// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use std::io::{Read, Write};
use std::marker::PhantomData;

use crate::codec::{write_next, Error as codec_error, StacksMessageCodec};
use crate::types::proof::TrieHash;
use burnchains::Address;
use burnchains::Burnchain;
use burnchains::BurnchainBlockHeader;
use burnchains::BurnchainTransaction;
use burnchains::PublicKey;
use burnchains::Txid;
use chainstate::burn::db::sortdb::SortitionHandleTx;
use chainstate::burn::operations::Error as op_error;
use chainstate::burn::operations::{
    parse_u16_from_be, parse_u32_from_be, BlockstackOperationType, LeaderBlockCommitOp,
    LeaderKeyRegisterOp, UserBurnSupportOp,
};
use chainstate::burn::ConsensusHash;
use chainstate::burn::Opcodes;
use net::Error as net_error;
use util::db::DBConn;
use util::db::DBTx;
use util::hash::Hash160;
use util::log;
use util::vrf::{VRFPublicKey, VRF};

use crate::types::chainstate::BlockHeaderHash;
use crate::types::chainstate::BurnchainHeaderHash;

// return type for parse_data (below)
struct ParsedData {
    pub consensus_hash: ConsensusHash,
    pub public_key: VRFPublicKey,
    pub key_block_ptr: u32,
    pub key_vtxindex: u16,
    pub block_header_hash_160: Hash160,
}

impl UserBurnSupportOp {
    fn parse_data(data: &Vec<u8>) -> Option<ParsedData> {
        /*
            Wire format:

            0      2  3              22                       54                 74       78        80
            |------|--|---------------|-----------------------|------------------|--------|---------|
             magic  op consensus hash    proving public key       block hash 160   key blk  key
                       (truncated by 1)                                                     vtxindex


             Note that `data` is missing the first 3 bytes -- the magic and op have been stripped
        */
        if data.len() < 77 {
            warn!(
                "USER_BURN_SUPPORT payload is malformed ({} bytes)",
                data.len()
            );
            return None;
        }

        let mut consensus_hash_trunc = data[0..19].to_vec();
        consensus_hash_trunc.push(0);

        let consensus_hash = ConsensusHash::from_vec(&consensus_hash_trunc)
            .expect("FATAL: invalid data slice for consensus hash");
        let pubkey = match VRFPublicKey::from_bytes(&data[19..51].to_vec()) {
            Some(pubk) => pubk,
            None => {
                warn!("Invalid VRF public key");
                return None;
            }
        };

        let block_header_hash_160 = Hash160::from_vec(&data[51..71].to_vec())
            .expect("FATAL: invalid data slice for block hash160");
        let key_block_ptr = parse_u32_from_be(&data[71..75]).unwrap();
        let key_vtxindex = parse_u16_from_be(&data[75..77]).unwrap();

        Some(ParsedData {
            consensus_hash,
            public_key: pubkey,
            block_header_hash_160,
            key_block_ptr,
            key_vtxindex,
        })
    }

    fn parse_from_tx(
        block_height: u64,
        block_hash: &BurnchainHeaderHash,
        tx: &BurnchainTransaction,
    ) -> Result<UserBurnSupportOp, op_error> {
        // can't be too careful...
        let inputs = tx.get_signers();
        let outputs = tx.get_recipients();

        if inputs.len() == 0 || outputs.len() == 0 {
            test_debug!(
                "Invalid tx: inputs: {}, outputs: {}",
                inputs.len(),
                outputs.len()
            );
            return Err(op_error::InvalidInput);
        }

        if outputs.len() < 2 {
            test_debug!(
                "Invalid tx: inputs: {}, outputs: {}",
                inputs.len(),
                outputs.len()
            );
            return Err(op_error::InvalidInput);
        }

        if tx.opcode() != Opcodes::UserBurnSupport as u8 {
            test_debug!("Invalid tx: invalid opcode {}", tx.opcode());
            return Err(op_error::InvalidInput);
        }

        // outputs[0] should be the burn output
        if !outputs[0].address.is_burn() {
            // wrong burn output
            test_debug!("Invalid tx: burn output missing (got {:?})", outputs[0]);
            return Err(op_error::ParseError);
        }

        let burn_fee = outputs[0].amount;

        let data = match UserBurnSupportOp::parse_data(&tx.data()) {
            None => {
                test_debug!("Invalid tx data");
                return Err(op_error::ParseError);
            }
            Some(d) => d,
        };

        // basic sanity checks
        if data.key_block_ptr == 0 {
            warn!("Invalid tx: key block pointer must be positive");
            return Err(op_error::ParseError);
        }

        if data.key_block_ptr as u64 > block_height {
            warn!(
                "Invalid tx: key block back-pointer {} exceeds block height {}",
                data.key_block_ptr, block_height
            );
            return Err(op_error::ParseError);
        }

        Ok(UserBurnSupportOp {
            address: outputs[1].address.clone(),
            consensus_hash: data.consensus_hash,
            public_key: data.public_key,
            block_header_hash_160: data.block_header_hash_160,
            key_block_ptr: data.key_block_ptr,
            key_vtxindex: data.key_vtxindex,
            burn_fee: burn_fee,

            txid: tx.txid(),
            vtxindex: tx.vtxindex(),
            block_height: block_height,
            burn_header_hash: block_hash.clone(),
        })
    }
}

impl StacksMessageCodec for UserBurnSupportOp {
    /*
        Wire format:

        0      2  3              22                       54                 74       78        80
        |------|--|---------------|-----------------------|------------------|--------|---------|
         magic  op consensus hash   proving public key       block hash 160   key blk  key
                (truncated by 1)                                                        vtxindex
    */
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        write_next(fd, &(Opcodes::UserBurnSupport as u8))?;
        let truncated_consensus = self.consensus_hash.to_bytes();
        fd.write_all(&truncated_consensus[0..19])
            .map_err(codec_error::WriteError)?;
        fd.write_all(&self.public_key.as_bytes()[..])
            .map_err(codec_error::WriteError)?;
        write_next(fd, &self.block_header_hash_160)?;
        write_next(fd, &self.key_block_ptr)?;
        write_next(fd, &self.key_vtxindex)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(_fd: &mut R) -> Result<UserBurnSupportOp, codec_error> {
        // Op deserialized through burchain indexer
        unimplemented!();
    }
}

impl UserBurnSupportOp {
    pub fn from_tx(
        _block_header: &BurnchainBlockHeader,
        _tx: &BurnchainTransaction,
    ) -> Result<UserBurnSupportOp, op_error> {
        Err(op_error::UserBurnSupportNotSupported)
    }

    pub fn check(&self, burnchain: &Burnchain, tx: &mut SortitionHandleTx) -> Result<(), op_error> {
        let leader_key_block_height = self.key_block_ptr as u64;

        /////////////////////////////////////////////////////////////////
        // Consensus hash must be recent and valid
        /////////////////////////////////////////////////////////////////

        // NOTE: we only care about the first 19 bytes
        let is_fresh = tx.is_fresh_consensus_hash_check_19b(
            burnchain.consensus_hash_lifetime.into(),
            &self.consensus_hash,
        )?;

        if !is_fresh {
            warn!(
                "Invalid user burn: invalid consensus hash {}",
                &self.consensus_hash
            );
            return Err(op_error::UserBurnSupportBadConsensusHash);
        }

        /////////////////////////////////////////////////////////////////////////////////////
        // There must exist a previously-accepted LeaderKeyRegisterOp that matches this
        // user support burn's VRF public key.
        /////////////////////////////////////////////////////////////////////////////////////
        if self.key_block_ptr == 0 {
            warn!("Invalid tx: key block back-pointer must be positive");
            return Err(op_error::ParseError);
        }

        if self.key_block_ptr as u64 > self.block_height {
            warn!(
                "Invalid tx: key block back-pointer {} exceeds block height {}",
                self.key_block_ptr, self.block_height
            );
            return Err(op_error::ParseError);
        }

        let chain_tip = tx.context.chain_tip.clone();
        let register_key_opt = tx.get_leader_key_at(
            leader_key_block_height,
            self.key_vtxindex.into(),
            &chain_tip,
        )?;

        if register_key_opt.is_none() {
            warn!(
                "Invalid user burn: no such leader VRF key {}",
                &self.public_key.to_hex()
            );
            return Err(op_error::UserBurnSupportNoLeaderKey);
        }

        /////////////////////////////////////////////////////////////////////////////////////
        // The block hash can't be checked here -- the corresponding LeaderBlockCommitOp may
        // not have been checked yet, so we don't know yet if it exists.  The sortition
        // algorithm will carry out this check, and only consider user burns if they match
        // a block commit and the commit's corresponding leader key.
        /////////////////////////////////////////////////////////////////////////////////////

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::types::chainstate::StacksAddress;
    use burnchains::bitcoin::address::BitcoinAddress;
    use burnchains::bitcoin::blocks::BitcoinBlockParser;
    use burnchains::bitcoin::keys::BitcoinPublicKey;
    use burnchains::bitcoin::BitcoinNetworkType;
    use burnchains::*;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::operations::{
        BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp, UserBurnSupportOp,
    };
    use chainstate::burn::*;
    use deps::bitcoin::blockdata::transaction::Transaction;
    use deps::bitcoin::network::serialize::deserialize;
    use util::get_epoch_time_secs;
    use util::hash::{hex_bytes, to_hex, Hash160};
    use util::log;

    use crate::types::chainstate::SortitionId;

    use super::*;

    struct OpFixture {
        txstr: String,
        opstr: String,
        result: Option<UserBurnSupportOp>,
    }

    struct CheckFixture {
        op: UserBurnSupportOp,
        res: Result<(), op_error>,
    }

    fn make_tx(hex_str: &str) -> Result<Transaction, &'static str> {
        let tx_bin = hex_bytes(hex_str).map_err(|_e| "failed to decode hex string")?;
        let tx = deserialize(&tx_bin.to_vec()).map_err(|_e| "failed to deserialize")?;
        Ok(tx)
    }

    #[test]
    fn test_parse() {
        let vtxindex = 1;
        let _block_height = 694;
        let burn_header_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let tx_fixtures = vec![
            OpFixture {
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a47304402204c51707ac34b6dcbfc518ba40c5fc4ef737bf69cc21a9f8a8e6f621f511f78e002200caca0f102d5df509c045c4fe229d957aa7ef833dc8103dc2fe4db15a22bab9e012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000030000000000000000536a4c5069645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a3333333333333333333333333333333333333333010203040539300000000000001976a914000000000000000000000000000000000000000088aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "69645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a33333333333333333333333333333333333333330102030405".to_string(),
                result: Some(UserBurnSupportOp {
                    address: StacksAddress::from_bitcoin_address(&BitcoinAddress::from_string(&"mgbpit8FvkVJ9kuXY8QSM5P7eibnhcEMBk".to_string()).unwrap()),
                    consensus_hash: ConsensusHash::from_bytes(&hex_bytes("2222222222222222222222222222222222222200").unwrap()).unwrap(),
                    public_key: VRFPublicKey::from_bytes(&hex_bytes("22a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c").unwrap()).unwrap(),
                    block_header_hash_160: Hash160::from_bytes(&hex_bytes("7a33333333333333333333333333333333333333").unwrap()).unwrap(),
                    key_block_ptr: 0x33010203,
                    key_vtxindex: 0x0405,
                    burn_fee: 12345,

                    txid: Txid::from_bytes_be(&hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c").unwrap()).unwrap(),
                    vtxindex: vtxindex,
                    block_height: 0x33010203 + 1,
                    burn_header_hash: burn_header_hash,
                })
            },
            OpFixture {
                // invalid -- no burn output
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a473044022073490a3958b9e6128d3b7a4a8c77203c56862b2da382e96551f7efae7029b0e1022046672d1e61bdfd3dca9cc199bffd0bfb9323e432f8431bb6749da3c5bd06e9ca012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000020000000000000000536a4c5069645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a33333333333333333333333333333333333333330102030405a05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "69645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a33333333333333333333333333333333333333330102030405".to_string(),
                result: None,
            },
            OpFixture {
                // invalid -- bad public key
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a47304402202bf944fa4d1dbbdd4f53e915c85f07c8a5afbf917f7cc9169e9c7d3bbadff05a022064b33a1020dd9cdd0ac6de213ee1bd8f364c9c876e716ad289f324c2a4bbe48a012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000030000000000000000536a4c5069645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7b3333333333333333333333333333333333333333010203040539300000000000001976a914000000000000000000000000000000000000000088aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "69645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a33333333333333333333333333333333333333330102030405".to_string(),
                result: None,
            },
            OpFixture {
                // invalid -- too short 
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a473044022038534377d738ba91df50a4bc885bcd6328520438d42cc29636cc299a24dcb4c202202953e87b6c176697d01d66a742a27fd48b8d2167fb9db184d59a3be23a59992e012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0000000000300000000000000004c6a4a69645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a3333333333333333333333333333333333333339300000000000001976a914000000000000000000000000000000000000000088aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "69645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a33333333333333333333333333333333333333330102030405".to_string(),
                result: None,
            },
            OpFixture {
                // invalid -- wrong opcode
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a47304402200e6dbb4ccefc44582135091678a49228716431583dab3d789b1211d5737d02e402205b523ad156cad4ae6bb29f046b144c8c82b7c85698616ee8f5d59ea40d594dd4012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000030000000000000000536a4c5069645e2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a3333333333333333333333333333333333333333010203040539300000000000001976a914000000000000000000000000000000000000000088aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "69645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a33333333333333333333333333333333333333330102030405".to_string(),
                result: None,
            }
        ];

        let parser = BitcoinBlockParser::new(BitcoinNetworkType::Testnet, BLOCKSTACK_MAGIC_MAINNET);

        for tx_fixture in tx_fixtures {
            let tx = make_tx(&tx_fixture.txstr).unwrap();
            let burnchain_tx =
                BurnchainTransaction::Bitcoin(parser.parse_tx(&tx, vtxindex as usize).unwrap());

            let header = match tx_fixture.result {
                Some(ref op) => BurnchainBlockHeader {
                    block_height: op.block_height,
                    block_hash: op.burn_header_hash.clone(),
                    parent_block_hash: op.burn_header_hash.clone(),
                    num_txs: 1,
                    timestamp: get_epoch_time_secs(),
                },
                None => BurnchainBlockHeader {
                    block_height: 0,
                    block_hash: BurnchainHeaderHash::zero(),
                    parent_block_hash: BurnchainHeaderHash::zero(),
                    num_txs: 0,
                    timestamp: get_epoch_time_secs(),
                },
            };

            let op = UserBurnSupportOp::parse_from_tx(
                header.block_height,
                &header.block_hash,
                &burnchain_tx,
            );

            match (op, tx_fixture.result) {
                (Ok(parsed_tx), Some(result)) => {
                    let opstr = {
                        let mut buffer = vec![];
                        let mut magic_bytes = BLOCKSTACK_MAGIC_MAINNET.as_bytes().to_vec();
                        buffer.append(&mut magic_bytes);
                        parsed_tx
                            .consensus_serialize(&mut buffer)
                            .expect("FATAL: invalid operation");
                        to_hex(&buffer)
                    };

                    assert_eq!(tx_fixture.opstr, opstr);
                    assert_eq!(parsed_tx, result);
                }
                (Err(_e), None) => {}
                (Ok(_parsed_tx), None) => {
                    test_debug!("Parsed a tx when we should not have");
                    assert!(false);
                }
                (Err(_e), Some(_result)) => {
                    test_debug!("Did not parse a tx when we should have: {:?}", _result);
                    assert!(false);
                }
            };
        }
    }

    #[test]
    fn test_check() {
        let first_block_height = 121;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000123",
        )
        .unwrap();

        let block_122_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000002",
        )
        .unwrap();
        let block_123_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000003",
        )
        .unwrap();
        let block_124_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000004",
        )
        .unwrap();
        let block_125_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000005",
        )
        .unwrap();
        let block_126_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000006",
        )
        .unwrap();
        let block_127_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000007",
        )
        .unwrap();
        let block_128_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000008",
        )
        .unwrap();
        let block_129_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000009",
        )
        .unwrap();
        let block_130_hash = BurnchainHeaderHash::from_hex(
            "000000000000000000000000000000000000000000000000000000000000000a",
        )
        .unwrap();
        let block_131_hash = BurnchainHeaderHash::from_hex(
            "000000000000000000000000000000000000000000000000000000000000000b",
        )
        .unwrap();

        let block_header_hashes = [
            block_122_hash.clone(),
            block_123_hash.clone(),
            block_124_hash.clone(),
            block_125_hash.clone(),
            block_126_hash.clone(),
            block_127_hash.clone(),
            block_128_hash.clone(),
            block_129_hash.clone(),
            block_130_hash.clone(),
            block_131_hash.clone(),
        ];
        let burnchain = Burnchain {
            pox_constants: PoxConstants::test_default(),
            peer_version: 0x012345678,
            network_id: 0x9abcdef0,
            chain_name: "bitcoin".to_string(),
            network_name: "testnet".to_string(),
            working_dir: "/nope".to_string(),
            consensus_hash_lifetime: 24,
            stable_confirmations: 7,
            first_block_height,
            initial_reward_start_block: first_block_height,
            first_block_timestamp: 0,
            first_block_hash: first_burn_hash.clone(),
        };

        let mut db = SortitionDB::connect_test(first_block_height, &first_burn_hash).unwrap();

        let leader_key_1 = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![01, 02, 03, 04, 05],
            address: StacksAddress::from_bitcoin_address(
                &BitcoinAddress::from_scriptpubkey(
                    BitcoinNetworkType::Testnet,
                    &hex_bytes("76a9140be3e286a15ea85882761618e366586b5574100d88ac").unwrap(),
                )
                .unwrap(),
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 456,
            block_height: 123,
            burn_header_hash: block_123_hash.clone(),
        };

        let block_ops = vec![
            // 122
            vec![],
            // 123
            vec![BlockstackOperationType::LeaderKeyRegister(
                leader_key_1.clone(),
            )],
            // 124
            vec![],
            // 125
            vec![],
            // 126
            vec![],
            // 127
            vec![],
            // 128
            vec![],
            // 129
            vec![],
            // 130
            vec![],
            // 131
            vec![],
        ];

        // populate consensus hashes
        let tip_index_root = {
            let mut prev_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            for i in 0..10 {
                let mut snapshot_row = BlockSnapshot {
                    accumulated_coinbase_ustx: 0,
                    pox_valid: true,
                    block_height: i + 1 + first_block_height,
                    burn_header_timestamp: get_epoch_time_secs(),
                    burn_header_hash: block_header_hashes[i as usize].clone(),
                    sortition_id: SortitionId(block_header_hashes[i as usize].0.clone()),
                    parent_sortition_id: prev_snapshot.sortition_id.clone(),
                    parent_burn_header_hash: prev_snapshot.burn_header_hash.clone(),
                    consensus_hash: ConsensusHash::from_bytes(&[
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        (i + 1) as u8,
                    ])
                    .unwrap(),
                    ops_hash: OpsHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i as u8,
                    ])
                    .unwrap(),
                    total_burn: i,
                    sortition: true,
                    sortition_hash: SortitionHash::initial(),
                    winning_block_txid: Txid::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    winning_stacks_block_hash: BlockHeaderHash::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    index_root: TrieHash::from_empty_data(),
                    num_sortitions: i + 1,
                    stacks_block_accepted: false,
                    stacks_block_height: 0,
                    arrival_index: 0,
                    canonical_stacks_tip_height: 0,
                    canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                    canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                    ..BlockSnapshot::initial(0, &first_burn_hash, 0)
                };
                let mut tx =
                    SortitionHandleTx::begin(&mut db, &prev_snapshot.sortition_id).unwrap();

                let tip_index_root = tx
                    .append_chain_tip_snapshot(
                        &prev_snapshot,
                        &snapshot_row,
                        &block_ops[i as usize],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                snapshot_row.index_root = tip_index_root;

                tx.commit().unwrap();
                prev_snapshot = snapshot_row;
            }

            prev_snapshot.index_root.clone()
        };

        let check_fixtures = vec![
            CheckFixture {
                // reject -- bad consensus hash
                op: UserBurnSupportOp {
                    address: StacksAddress::new(1, Hash160([1u8; 20])),
                    consensus_hash: ConsensusHash::from_bytes(
                        &hex_bytes("1000000000000000000000000000000000000000").unwrap(),
                    )
                    .unwrap(),
                    public_key: VRFPublicKey::from_bytes(
                        &hex_bytes(
                            "a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    block_header_hash_160: Hash160::from_bytes(
                        &hex_bytes("7150f635054b87df566a970b21e07030d6444bf2").unwrap(),
                    )
                    .unwrap(), // 22222....2222
                    key_block_ptr: 123,
                    key_vtxindex: 456,
                    burn_fee: 10000,

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716b",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 13,
                    block_height: 124,
                    burn_header_hash: block_124_hash.clone(),
                },
                res: Err(op_error::UserBurnSupportBadConsensusHash),
            },
            CheckFixture {
                // reject -- no leader key
                op: UserBurnSupportOp {
                    address: StacksAddress::new(1, Hash160([1u8; 20])),
                    consensus_hash: ConsensusHash::from_bytes(
                        &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
                    )
                    .unwrap(),
                    public_key: VRFPublicKey::from_bytes(
                        &hex_bytes(
                            "bb519494643f79f1dea0350e6fb9a1da88dfdb6137117fc2523824a8aa44fe1c",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    block_header_hash_160: Hash160::from_bytes(
                        &hex_bytes("7150f635054b87df566a970b21e07030d6444bf2").unwrap(),
                    )
                    .unwrap(), // 22222....2222
                    key_block_ptr: 123,
                    key_vtxindex: 457,
                    burn_fee: 10000,

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716b",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 13,
                    block_height: 124,
                    burn_header_hash: block_124_hash.clone(),
                },
                res: Err(op_error::UserBurnSupportNoLeaderKey),
            },
            CheckFixture {
                // accept
                op: UserBurnSupportOp {
                    address: StacksAddress::new(1, Hash160([1u8; 20])),
                    consensus_hash: ConsensusHash::from_bytes(
                        &hex_bytes("0000000000000000000000000000000000000000").unwrap(),
                    )
                    .unwrap(),
                    public_key: VRFPublicKey::from_bytes(
                        &hex_bytes(
                            "a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    block_header_hash_160: Hash160::from_bytes(
                        &hex_bytes("7150f635054b87df566a970b21e07030d6444bf2").unwrap(),
                    )
                    .unwrap(), // 22222....2222
                    key_block_ptr: 123,
                    key_vtxindex: 456,
                    burn_fee: 10000,

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716b",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 13,
                    block_height: 124,
                    burn_header_hash: block_124_hash.clone(),
                },
                res: Ok(()),
            },
        ];

        for fixture in check_fixtures {
            let header = BurnchainBlockHeader {
                block_height: fixture.op.block_height,
                block_hash: fixture.op.burn_header_hash.clone(),
                parent_block_hash: fixture.op.burn_header_hash.clone(),
                num_txs: 1,
                timestamp: get_epoch_time_secs(),
            };
            let mut ic = SortitionHandleTx::begin(
                &mut db,
                &SortitionId::stubbed(&fixture.op.burn_header_hash),
            )
            .unwrap();
            assert_eq!(
                format!("{:?}", &fixture.res),
                format!("{:?}", &fixture.op.check(&burnchain, &mut ic))
            );
        }
    }
}
