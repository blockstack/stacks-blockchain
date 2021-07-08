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

use crate::codec::{write_next, Error as codec_error, StacksMessageCodec};
use crate::types::chainstate::StacksAddress;
use crate::types::proof::TrieHash;
use address::AddressHashMode;
use burnchains::Address;
use burnchains::Burnchain;
use burnchains::BurnchainBlockHeader;
use burnchains::BurnchainTransaction;
use burnchains::PublicKey;
use burnchains::Txid;
use chainstate::burn::db::sortdb::SortitionHandleTx;
use chainstate::burn::operations::Error as op_error;
use chainstate::burn::operations::{
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp, UserBurnSupportOp,
};
use chainstate::burn::ConsensusHash;
use chainstate::burn::Opcodes;
use chainstate::stacks::StacksPrivateKey;
use chainstate::stacks::StacksPublicKey;
use net::Error as net_error;
use util::db::DBConn;
use util::db::DBTx;
use util::hash::DoubleSha256;
use util::log;
use util::vrf::{VRFPrivateKey, VRFPublicKey, VRF};

use crate::types::chainstate::BlockHeaderHash;
use crate::types::chainstate::BurnchainHeaderHash;

struct ParsedData {
    pub consensus_hash: ConsensusHash,
    pub public_key: VRFPublicKey,
    pub memo: Vec<u8>,
}

impl LeaderKeyRegisterOp {
    #[cfg(test)]
    pub fn new(sender: &StacksAddress, public_key: &VRFPublicKey) -> LeaderKeyRegisterOp {
        LeaderKeyRegisterOp {
            public_key: public_key.clone(),
            memo: vec![],
            address: sender.clone(),

            // will be filled in
            consensus_hash: ConsensusHash([0u8; 20]),
            txid: Txid([0u8; 32]),
            vtxindex: 0,
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        }
    }

    #[cfg(test)]
    pub fn new_from_secrets(
        privks: &Vec<StacksPrivateKey>,
        num_sigs: u16,
        hash_mode: &AddressHashMode,
        prover_key: &VRFPrivateKey,
    ) -> Option<LeaderKeyRegisterOp> {
        let pubks = privks
            .iter()
            .map(|ref pk| StacksPublicKey::from_private(pk))
            .collect();
        let addr = match StacksAddress::from_public_keys(
            hash_mode.to_version_testnet(),
            hash_mode,
            num_sigs as usize,
            &pubks,
        ) {
            Some(a) => a,
            None => {
                return None;
            }
        };
        let prover_pubk = VRFPublicKey::from_private(prover_key);
        Some(LeaderKeyRegisterOp::new(&addr, &prover_pubk))
    }

    fn parse_data(data: &Vec<u8>) -> Option<ParsedData> {
        /*
            Wire format:

            0      2  3              23                       55                          80
            |------|--|---------------|-----------------------|---------------------------|
             magic  op consensus hash   proving public key               memo
                       (ignored)                                       (ignored)

             Note that `data` is missing the first 3 bytes -- the magic and op have been stripped
        */
        // memo can be empty, and magic + op are omitted
        if data.len() < 52 {
            // too short to have a consensus hash and proving public key
            warn!(
                "LEADER_KEY_REGISTER payload is malformed ({} bytes)",
                data.len()
            );
            return None;
        }

        let consensus_hash = ConsensusHash::from_bytes(&data[0..20])
            .expect("FATAL: invalid byte slice for consensus hash");
        let pubkey = match VRFPublicKey::from_bytes(&data[20..52].to_vec()) {
            Some(pubk) => pubk,
            None => {
                warn!("Invalid VRF public key");
                return None;
            }
        };

        let memo = &data[52..];

        Some(ParsedData {
            consensus_hash,
            public_key: pubkey,
            memo: memo.to_vec(),
        })
    }

    fn parse_from_tx(
        block_height: u64,
        block_hash: &BurnchainHeaderHash,
        tx: &BurnchainTransaction,
    ) -> Result<LeaderKeyRegisterOp, op_error> {
        // can't be too careful...
        let inputs = tx.get_signers();
        let outputs = tx.get_recipients();

        if inputs.len() == 0 {
            test_debug!(
                "Invalid tx: inputs: {}, outputs: {}",
                inputs.len(),
                outputs.len()
            );
            return Err(op_error::InvalidInput);
        }

        if outputs.len() < 1 {
            test_debug!(
                "Invalid tx: inputs: {}, outputs: {}",
                inputs.len(),
                outputs.len()
            );
            return Err(op_error::InvalidInput);
        }

        if tx.opcode() != Opcodes::LeaderKeyRegister as u8 {
            test_debug!("Invalid tx: invalid opcode {}", tx.opcode());
            return Err(op_error::InvalidInput);
        }

        let data = match LeaderKeyRegisterOp::parse_data(&tx.data()) {
            Some(data) => data,
            None => {
                test_debug!("Invalid tx data");
                return Err(op_error::ParseError);
            }
        };

        let address = outputs[0].address.clone();

        Ok(LeaderKeyRegisterOp {
            consensus_hash: data.consensus_hash,
            public_key: data.public_key,
            memo: data.memo,
            address: address,

            txid: tx.txid(),
            vtxindex: tx.vtxindex(),
            block_height: block_height,
            burn_header_hash: block_hash.clone(),
        })
    }
}

impl StacksMessageCodec for LeaderKeyRegisterOp {
    /*
        Wire format:

        0      2  3              23                       55                          80
        |------|--|---------------|-----------------------|---------------------------|
         magic  op consensus hash    proving public key               memo
                   (ignored)                                       (ignored)
    */
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        write_next(fd, &(Opcodes::LeaderKeyRegister as u8))?;
        write_next(fd, &self.consensus_hash)?;
        fd.write_all(&self.public_key.as_bytes()[..])
            .map_err(codec_error::WriteError)?;

        let memo = match self.memo.len() {
            l if l <= 25 => self.memo[0..].to_vec(),
            _ => self.memo[0..25].to_vec(),
        };
        fd.write_all(&memo).map_err(codec_error::WriteError)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(_fd: &mut R) -> Result<LeaderKeyRegisterOp, codec_error> {
        // Op deserialized through burchain indexer
        unimplemented!();
    }
}

impl LeaderKeyRegisterOp {
    pub fn from_tx(
        block_header: &BurnchainBlockHeader,
        tx: &BurnchainTransaction,
    ) -> Result<LeaderKeyRegisterOp, op_error> {
        LeaderKeyRegisterOp::parse_from_tx(block_header.block_height, &block_header.block_hash, tx)
    }

    pub fn check(
        &self,
        _burnchain: &Burnchain,
        tx: &mut SortitionHandleTx,
    ) -> Result<(), op_error> {
        /////////////////////////////////////////////////////////////////
        // Keys must be unique -- no one can register the same key twice
        /////////////////////////////////////////////////////////////////

        // key selected here must never have been submitted on this fork before
        let has_key_already = tx.has_VRF_public_key(&self.public_key)?;

        if has_key_already {
            warn!(
                "Invalid leader key registration: public key {} previously used",
                &self.public_key.to_hex()
            );
            return Err(op_error::LeaderKeyAlreadyRegistered);
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use burnchains::bitcoin::address::BitcoinAddress;
    use burnchains::bitcoin::blocks::BitcoinBlockParser;
    use burnchains::bitcoin::keys::BitcoinPublicKey;
    use burnchains::bitcoin::BitcoinNetworkType;
    use burnchains::*;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::operations::{
        BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp, UserBurnSupportOp,
    };
    use chainstate::burn::{BlockSnapshot, ConsensusHash, OpsHash, SortitionHash};
    use deps::bitcoin::blockdata::transaction::Transaction;
    use deps::bitcoin::network::serialize::deserialize;
    use util::get_epoch_time_secs;
    use util::hash::{hex_bytes, to_hex};
    use util::log;

    use crate::types::chainstate::SortitionId;

    use super::*;

    pub struct OpFixture {
        pub txstr: String,
        pub opstr: String,
        pub result: Option<LeaderKeyRegisterOp>,
    }

    struct CheckFixture {
        op: LeaderKeyRegisterOp,
        res: Result<(), op_error>,
    }

    fn make_tx(hex_str: &str) -> Result<Transaction, &'static str> {
        let tx_bin = hex_bytes(hex_str).map_err(|_e| "failed to decode hex string")?;
        let tx = deserialize(&tx_bin.to_vec()).map_err(|_e| "failed to deserialize")?;
        Ok(tx)
    }

    pub fn get_test_fixtures(
        vtxindex: u32,
        block_height: u64,
        burn_header_hash: BurnchainHeaderHash,
    ) -> Vec<OpFixture> {
        vec![
            OpFixture {
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a47304402203a176d95803e8d51e7884d38750322c4bfa55307a71291ef8db65191edd665f1022056f5d1720d1fde8d6a163c79f73f22f874ef9e186e98e5b60fa8ac64d298e77a012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0000000000200000000000000003e6a3c69645e2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a010203040539300000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "69645e2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a0102030405".to_string(),
                result: Some(LeaderKeyRegisterOp {
                    consensus_hash: ConsensusHash::from_bytes(&hex_bytes("2222222222222222222222222222222222222222").unwrap()).unwrap(),
                    public_key: VRFPublicKey::from_bytes(&hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap()).unwrap(),
                    memo: vec![01, 02, 03, 04, 05],
                    address: StacksAddress::from_bitcoin_address(&BitcoinAddress::from_scriptpubkey(BitcoinNetworkType::Testnet, &hex_bytes("76a9140be3e286a15ea85882761618e366586b5574100d88ac").unwrap()).unwrap()),

                    txid: Txid::from_bytes_be(&hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562").unwrap()).unwrap(),
                    vtxindex: vtxindex,
                    block_height: block_height,
                    burn_header_hash: burn_header_hash.clone(),
                })
            },
            OpFixture {
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a473044022037d0b9d4e98eab190522acf5fb8ea8e89b6a4704e0ac6c1883d6ffa629b3edd30220202757d710ec0fb940d1715e02588bb2150110161a9ee08a83b750d961431a8e012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000020000000000000000396a3769645e2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a39300000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "69645e2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a".to_string(),
                result: Some(LeaderKeyRegisterOp {
                    consensus_hash: ConsensusHash::from_bytes(&hex_bytes("2222222222222222222222222222222222222222").unwrap()).unwrap(),
                    public_key: VRFPublicKey::from_bytes(&hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap()).unwrap(),
                    memo: vec![],
                    address: StacksAddress::from_bitcoin_address(&BitcoinAddress::from_scriptpubkey(BitcoinNetworkType::Testnet, &hex_bytes("76a9140be3e286a15ea85882761618e366586b5574100d88ac").unwrap()).unwrap()),

                    txid: Txid::from_bytes_be(&hex_bytes("2fbf8d5be32dce49790d203ba59acbb0929d5243413174ff5d26a5c6f23dea65").unwrap()).unwrap(),
                    vtxindex: vtxindex,
                    block_height: block_height,
                    burn_header_hash: burn_header_hash,
                })
            },
            OpFixture {
                // invalid VRF public key 
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006b483045022100ddbbaf029174a9bd1588fc0b34094e9f48fec9c89704eb12a3ee70dd5ca4142e02202eab7cbf985da23e890766331f7e0009268d1db75da8b583a953528e6a099499012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0000000000200000000000000003e6a3c69645e2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7b010203040539300000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "".to_string(),
                result: None,
            },
            OpFixture {
                // too short
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006b483045022100b2680431ab771826f42b93f5238e518c6483af7026c25ddd6e970f26fec80473022050ab510ede8d7b50cea1a286d1e05fa2b2d62ffbb9983e4cade9899474d0f8b9012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000020000000000000000386a3669645e22222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a39300000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "".to_string(),
                result: None,
            },
            OpFixture {
                // not enough outputs
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006a473044022070c8ce3786cee46d283b8a02a9c6ba87ef693960a0200b4a85e1b4808ea7b23a02201c6926162fe8cf4d3bbc3fcea80baa8307543af69b5dbbad72aa659a3a87f08e012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0000000000100000000000000003e6a3c69645e2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a010203040500000000".to_string(),
                opstr: "".to_string(),
                result: None,
            },
            OpFixture {
                // wrong opcode
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006b483045022100a72df03441bdd08b8fd042f417e37e7ba7dc6212078835840f4cbd64f690533a0220385309a6096044828ec7889107a73da23b009157a752251ed68f8084834d4d44012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0000000000200000000000000003e6a3c69645f2222222222222222222222222222222222222222a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a010203040539300000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "".to_string(),
                result: None,
            }
        ]
    }

    #[test]
    fn test_parse() {
        let vtxindex = 1;
        let block_height = 694;
        let burn_header_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let tx_fixtures = get_test_fixtures(vtxindex, block_height, burn_header_hash);

        let parser = BitcoinBlockParser::new(BitcoinNetworkType::Testnet, BLOCKSTACK_MAGIC_MAINNET);

        for tx_fixture in tx_fixtures {
            let tx = make_tx(&tx_fixture.txstr).unwrap();
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
            let burnchain_tx =
                BurnchainTransaction::Bitcoin(parser.parse_tx(&tx, vtxindex as usize).unwrap());
            let op = LeaderKeyRegisterOp::from_tx(&header, &burnchain_tx);

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
                    test_debug!("Parsed a tx when we should not have: {}", tx_fixture.txstr);
                    assert!(false);
                }
                (Err(_e), Some(_result)) => {
                    test_debug!(
                        "Did not parse a tx when we should have: {}",
                        tx_fixture.txstr
                    );
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
            "0000000000000000000000000000000000000000000000000000000000000006",
        )
        .unwrap();
        let block_126_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000007",
        )
        .unwrap();
        let block_127_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000008",
        )
        .unwrap();
        let block_128_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000009",
        )
        .unwrap();
        let block_129_hash = BurnchainHeaderHash::from_hex(
            "000000000000000000000000000000000000000000000000000000000000000a",
        )
        .unwrap();
        let block_130_hash = BurnchainHeaderHash::from_hex(
            "000000000000000000000000000000000000000000000000000000000000000b",
        )
        .unwrap();
        let block_131_hash = BurnchainHeaderHash::from_hex(
            "000000000000000000000000000000000000000000000000000000000000000c",
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
            first_block_hash: first_burn_hash.clone(),
            first_block_timestamp: 0,
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
        let tip_root_index = {
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

                let next_tip_root = tx
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
                snapshot_row.index_root = next_tip_root;

                tx.commit().unwrap();
                prev_snapshot = snapshot_row;
            }
            prev_snapshot.index_root.clone()
        };

        let check_fixtures = vec![
            CheckFixture {
                // reject -- key already registered
                op: LeaderKeyRegisterOp {
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
                    memo: vec![01, 02, 03, 04, 05],
                    address: StacksAddress::from_bitcoin_address(
                        &BitcoinAddress::from_scriptpubkey(
                            BitcoinNetworkType::Testnet,
                            &hex_bytes("76a9140be3e286a15ea85882761618e366586b5574100d88ac")
                                .unwrap(),
                        )
                        .unwrap(),
                    ),

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 455,
                    block_height: 123,
                    burn_header_hash: block_123_hash.clone(),
                },
                res: Err(op_error::LeaderKeyAlreadyRegistered),
            },
            CheckFixture {
                // accept
                op: LeaderKeyRegisterOp {
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
                    memo: vec![01, 02, 03, 04, 05],
                    address: StacksAddress::from_bitcoin_address(
                        &BitcoinAddress::from_scriptpubkey(
                            BitcoinNetworkType::Testnet,
                            &hex_bytes("76a9140be3e286a15ea85882761618e366586b5574100d88ac")
                                .unwrap(),
                        )
                        .unwrap(),
                    ),

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 456,
                    block_height: 123,
                    burn_header_hash: block_123_hash.clone(),
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
