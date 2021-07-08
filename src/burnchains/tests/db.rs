// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2021 Stacks Open Internet Foundation
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

use std::cmp;
use std::convert::TryInto;

use address::*;
use burnchains::bitcoin::address::*;
use burnchains::bitcoin::blocks::*;
use burnchains::bitcoin::*;
use burnchains::db::*;
use burnchains::PoxConstants;
use burnchains::BLOCKSTACK_MAGIC_MAINNET;
use burnchains::*;
use burnchains::{BurnchainBlock, BurnchainBlockHeader, Txid};
use chainstate::burn::operations::{
    leader_block_commit::BURN_BLOCK_MINED_AT_MODULUS, BlockstackOperationType, LeaderBlockCommitOp,
};
use chainstate::burn::*;
use chainstate::coordinator::tests::*;
use chainstate::stacks::*;
use deps::bitcoin::blockdata::transaction::Transaction as BtcTx;
use deps::bitcoin::network::serialize::deserialize;
use util::db::Error as DBError;
use util::db::*;
use util::hash::*;

use crate::types::proof::ClarityMarfTrieId;

use crate::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, PoxId, SortitionId, StacksAddress, VRFSeed,
};

fn make_tx(hex_str: &str) -> BtcTx {
    let tx_bin = hex_bytes(hex_str).unwrap();
    deserialize(&tx_bin.to_vec()).unwrap()
}

impl BurnchainHeaderReader for Vec<BurnchainBlockHeader> {
    fn read_burnchain_headers(
        &self,
        start_height: u64,
        end_height: u64,
    ) -> Result<Vec<BurnchainBlockHeader>, DBError> {
        if start_height >= self.len() as u64 {
            return Ok(vec![]);
        }
        let end = cmp::min(end_height, self.len() as u64) as usize;
        Ok(self[(start_height as usize)..end].to_vec())
    }

    fn get_burnchain_headers_height(&self) -> Result<u64, DBError> {
        Ok(self.len() as u64)
    }
}

#[test]
fn test_store_and_fetch() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 321;
    let first_height = 1;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::test_default();
    burnchain.pox_constants.sunset_start = 999;
    burnchain.pox_constants.sunset_end = 1000;

    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();
    assert_eq!(&first_block_header.block_hash, &first_bhh);
    assert_eq!(&first_block_header.block_height, &first_height);
    assert_eq!(first_block_header.timestamp, first_timestamp as u64);
    assert_eq!(
        &first_block_header.parent_block_hash,
        &BurnchainHeaderHash::sentinel()
    );

    let headers = vec![first_block_header.clone()];
    let canon_hash = BurnchainHeaderHash([1; 32]);

    let canonical_block = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        500,
        &canon_hash,
        &first_bhh,
        &vec![],
        485,
    ));
    let ops = burnchain_db
        .store_new_burnchain_block(&burnchain, &headers, &canonical_block)
        .unwrap();
    assert_eq!(ops.len(), 0);

    let vtxindex = 1;
    let noncanon_block_height = 400;
    let non_canon_hash = BurnchainHeaderHash([2; 32]);

    let fixtures = operations::leader_key_register::tests::get_test_fixtures(
        vtxindex,
        noncanon_block_height,
        non_canon_hash,
    );

    let parser = BitcoinBlockParser::new(BitcoinNetworkType::Testnet, BLOCKSTACK_MAGIC_MAINNET);
    let mut broadcast_ops = vec![];
    let mut expected_ops = vec![];

    for (ix, tx_fixture) in fixtures.iter().enumerate() {
        let tx = make_tx(&tx_fixture.txstr);
        let burnchain_tx = parser.parse_tx(&tx, ix + 1).unwrap();
        if let Some(res) = &tx_fixture.result {
            let mut res = res.clone();
            res.vtxindex = (ix + 1).try_into().unwrap();
            expected_ops.push(res.clone());
        }
        broadcast_ops.push(burnchain_tx);
    }

    let non_canonical_block = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        400,
        &non_canon_hash,
        &first_bhh,
        &broadcast_ops,
        350,
    ));

    let ops = burnchain_db
        .store_new_burnchain_block(&burnchain, &headers, &non_canonical_block)
        .unwrap();
    assert_eq!(ops.len(), expected_ops.len());
    for op in ops.iter() {
        let expected_op = expected_ops
            .iter()
            .find(|candidate| candidate.txid == op.txid())
            .expect("FAILED to find parsed op in expected ops");
        if let BlockstackOperationType::LeaderKeyRegister(op) = op {
            assert_eq!(op, expected_op);
        } else {
            panic!("EXPECTED to parse a LeaderKeyRegister");
        }
    }

    let BurnchainBlockData { header, ops } =
        BurnchainDB::get_burnchain_block(&burnchain_db.conn(), &non_canon_hash).unwrap();
    assert_eq!(ops.len(), expected_ops.len());
    for op in ops.iter() {
        let expected_op = expected_ops
            .iter()
            .find(|candidate| candidate.txid == op.txid())
            .expect("FAILED to find parsed op in expected ops");
        if let BlockstackOperationType::LeaderKeyRegister(op) = op {
            assert_eq!(op, expected_op);
        } else {
            panic!("EXPECTED to parse a LeaderKeyRegister");
        }
    }
    assert_eq!(&header, &non_canonical_block.header());

    let looked_up_canon = burnchain_db.get_canonical_chain_tip().unwrap();
    assert_eq!(&looked_up_canon, &canonical_block.header());

    let BurnchainBlockData { header, ops } =
        BurnchainDB::get_burnchain_block(&burnchain_db.conn(), &canon_hash).unwrap();
    assert_eq!(ops.len(), 0);
    assert_eq!(&header, &looked_up_canon);
}

#[test]
fn test_classify_stack_stx() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 321;
    let first_height = 1;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::test_default();
    burnchain.pox_constants.sunset_start = 999;
    burnchain.pox_constants.sunset_end = 1000;

    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();
    assert_eq!(&first_block_header.block_hash, &first_bhh);
    assert_eq!(&first_block_header.block_height, &first_height);
    assert_eq!(first_block_header.timestamp, first_timestamp as u64);
    assert_eq!(
        &first_block_header.parent_block_hash,
        &BurnchainHeaderHash::sentinel()
    );

    let canon_hash = BurnchainHeaderHash([1; 32]);
    let mut headers = vec![first_block_header.clone()];

    let canonical_block = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        500,
        &canon_hash,
        &first_bhh,
        &vec![],
        485,
    ));
    let ops = burnchain_db
        .store_new_burnchain_block(&burnchain, &headers, &canonical_block)
        .unwrap();
    assert_eq!(ops.len(), 0);

    // let's mine a block with a pre-stack-stx tx, and a stack-stx tx,
    //    the stack-stx tx should _fail_ to verify, because there's no
    //    corresponding pre-stack-stx.

    let parser = BitcoinBlockParser::new(BitcoinNetworkType::Testnet, BLOCKSTACK_MAGIC_MAINNET);

    let pre_stack_stx_0_txid = Txid([5; 32]);
    let pre_stack_stx_0 = BitcoinTransaction {
        txid: pre_stack_stx_0_txid.clone(),
        vtxindex: 0,
        opcode: Opcodes::PreStx as u8,
        data: vec![0; 80],
        data_amt: 0,
        inputs: vec![BitcoinTxInput {
            keys: vec![],
            num_required: 0,
            in_type: BitcoinInputType::Standard,
            tx_ref: (Txid([0; 32]), 1),
        }],
        outputs: vec![BitcoinTxOutput {
            units: 10,
            address: BitcoinAddress {
                addrtype: BitcoinAddressType::PublicKeyHash,
                network_id: BitcoinNetworkType::Mainnet,
                bytes: Hash160([1; 20]),
            },
        }],
    };

    // this one will not have a corresponding pre_stack_stx tx.
    let stack_stx_0 = BitcoinTransaction {
        txid: Txid([4; 32]),
        vtxindex: 1,
        opcode: Opcodes::StackStx as u8,
        data: vec![1; 80],
        data_amt: 0,
        inputs: vec![BitcoinTxInput {
            keys: vec![],
            num_required: 0,
            in_type: BitcoinInputType::Standard,
            tx_ref: (Txid([0; 32]), 1),
        }],
        outputs: vec![BitcoinTxOutput {
            units: 10,
            address: BitcoinAddress {
                addrtype: BitcoinAddressType::PublicKeyHash,
                network_id: BitcoinNetworkType::Mainnet,
                bytes: Hash160([1; 20]),
            },
        }],
    };

    // this one will have a corresponding pre_stack_stx tx.
    let stack_stx_0_second_attempt = BitcoinTransaction {
        txid: Txid([4; 32]),
        vtxindex: 2,
        opcode: Opcodes::StackStx as u8,
        data: vec![1; 80],
        data_amt: 0,
        inputs: vec![BitcoinTxInput {
            keys: vec![],
            num_required: 0,
            in_type: BitcoinInputType::Standard,
            tx_ref: (pre_stack_stx_0_txid.clone(), 1),
        }],
        outputs: vec![BitcoinTxOutput {
            units: 10,
            address: BitcoinAddress {
                addrtype: BitcoinAddressType::PublicKeyHash,
                network_id: BitcoinNetworkType::Mainnet,
                bytes: Hash160([2; 20]),
            },
        }],
    };

    // this one won't have a corresponding pre_stack_stx tx.
    let stack_stx_1 = BitcoinTransaction {
        txid: Txid([3; 32]),
        vtxindex: 3,
        opcode: Opcodes::StackStx as u8,
        data: vec![1; 80],
        data_amt: 0,
        inputs: vec![BitcoinTxInput {
            keys: vec![],
            num_required: 0,
            in_type: BitcoinInputType::Standard,
            tx_ref: (Txid([0; 32]), 1),
        }],
        outputs: vec![BitcoinTxOutput {
            units: 10,
            address: BitcoinAddress {
                addrtype: BitcoinAddressType::PublicKeyHash,
                network_id: BitcoinNetworkType::Mainnet,
                bytes: Hash160([1; 20]),
            },
        }],
    };

    // this one won't use the correct output
    let stack_stx_2 = BitcoinTransaction {
        txid: Txid([8; 32]),
        vtxindex: 4,
        opcode: Opcodes::StackStx as u8,
        data: vec![1; 80],
        data_amt: 0,
        inputs: vec![BitcoinTxInput {
            keys: vec![],
            num_required: 0,
            in_type: BitcoinInputType::Standard,
            tx_ref: (pre_stack_stx_0_txid.clone(), 2),
        }],
        outputs: vec![BitcoinTxOutput {
            units: 10,
            address: BitcoinAddress {
                addrtype: BitcoinAddressType::PublicKeyHash,
                network_id: BitcoinNetworkType::Mainnet,
                bytes: Hash160([1; 20]),
            },
        }],
    };

    let ops_0 = vec![pre_stack_stx_0, stack_stx_0];

    let ops_1 = vec![stack_stx_1, stack_stx_0_second_attempt, stack_stx_2];

    let block_height_0 = 501;
    let block_hash_0 = BurnchainHeaderHash([2; 32]);
    let block_height_1 = 502;
    let block_hash_1 = BurnchainHeaderHash([3; 32]);

    let block_0 = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        block_height_0,
        &block_hash_0,
        &first_bhh,
        &ops_0,
        350,
    ));

    headers.push(BurnchainBlockHeader {
        block_height: first_block_header.block_height + 1,
        block_hash: block_hash_0.clone(),
        parent_block_hash: first_bhh.clone(),
        num_txs: ops_0.len() as u64,
        timestamp: first_block_header.timestamp + 1,
    });

    let block_1 = BurnchainBlock::Bitcoin(BitcoinBlock::new(
        block_height_1,
        &block_hash_1,
        &block_hash_0,
        &ops_1,
        360,
    ));

    headers.push(BurnchainBlockHeader {
        block_height: first_block_header.block_height + 2,
        block_hash: block_hash_1.clone(),
        parent_block_hash: block_hash_0.clone(),
        num_txs: ops_1.len() as u64,
        timestamp: first_block_header.timestamp + 2,
    });

    let processed_ops_0 = burnchain_db
        .store_new_burnchain_block(&burnchain, &headers, &block_0)
        .unwrap();

    assert_eq!(
        processed_ops_0.len(),
        1,
        "Only pre_stack_stx op should have been accepted"
    );

    let processed_ops_1 = burnchain_db
        .store_new_burnchain_block(&burnchain, &headers, &block_1)
        .unwrap();

    assert_eq!(
        processed_ops_1.len(),
        1,
        "Only one stack_stx op should have been accepted"
    );

    let expected_pre_stack_addr = StacksAddress::from_bitcoin_address(&BitcoinAddress {
        addrtype: BitcoinAddressType::PublicKeyHash,
        network_id: BitcoinNetworkType::Mainnet,
        bytes: Hash160([1; 20]),
    });

    let expected_reward_addr = StacksAddress::from_bitcoin_address(&BitcoinAddress {
        addrtype: BitcoinAddressType::PublicKeyHash,
        network_id: BitcoinNetworkType::Mainnet,
        bytes: Hash160([2; 20]),
    });

    if let BlockstackOperationType::PreStx(op) = &processed_ops_0[0] {
        assert_eq!(&op.output, &expected_pre_stack_addr);
    } else {
        panic!("EXPECTED to parse a pre stack stx op");
    }

    if let BlockstackOperationType::StackStx(op) = &processed_ops_1[0] {
        assert_eq!(&op.sender, &expected_pre_stack_addr);
        assert_eq!(&op.reward_addr, &expected_reward_addr);
        assert_eq!(op.stacked_ustx, u128::from_be_bytes([1; 16]));
        assert_eq!(op.num_cycles, 1);
    } else {
        panic!("EXPECTED to parse a stack stx op");
    }
}

pub fn make_simple_block_commit(
    burnchain: &Burnchain,
    parent: Option<&LeaderBlockCommitOp>,
    burn_header: &BurnchainBlockHeader,
    block_hash: BlockHeaderHash,
) -> LeaderBlockCommitOp {
    let block_height = burn_header.block_height;
    let mut new_op = LeaderBlockCommitOp {
        sunset_burn: 0,
        block_header_hash: block_hash,
        new_seed: VRFSeed([1u8; 32]),
        parent_block_ptr: 0,
        parent_vtxindex: 0,
        key_block_ptr: 0,
        key_vtxindex: 0,
        memo: vec![0],

        commit_outs: vec![
            StacksAddress {
                version: 26,
                bytes: Hash160::empty(),
            },
            StacksAddress {
                version: 26,
                bytes: Hash160::empty(),
            },
        ],

        burn_fee: 10000,
        input: (next_txid(), 0),
        apparent_sender: BurnchainSigner {
            public_keys: vec![StacksPublicKey::from_hex(
                "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
            )
            .unwrap()],
            num_sigs: 1,
            hash_mode: AddressHashMode::SerializeP2PKH,
        },

        txid: next_txid(),
        vtxindex: 0,
        block_height: block_height,
        burn_parent_modulus: ((block_height - 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
        burn_header_hash: burn_header.block_hash.clone(),
    };

    if burnchain.is_in_prepare_phase(block_height) {
        new_op.commit_outs = vec![StacksAddress {
            version: 26,
            bytes: Hash160::empty(),
        }];
    }

    if let Some(ref op) = parent {
        new_op.parent_block_ptr = op.block_height as u32;
        new_op.parent_vtxindex = op.vtxindex as u16;
    };

    new_op
}

#[test]
fn test_get_commit_at() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 1;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(5, 3, 2, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let mut parent = None;
    let mut parent_block_header: Option<BurnchainBlockHeader> = None;
    let mut cmts = vec![];

    for i in 0..5 {
        let hdr = BurnchainHeaderHash([(i + 1) as u8; 32]);
        let block_header = BurnchainBlockHeader {
            block_height: (first_height + i) as u64,
            block_hash: hdr,
            parent_block_hash: parent_block_header
                .as_ref()
                .map(|blk| blk.block_hash.clone())
                .unwrap_or(first_block_header.block_hash.clone()),
            num_txs: 1,
            timestamp: i as u64,
        };

        headers.push(block_header.clone());
        parent_block_header = Some(block_header);
    }

    for i in 0..5 {
        let block_header = &headers[i + 1];

        let cmt = make_simple_block_commit(
            &burnchain,
            parent.as_ref(),
            block_header,
            BlockHeaderHash([((i + 1) as u8) | 0x80; 32]),
        );
        burnchain_db
            .store_new_burnchain_block_ops_unchecked(
                &burnchain,
                &headers,
                block_header,
                &vec![BlockstackOperationType::LeaderBlockCommit(cmt.clone())],
            )
            .unwrap();

        cmts.push(cmt.clone());
        parent = Some(cmt);
    }

    for i in 0..5 {
        let cmt = BurnchainDB::get_commit_at(
            &burnchain_db.conn(),
            &headers,
            (first_height + i) as u32,
            0,
        )
        .unwrap()
        .unwrap();
        assert_eq!(cmt, cmts[i as usize]);
    }

    let cmt = BurnchainDB::get_commit_at(&burnchain_db.conn(), &headers, 5, 0)
        .unwrap()
        .unwrap();
    assert_eq!(cmt, cmts[4]);

    // fork off the last stored commit block
    let fork_hdr = BurnchainHeaderHash([90 as u8; 32]);
    let fork_block_header = BurnchainBlockHeader {
        block_height: 4,
        block_hash: fork_hdr,
        parent_block_hash: BurnchainHeaderHash([5 as u8; 32]),
        num_txs: 0,
        timestamp: 4 as u64,
    };

    burnchain_db
        .store_new_burnchain_block_ops_unchecked(&burnchain, &headers, &fork_block_header, &vec![])
        .unwrap();
    headers[4] = fork_block_header;

    let cmt = BurnchainDB::get_commit_at(&burnchain_db.conn(), &headers, 4, 0).unwrap();
    assert!(cmt.is_none());
}
