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
use std::collections::HashSet;
use std::collections::VecDeque;
use std::sync::{
    atomic::{AtomicBool, AtomicU64, Ordering},
    mpsc::sync_channel,
    Arc, RwLock,
};

use rusqlite::Connection;

use address;
use burnchains::affirmation::*;
use burnchains::bitcoin::address::BitcoinAddress;
use burnchains::bitcoin::indexer::BitcoinIndexer;
use burnchains::bitcoin::BitcoinNetworkType;
use burnchains::tests::db::*;
use burnchains::{db::*, *};
use burnchains::{BurnchainBlock, BurnchainBlockHeader, Txid};
use chainstate;
use chainstate::burn::db::sortdb::SortitionDB;
use chainstate::burn::operations::leader_block_commit::*;
use chainstate::burn::operations::*;
use chainstate::burn::*;
use chainstate::coordinator::{Error as CoordError, *};
use chainstate::stacks::*;
use clarity_vm::clarity::ClarityConnection;
use core;
use core::*;
use monitoring::increment_stx_blocks_processed_counter;
use util::hash::{hex_bytes, Hash160};
use util::vrf::*;
use vm::{
    costs::{ExecutionCost, LimitedCostTracker},
    types::PrincipalData,
    types::QualifiedContractIdentifier,
    Value,
};

use crate::types::chainstate::StacksBlockId;
use crate::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, PoxId, SortitionId, StacksAddress, VRFSeed,
};
use crate::types::proof::TrieHash;
use crate::{types, util};

use chainstate::coordinator::tests::*;

#[test]
fn affirmation_map_encode_decode() {
    assert_eq!(AffirmationMap::decode(""), Some(AffirmationMap::empty()));
    assert_eq!(
        AffirmationMap::decode("anp"),
        Some(AffirmationMap::new(vec![
            AffirmationMapEntry::PoxAnchorBlockAbsent,
            AffirmationMapEntry::Nothing,
            AffirmationMapEntry::PoxAnchorBlockPresent
        ]))
    );
    assert_eq!(AffirmationMap::decode("x"), None);

    assert_eq!(AffirmationMap::empty().encode(), "".to_string());
    assert_eq!(
        AffirmationMap::new(vec![
            AffirmationMapEntry::PoxAnchorBlockAbsent,
            AffirmationMapEntry::Nothing,
            AffirmationMapEntry::PoxAnchorBlockPresent
        ])
        .encode(),
        "anp".to_string()
    );
}

#[test]
fn affirmation_map_find_divergence() {
    assert_eq!(
        AffirmationMap::decode("aaa")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("aaa").unwrap()),
        None
    );
    assert_eq!(
        AffirmationMap::decode("aaa")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("aaaa").unwrap()),
        Some(3)
    );
    assert_eq!(
        AffirmationMap::decode("aaa")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("aa").unwrap()),
        None
    );
    assert_eq!(
        AffirmationMap::decode("apa")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("aaa").unwrap()),
        Some(1)
    );
    assert_eq!(
        AffirmationMap::decode("apa")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("aaaa").unwrap()),
        Some(1)
    );
    assert_eq!(
        AffirmationMap::decode("naa")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("aa").unwrap()),
        Some(0)
    );
    assert_eq!(
        AffirmationMap::decode("napn")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("").unwrap()),
        None
    );
    assert_eq!(
        AffirmationMap::decode("pn")
            .unwrap()
            .find_divergence(&AffirmationMap::decode("n").unwrap()),
        Some(0)
    );
}

fn make_simple_key_register(
    burn_header_hash: &BurnchainHeaderHash,
    block_height: u64,
    vtxindex: u32,
) -> LeaderKeyRegisterOp {
    LeaderKeyRegisterOp {
        consensus_hash: ConsensusHash::from_bytes(
            &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
        )
        .unwrap(),
        public_key: VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap(),
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

        txid: next_txid(),
        vtxindex: vtxindex,
        block_height: block_height,
        burn_header_hash: burn_header_hash.clone(),
    }
}

pub fn make_reward_cycle_with_vote(
    burnchain_db: &mut BurnchainDB,
    burnchain: &Burnchain,
    key: &LeaderKeyRegisterOp,
    headers: &mut Vec<BurnchainBlockHeader>,
    mut parent_commits: Vec<Option<LeaderBlockCommitOp>>,
    confirm_anchor_block: bool,
) -> (
    Vec<BurnchainBlockHeader>,
    Vec<Vec<Option<LeaderBlockCommitOp>>>,
) {
    let mut new_headers = vec![];
    let mut new_commits = vec![];

    let first_block_header = burnchain_db.get_first_header().unwrap();
    let mut current_header = burnchain_db.get_canonical_chain_tip().unwrap();
    let mut height = current_header.block_height + 1;
    let mut parent_block_header: Option<BurnchainBlockHeader> =
        Some(headers.last().unwrap().to_owned());

    for i in 0..burnchain.pox_constants.reward_cycle_length {
        let block_header = BurnchainBlockHeader {
            block_height: height,
            block_hash: next_burn_header_hash(),
            parent_block_hash: parent_block_header
                .as_ref()
                .map(|blk| blk.block_hash.clone())
                .unwrap_or(first_block_header.block_hash.clone()),
            num_txs: parent_commits.len() as u64,
            timestamp: i as u64,
        };

        let ops = if current_header == first_block_header {
            // first-ever block -- add only the leader key
            let mut key_insert = key.clone();
            key_insert.burn_header_hash = block_header.block_hash.clone();

            test_debug!(
                "Insert key-register in {}: {},{},{} in block {}",
                &key_insert.burn_header_hash,
                &key_insert.txid,
                key_insert.block_height,
                key_insert.vtxindex,
                block_header.block_height
            );

            new_commits.push(vec![None; parent_commits.len()]);
            vec![BlockstackOperationType::LeaderKeyRegister(
                key_insert.clone(),
            )]
        } else {
            let mut commits = vec![];
            for i in 0..parent_commits.len() {
                let mut block_commit = make_simple_block_commit(
                    &burnchain,
                    parent_commits[i].as_ref(),
                    &block_header,
                    next_block_hash(),
                );
                block_commit.key_block_ptr = key.block_height as u32;
                block_commit.key_vtxindex = key.vtxindex as u16;
                block_commit.vtxindex += i as u32;
                block_commit.burn_parent_modulus = if height > 0 {
                    ((height - 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8
                } else {
                    BURN_BLOCK_MINED_AT_MODULUS as u8 - 1
                };

                assert_eq!(block_commit.burn_header_hash, block_header.block_hash);
                assert_eq!(block_commit.block_height, block_header.block_height);

                let append = if !burnchain.is_in_prepare_phase(block_commit.block_height) {
                    // non-prepare-phase commits always confirm their parent
                    true
                } else {
                    if confirm_anchor_block {
                        // all block-commits confirm anchor block
                        true
                    } else {
                        // fewer than anchor_threshold commits confirm anchor block
                        let next_rc_start = burnchain.reward_cycle_to_block_height(
                            burnchain
                                .block_height_to_reward_cycle(block_commit.block_height)
                                .unwrap()
                                + 1,
                        );
                        if block_commit.block_height
                            + (burnchain.pox_constants.anchor_threshold as u64)
                            + 1
                            < next_rc_start
                        {
                            // in first half of prepare phase, so confirm
                            true
                        } else {
                            // in second half of prepare phase, so don't confirm
                            false
                        }
                    }
                };

                if append {
                    test_debug!(
                        "Insert block-commit in {}: {},{},{}, builds on {},{}",
                        &block_commit.burn_header_hash,
                        &block_commit.txid,
                        block_commit.block_height,
                        block_commit.vtxindex,
                        block_commit.parent_block_ptr,
                        block_commit.parent_vtxindex
                    );

                    if let Some(ref parent_commit) = parent_commits[i].as_ref() {
                        assert!(
                            parent_commit.block_height as u64 != block_commit.block_height as u64
                        );
                        assert!(
                            parent_commit.block_height as u64
                                == block_commit.parent_block_ptr as u64
                        );
                        assert!(
                            parent_commit.vtxindex as u64 == block_commit.parent_vtxindex as u64
                        );
                    }

                    parent_commits[i] = Some(block_commit.clone());
                    commits.push(Some(block_commit.clone()));
                } else {
                    test_debug!(
                        "Do NOT insert block-commit in {}: {},{},{}",
                        &block_commit.burn_header_hash,
                        &block_commit.txid,
                        block_commit.block_height,
                        block_commit.vtxindex
                    );

                    commits.push(None);
                }
            }
            new_commits.push(commits.clone());
            commits
                .into_iter()
                .filter_map(|cmt| cmt)
                .map(|cmt| BlockstackOperationType::LeaderBlockCommit(cmt))
                .collect()
        };

        burnchain_db
            .store_new_burnchain_block_ops_unchecked(burnchain, headers, &block_header, &ops)
            .unwrap();

        headers.push(block_header.clone());
        new_headers.push(block_header.clone());
        parent_block_header = Some(block_header);

        current_header = burnchain_db.get_canonical_chain_tip().unwrap();
        height = current_header.block_height + 1;
    }

    (new_headers, new_commits)
}

fn make_simple_reward_cycle(
    burnchain_db: &mut BurnchainDB,
    burnchain: &Burnchain,
    key: &LeaderKeyRegisterOp,
    headers: &mut Vec<BurnchainBlockHeader>,
    parent_commit: Option<LeaderBlockCommitOp>,
) -> (Vec<BurnchainBlockHeader>, Vec<Option<LeaderBlockCommitOp>>) {
    let (new_headers, commits) =
        make_reward_cycle(burnchain_db, burnchain, key, headers, vec![parent_commit]);
    (
        new_headers,
        commits
            .into_iter()
            .map(|mut cmts| cmts.pop().unwrap())
            .collect(),
    )
}

pub fn make_reward_cycle(
    burnchain_db: &mut BurnchainDB,
    burnchain: &Burnchain,
    key: &LeaderKeyRegisterOp,
    headers: &mut Vec<BurnchainBlockHeader>,
    parent_commits: Vec<Option<LeaderBlockCommitOp>>,
) -> (
    Vec<BurnchainBlockHeader>,
    Vec<Vec<Option<LeaderBlockCommitOp>>>,
) {
    make_reward_cycle_with_vote(burnchain_db, burnchain, key, headers, parent_commits, true)
}

pub fn make_reward_cycle_without_anchor(
    burnchain_db: &mut BurnchainDB,
    burnchain: &Burnchain,
    key: &LeaderKeyRegisterOp,
    headers: &mut Vec<BurnchainBlockHeader>,
    parent_commits: Vec<Option<LeaderBlockCommitOp>>,
) -> (
    Vec<BurnchainBlockHeader>,
    Vec<Vec<Option<LeaderBlockCommitOp>>>,
) {
    make_reward_cycle_with_vote(burnchain_db, burnchain, key, headers, parent_commits, false)
}

#[test]
fn test_read_prepare_phase_commits() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(10, 5, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();
    assert_eq!(&first_block_header.block_hash, &first_bhh);
    assert_eq!(first_block_header.block_height, first_height);
    assert_eq!(first_block_header.timestamp, first_timestamp as u64);
    /*
    assert_eq!(
        &first_block_header.parent_block_hash,
        &BurnchainHeaderHash::sentinel()
    );
    */
    eprintln!(
        "First block parent is {}",
        &first_block_header.parent_block_hash
    );

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);
    let (next_headers, commits) = make_simple_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        None,
    );

    assert_eq!(
        commits.len() as u32,
        burnchain.pox_constants.reward_cycle_length
    );
    assert!(commits[0].is_none());
    for i in 1..burnchain.pox_constants.reward_cycle_length {
        assert!(commits[i as usize].is_some());
    }

    let all_ops = read_prepare_phase_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &burnchain.pox_constants,
        first_block_header.block_height,
        0,
    )
    .unwrap();
    assert_eq!(all_ops.len() as u32, burnchain.pox_constants.prepare_length);
    for i in 0..burnchain.pox_constants.prepare_length {
        assert_eq!(all_ops[i as usize].len(), 1);

        let opdata = &all_ops[i as usize][0];
        assert_eq!(
            opdata,
            commits[(i + burnchain.pox_constants.reward_cycle_length
                - burnchain.pox_constants.prepare_length) as usize]
                .as_ref()
                .unwrap()
        );
    }
}

#[test]
fn test_parent_block_commits() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(10, 5, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits) = make_simple_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        None,
    );

    let all_ops = read_prepare_phase_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &burnchain.pox_constants,
        first_block_header.block_height,
        0,
    )
    .unwrap();
    let parent_commits =
        read_parent_block_commits(&burnchain_db.tx_begin().unwrap(), &headers, &all_ops).unwrap();

    // this is a simple reward cycle -- each block-commit has a unique parent
    assert_eq!(parent_commits.len(), all_ops.len());

    for op_list in all_ops.iter() {
        for opdata in op_list.iter() {
            let mut found_parent = false;
            for parent_commit in parent_commits.iter() {
                if parent_commit.block_height == (opdata.parent_block_ptr as u64)
                    && parent_commit.vtxindex == (opdata.parent_vtxindex as u32)
                {
                    found_parent = true;
                    break;
                }
            }
            assert!(found_parent, "did not find parent for {:?}", opdata);
        }
    }

    let mut all_ops_with_orphan = all_ops.clone();
    all_ops_with_orphan[1][0].parent_vtxindex += 1;

    let parent_commits = read_parent_block_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_with_orphan,
    )
    .unwrap();

    // this is a simple reward cycle -- each block-commit has a unique parent, except for the
    // orphan
    assert_eq!(parent_commits.len(), all_ops_with_orphan.len() - 1);

    let mut all_ops_with_same_parent = all_ops.clone();
    for ops in all_ops_with_same_parent.iter_mut() {
        for opdata in ops.iter_mut() {
            opdata.parent_block_ptr = 3;
            opdata.parent_vtxindex = 0;
        }
    }

    let parent_commits = read_parent_block_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_with_same_parent,
    )
    .unwrap();

    assert_eq!(parent_commits.len(), 1);
    assert_eq!(parent_commits[0].block_height, 3);
    assert_eq!(parent_commits[0].vtxindex, 0);
}

#[test]
fn test_filter_orphan_block_commits() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(5, 3, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits) = make_simple_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        None,
    );

    let all_ops = read_prepare_phase_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &burnchain.pox_constants,
        first_block_header.block_height,
        0,
    )
    .unwrap();
    let parent_commits =
        read_parent_block_commits(&burnchain_db.tx_begin().unwrap(), &headers, &all_ops).unwrap();

    let mut all_ops_with_orphan = all_ops.clone();
    all_ops_with_orphan[1][0].parent_vtxindex += 1;

    assert_eq!(all_ops_with_orphan[0].len(), 1);
    assert_eq!(all_ops_with_orphan[1].len(), 1);
    assert_eq!(all_ops_with_orphan[2].len(), 1);

    let parent_commits = read_parent_block_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_with_orphan,
    )
    .unwrap();
    let filtered_ops = filter_orphan_block_commits(&parent_commits, all_ops_with_orphan);

    assert_eq!(filtered_ops.len(), all_ops.len());
    assert_eq!(filtered_ops[0].len(), 1);
    assert_eq!(filtered_ops[1].len(), 0);
    assert_eq!(filtered_ops[2].len(), 1);
}

#[test]
fn test_filter_missed_block_commits() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(5, 3, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits) = make_simple_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        None,
    );

    let all_ops = read_prepare_phase_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &burnchain.pox_constants,
        first_block_header.block_height,
        0,
    )
    .unwrap();
    let parent_commits =
        read_parent_block_commits(&burnchain_db.tx_begin().unwrap(), &headers, &all_ops).unwrap();

    let mut all_ops_with_missed = all_ops.clone();
    all_ops_with_missed[1][0].burn_parent_modulus -= 1;

    assert_eq!(all_ops_with_missed[0].len(), 1);
    assert_eq!(all_ops_with_missed[1].len(), 1);
    assert_eq!(all_ops_with_missed[2].len(), 1);

    let parent_commits = read_parent_block_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_with_missed,
    )
    .unwrap();
    let filtered_ops = filter_missed_block_commits(all_ops_with_missed);

    assert_eq!(filtered_ops.len(), all_ops.len());
    assert_eq!(filtered_ops[0].len(), 1);
    assert_eq!(filtered_ops[1].len(), 0);
    assert_eq!(filtered_ops[2].len(), 1);
}

#[test]
fn test_find_heaviest_block_commit() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(5, 3, 2, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits) = make_simple_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        None,
    );

    let all_ops = read_prepare_phase_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &burnchain.pox_constants,
        first_block_header.block_height,
        0,
    )
    .unwrap();
    let parent_commits =
        read_parent_block_commits(&burnchain_db.tx_begin().unwrap(), &headers, &all_ops).unwrap();
    let filtered_ops = filter_orphan_block_commits(&parent_commits, all_ops);

    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &filtered_ops,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    // since this is just a linear chain of block-commits, the heaviest parent is the parent of the
    // first block-commit in the prepare phase
    assert_eq!(commits[1].as_ref().unwrap(), &heaviest_parent_block_commit);
    assert_eq!(descendancy, vec![vec![true], vec![true], vec![true]]);
    assert_eq!(total_confs, 3);
    assert_eq!(total_burns, 3 * 10000);

    // make a forked history, but with a best-tip
    // 1,0 <-- 2,0 <-- 3,0 <-- 4,0
    //  \
    //   `---------------------------- 5,0
    let mut all_ops_forked_majority = filtered_ops.clone();
    all_ops_forked_majority[2][0].parent_block_ptr = 1;
    all_ops_forked_majority[2][0].parent_vtxindex = 0;

    // still commit 1
    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_forked_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    assert_eq!(commits[1].as_ref().unwrap(), &heaviest_parent_block_commit);
    assert_eq!(descendancy, vec![vec![true], vec![true], vec![false]]);
    assert_eq!(total_confs, 2);
    assert_eq!(total_burns, 2 * 10000);

    // make a forked history, with another best-tip winner, but with a deeper fork split
    // 1,0 <-- 2,0 <-- 3,0
    //           \
    //            `------- 4,0 <-- 5,0
    let mut all_ops_forked_majority = filtered_ops.clone();
    all_ops_forked_majority[1][0].parent_block_ptr = 2;
    all_ops_forked_majority[1][0].parent_vtxindex = 0;

    all_ops_forked_majority[2][0].parent_block_ptr = 2;
    all_ops_forked_majority[2][0].parent_vtxindex = 0;

    // still commit 1
    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_forked_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    assert_eq!(commits[1].as_ref().unwrap(), &heaviest_parent_block_commit);
    assert_eq!(descendancy, vec![vec![true], vec![true], vec![true]]);
    assert_eq!(total_confs, 3);
    assert_eq!(total_burns, 3 * 10000);

    // make a forked history where there is no best tip, but enough confirmations
    // 1,0 <-- 2,0 <-- 3,0
    //          |\
    //          | `------- 4,0
    //          \
    //           `------------- 5,0
    let mut all_ops_no_majority = filtered_ops.clone();
    all_ops_no_majority[0][0].parent_block_ptr = 2;
    all_ops_no_majority[0][0].parent_vtxindex = 0;
    all_ops_no_majority[0][0].burn_fee = 0;

    all_ops_no_majority[1][0].parent_block_ptr = 2;
    all_ops_no_majority[1][0].parent_vtxindex = 0;
    all_ops_no_majority[1][0].burn_fee = 1;

    all_ops_no_majority[2][0].parent_block_ptr = 2;
    all_ops_no_majority[2][0].parent_vtxindex = 0;
    all_ops_no_majority[2][0].burn_fee = 2;

    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_no_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    assert_eq!(commits[1].as_ref().unwrap(), &heaviest_parent_block_commit);
    assert_eq!(descendancy, vec![vec![true], vec![true], vec![true]]);
    assert_eq!(total_confs, 3);
    assert_eq!(total_burns, 1 + 2);

    // make a forked history where there is no best tip, but enough (majority) confirmations
    // 1,0 <-- 2,0 <-- 3,0
    //  |        \
    //  |         `-------- 4,0
    //  |
    //  `----------------------- 5,0
    let mut all_ops_no_majority = filtered_ops.clone();
    all_ops_no_majority[0][0].parent_block_ptr = 2;
    all_ops_no_majority[0][0].parent_vtxindex = 0;
    all_ops_no_majority[0][0].burn_fee = 0;

    all_ops_no_majority[1][0].parent_block_ptr = 2;
    all_ops_no_majority[1][0].parent_vtxindex = 0;
    all_ops_no_majority[1][0].burn_fee = 1;

    all_ops_no_majority[2][0].parent_block_ptr = 1;
    all_ops_no_majority[2][0].parent_vtxindex = 0;
    all_ops_no_majority[2][0].burn_fee = 20;

    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_no_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    assert_eq!(commits[1].as_ref().unwrap(), &heaviest_parent_block_commit);
    assert_eq!(descendancy, vec![vec![true], vec![true], vec![false]]);
    assert_eq!(total_confs, 2);
    assert_eq!(total_burns, 1);

    // make a history where there is no anchor block, period
    // 1,0 <-- 2,0 X-- 3,0
    //
    //             X------- 4,0
    //
    //             X------------ 5,0
    let mut all_ops_no_majority = filtered_ops.clone();
    all_ops_no_majority[0][0].parent_block_ptr = 2;
    all_ops_no_majority[0][0].parent_vtxindex = 10;
    all_ops_no_majority[0][0].burn_fee = 0;

    all_ops_no_majority[1][0].parent_block_ptr = 2;
    all_ops_no_majority[1][0].parent_vtxindex = 10;
    all_ops_no_majority[1][0].burn_fee = 1;

    all_ops_no_majority[2][0].parent_block_ptr = 1;
    all_ops_no_majority[2][0].parent_vtxindex = 10;
    all_ops_no_majority[2][0].burn_fee = 20;

    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_no_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_none());
}

#[test]
fn test_find_heaviest_parent_commit_many_commits() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(5, 3, 2, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    let (next_headers, commits) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![None, None],
    );

    let all_ops = read_prepare_phase_commits(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &burnchain.pox_constants,
        first_block_header.block_height,
        0,
    )
    .unwrap();
    let parent_commits =
        read_parent_block_commits(&burnchain_db.tx_begin().unwrap(), &headers, &all_ops).unwrap();
    let filtered_ops = filter_orphan_block_commits(&parent_commits, all_ops);

    // make a history with two miners' commits.
    // sortition winners in prepare phase were 3,0; 4,1; 5,0
    // 1,0 <-- 2,0 <--- 3,0 <--- 4,0 ,--- 5,0
    //           \         \        /
    //            `---- 3,1 `--- 4,1 <--- 5,1
    let mut all_ops_no_majority = filtered_ops.clone();

    // 3,0
    all_ops_no_majority[0][0].parent_block_ptr = 2;
    all_ops_no_majority[0][0].parent_vtxindex = 0;
    all_ops_no_majority[0][0].vtxindex = 0;
    all_ops_no_majority[0][0].burn_fee = 1;

    // 3,1
    all_ops_no_majority[0][1].parent_block_ptr = 2;
    all_ops_no_majority[0][1].parent_vtxindex = 0;
    all_ops_no_majority[0][1].vtxindex = 1;
    all_ops_no_majority[0][1].burn_fee = 1;

    // 4,0
    all_ops_no_majority[1][0].parent_block_ptr = 3;
    all_ops_no_majority[1][0].parent_vtxindex = 0;
    all_ops_no_majority[1][0].vtxindex = 0;
    all_ops_no_majority[1][0].burn_fee = 2;

    // 4,1
    all_ops_no_majority[1][1].parent_block_ptr = 3;
    all_ops_no_majority[1][1].parent_vtxindex = 0;
    all_ops_no_majority[1][1].vtxindex = 1;
    all_ops_no_majority[1][1].burn_fee = 2;

    // 5,0
    all_ops_no_majority[2][0].parent_block_ptr = 4;
    all_ops_no_majority[2][0].parent_vtxindex = 1;
    all_ops_no_majority[2][0].vtxindex = 0;
    all_ops_no_majority[2][0].burn_fee = 3;

    // 5,1
    all_ops_no_majority[2][1].parent_block_ptr = 4;
    all_ops_no_majority[2][1].parent_vtxindex = 1;
    all_ops_no_majority[2][1].vtxindex = 1;
    all_ops_no_majority[2][1].burn_fee = 3;

    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_no_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    assert_eq!(
        commits[1][0].as_ref().unwrap(),
        &heaviest_parent_block_commit
    );
    assert_eq!(
        descendancy,
        vec![vec![true, true], vec![true, true], vec![true, true]]
    );
    assert_eq!(total_confs, 3);
    assert_eq!(total_burns, 1 + 1 + 2 + 2 + 3 + 3);

    // make a history with two miners' commits, with some invalid commits.
    // The heavier commit descendancy wins -- 2,1 is the anchor block.
    // 1,0 <-- 2,0 <--- 3,0 <--- 4,0 <--- 5,0 (winner)
    //  \
    //   `---- 2,1 <--- 3,1 <--- 4,1 <--- 5,1
    let mut all_ops_no_majority = filtered_ops.clone();

    // 3,0
    all_ops_no_majority[0][0].parent_block_ptr = 2;
    all_ops_no_majority[0][0].parent_vtxindex = 0;
    all_ops_no_majority[0][0].vtxindex = 0;
    all_ops_no_majority[0][0].burn_fee = 1;

    // 3,1
    all_ops_no_majority[0][1].parent_block_ptr = 2;
    all_ops_no_majority[0][1].parent_vtxindex = 1;
    all_ops_no_majority[0][1].vtxindex = 1;
    all_ops_no_majority[0][1].burn_fee = 1;

    // 4,0
    all_ops_no_majority[1][0].parent_block_ptr = 3;
    all_ops_no_majority[1][0].parent_vtxindex = 0;
    all_ops_no_majority[1][0].vtxindex = 0;
    all_ops_no_majority[1][0].burn_fee = 2;

    // 4,1
    all_ops_no_majority[1][1].parent_block_ptr = 3;
    all_ops_no_majority[1][1].parent_vtxindex = 1;
    all_ops_no_majority[1][1].vtxindex = 1;
    all_ops_no_majority[1][1].burn_fee = 2;

    // 5,0
    all_ops_no_majority[2][0].parent_block_ptr = 4;
    all_ops_no_majority[2][0].parent_vtxindex = 0;
    all_ops_no_majority[2][0].vtxindex = 0;
    all_ops_no_majority[2][0].burn_fee = 4;

    // 5,1
    all_ops_no_majority[2][1].parent_block_ptr = 4;
    all_ops_no_majority[2][1].parent_vtxindex = 1;
    all_ops_no_majority[2][1].vtxindex = 1;
    all_ops_no_majority[2][1].burn_fee = 3;

    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_no_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    // best option wins
    assert_eq!(
        commits[1][0].as_ref().unwrap(),
        &heaviest_parent_block_commit
    );
    assert_eq!(
        descendancy,
        vec![vec![true, false], vec![true, false], vec![true, false]]
    );
    assert_eq!(total_confs, 3);
    assert_eq!(total_burns, 1 + 2 + 4);

    // make a history with two miners' commits, with some invalid commits.
    // commit descendancy weight is a tie, so highest commit is the anchor block (2,1)
    // 1,0 <-- 2,0 <--- 3,0 <--- 4,0 <--- 5,0
    //  \
    //   `---- 2,1 <--- 3,1 <--- 4,1 <--- 5,1 (winner)
    let mut all_ops_no_majority = filtered_ops.clone();

    // 3,0
    all_ops_no_majority[0][0].parent_block_ptr = 2;
    all_ops_no_majority[0][0].parent_vtxindex = 0;
    all_ops_no_majority[0][0].vtxindex = 0;
    all_ops_no_majority[0][0].burn_fee = 1;

    // 3,1
    all_ops_no_majority[0][1].parent_block_ptr = 2;
    all_ops_no_majority[0][1].parent_vtxindex = 1;
    all_ops_no_majority[0][1].vtxindex = 1;
    all_ops_no_majority[0][1].burn_fee = 1;

    // 4,0
    all_ops_no_majority[1][0].parent_block_ptr = 3;
    all_ops_no_majority[1][0].parent_vtxindex = 0;
    all_ops_no_majority[1][0].vtxindex = 0;
    all_ops_no_majority[1][0].burn_fee = 2;

    // 4,1
    all_ops_no_majority[1][1].parent_block_ptr = 3;
    all_ops_no_majority[1][1].parent_vtxindex = 1;
    all_ops_no_majority[1][1].vtxindex = 1;
    all_ops_no_majority[1][1].burn_fee = 2;

    // 5,0
    all_ops_no_majority[2][0].parent_block_ptr = 4;
    all_ops_no_majority[2][0].parent_vtxindex = 0;
    all_ops_no_majority[2][0].vtxindex = 0;
    all_ops_no_majority[2][0].burn_fee = 3;

    // 5,1
    all_ops_no_majority[2][1].parent_block_ptr = 4;
    all_ops_no_majority[2][1].parent_vtxindex = 1;
    all_ops_no_majority[2][1].vtxindex = 1;
    all_ops_no_majority[2][1].burn_fee = 3;

    let heaviest_parent_commit_opt = find_heaviest_block_commit(
        &burnchain_db.tx_begin().unwrap(),
        &headers,
        &all_ops_no_majority,
        burnchain.pox_constants.anchor_threshold,
    )
    .unwrap();
    assert!(heaviest_parent_commit_opt.is_some());
    let (heaviest_parent_block_commit, descendancy, total_confs, total_burns) =
        heaviest_parent_commit_opt.unwrap();

    // best option wins
    assert_eq!(
        commits[1][1].as_ref().unwrap(),
        &heaviest_parent_block_commit
    );
    assert_eq!(
        descendancy,
        vec![vec![false, true], vec![false, true], vec![false, true]]
    );
    assert_eq!(total_confs, 3);
    assert_eq!(total_burns, 1 + 2 + 3);
}

#[test]
fn test_update_pox_affirmation_maps_3_forks() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(10, 5, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits_0) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![None],
    );

    // no anchor blocks recorded, yet!
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0: before update: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("n").unwrap());

    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_none());

    update_pox_affirmation_maps(&mut burnchain_db, &headers, 0, &burnchain).unwrap();

    // there's only one anchor block
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());

    // the anchor block itself affirms nothing, since it isn't built on an anchor block
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0: after update: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("p").unwrap());

    let anchor_block_0 = BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .unwrap()
        .0;
    eprintln!("anchor block 1 at height {}", anchor_block_0.block_height);
    assert!(anchor_block_0.block_height < commits_0[7][0].as_ref().unwrap().block_height);

    // descend from a prepare-phase commit in rc 0, so affirms rc 0's anchor block
    let (next_headers, commits_1) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[7][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 1, &burnchain).unwrap();

    // there's two anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=1: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("p").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pp").unwrap());

    // descend from a prepare-phase commit in rc 0, so affirms rc 0's anchor block but not rc
    // 1's
    assert!(anchor_block_0.block_height < commits_0[6][0].as_ref().unwrap().block_height);
    let (next_headers, commits_2) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[6][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 2, &burnchain).unwrap();

    // there's three anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_some());

    // there are two equivalently heavy affirmation maps, but the affirmation map discovered later
    // is the heaviest.
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=2: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("pa").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pap").unwrap());

    // descend from a prepare-phase commit in rc 0, so affirms rc 0's anchor block, but not rc
    // 1's or rc 2's
    assert!(anchor_block_0.block_height < commits_0[8][0].as_ref().unwrap().block_height);
    let (next_headers, commits_3) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[8][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 3, &burnchain).unwrap();

    // there are three equivalently heavy affirmation maps, but the affirmation map discovered last
    // is the heaviest.
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=3: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("paa").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("paap").unwrap());
}

#[test]
fn test_update_pox_affirmation_maps_unique_anchor_block() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(10, 5, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits_0) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![None],
    );

    // no anchor blocks recorded, yet!
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0: before update: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("n").unwrap());

    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_none());

    update_pox_affirmation_maps(&mut burnchain_db, &headers, 0, &burnchain).unwrap();

    // there's only one anchor block
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());

    // the anchor block itself affirms nothing, since it isn't built on an anchor block
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0: after update: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("p").unwrap());

    let anchor_block_0 = BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .unwrap()
        .0;
    eprintln!("anchor block 1 at height {}", anchor_block_0.block_height);
    assert!(anchor_block_0.block_height < commits_0[7][0].as_ref().unwrap().block_height);

    // try and select the same anchor block, twice
    let mut dup_commits = commits_0.clone();
    for (i, cmts) in dup_commits.iter_mut().enumerate() {
        let block_header = BurnchainBlockHeader {
            block_height: (i + commits_0.len() + 1) as u64,
            block_hash: next_burn_header_hash(),
            parent_block_hash: headers
                .last()
                .map(|blk| blk.block_hash.clone())
                .unwrap_or(first_bhh.clone()),
            num_txs: cmts.len() as u64,
            timestamp: (i + commits_0.len()) as u64,
        };

        for cmt_opt in cmts.iter_mut() {
            if let Some(cmt) = cmt_opt.as_mut() {
                cmt.block_height = block_header.block_height;
                cmt.parent_block_ptr = anchor_block_0.block_height as u32;
                cmt.parent_vtxindex = anchor_block_0.vtxindex as u16;
                cmt.burn_parent_modulus =
                    ((cmt.block_height - 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8;
                cmt.burn_header_hash = block_header.block_hash.clone();
                cmt.block_header_hash = next_block_hash();
            }
        }

        headers.push(block_header.clone());

        let cmt_ops: Vec<BlockstackOperationType> = cmts
            .iter()
            .filter_map(|op| op.clone())
            .map(|op| BlockstackOperationType::LeaderBlockCommit(op))
            .collect();

        burnchain_db
            .store_new_burnchain_block_ops_unchecked(&burnchain, &headers, &block_header, &cmt_ops)
            .unwrap();
    }

    update_pox_affirmation_maps(&mut burnchain_db, &headers, 1, &burnchain).unwrap();

    // there's still only one anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_none());

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=1: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pn").unwrap());
}

#[test]
fn test_update_pox_affirmation_maps_absent() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(10, 5, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // make two histories -- one with an anchor block, and one without.
    let (next_headers, commits_0) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![None, None],
    );

    // no anchor blocks recorded, yet!
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    assert_eq!(heaviest_am, AffirmationMap::empty());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_none());

    update_pox_affirmation_maps(&mut burnchain_db, &headers, 0, &burnchain).unwrap();

    // there's only one anchor block, and it's at vtxindex 1 (not 0)
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert_eq!(
        BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
            .unwrap()
            .unwrap()
            .0
            .vtxindex,
        1
    );
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_none());

    // the anchor block itself affirms nothing
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("p").unwrap());

    for i in 5..10 {
        let block_commit = BurnchainDB::get_block_commit(
            burnchain_db.conn(),
            &commits_0[i][0].as_ref().unwrap().txid,
        )
        .unwrap()
        .unwrap();
        assert_eq!(block_commit.vtxindex, 0);

        let block_commit_metadata = BurnchainDB::get_commit_metadata(
            burnchain_db.conn(),
            &block_commit.burn_header_hash,
            &block_commit.txid,
        )
        .unwrap()
        .unwrap();
        assert_eq!(block_commit_metadata.anchor_block_descendant, None);
    }

    // build a second reward cycle off of a commit that does _not_ affirm the first anchor
    // block
    let (next_headers, commits_1) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[9][1].clone(), commits_0[9][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 1, &burnchain).unwrap();

    // the second anchor block affirms that the first anchor block is missing.
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=1: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("a").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("ap").unwrap());

    // build a third reward cycle off of a commit in the second reward cycle, but make it so
    // that there is no anchor block mined
    let (next_headers, commits_2) = make_reward_cycle_without_anchor(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_1[9][0].clone(), commits_1[9][1].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 2, &burnchain).unwrap();

    // there isn't a third anchor block
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());

    // heaviest _anchor block_ affirmation map is unchanged.
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=2: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("a").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("apn").unwrap());

    // build a fourth reward cycle off of a commit in the third reward cycle, but make it so
    // that there is no anchor block mined
    assert!(commits_2[5][0].is_some());
    assert!(commits_2[5][1].is_some());
    let (next_headers, commits_3) = make_reward_cycle_without_anchor(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_2[5][0].clone(), commits_2[5][1].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 3, &burnchain).unwrap();

    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_none());

    // heaviest _anchor block_ affirmation map is unchanged.
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=3: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("a").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("apnn").unwrap());

    // make a fourth fifth cycle, again with a missing anchor block
    assert!(commits_3[5][0].is_some());
    assert!(commits_3[5][1].is_some());
    let (next_headers, commits_4) = make_reward_cycle_without_anchor(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_3[5][0].clone(), commits_3[5][1].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 4, &burnchain).unwrap();

    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 4)
        .unwrap()
        .is_none());

    // heaviest _anchor block_ affirmation map advances
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=4: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("a").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("apnnn").unwrap());

    // make a fifth reward cycle, but with an anchor block.  Affirms the first anchor block by
    // descending from a chain that descends from it.
    assert!(commits_4[5][0].is_some());
    assert!(commits_4[5][1].is_some());
    let (next_headers, commits_5) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_4[5][1].clone(), commits_4[5][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 5, &burnchain).unwrap();

    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 4)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 5)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 6)
        .unwrap()
        .is_some());

    // heaviest _anchor block_ affirmation map advances, since the new anchor block affirms the
    // last 4 reward cycles, including the anchor block mined in the first reward cycle
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=5: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    // anchor block was chosen in the last reward cycle, and in doing so created the heaviest
    // affirmation map for an anchor block, so the canonical affirmation map is
    // whatever that last anchor block affirmed
    assert_eq!(heaviest_am, AffirmationMap::decode("pannn").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pannnp").unwrap());

    // make a third history that affirms _nothing_.  It should eventually overtake this last
    // heaviest affirmation map
    let mut start = vec![commits_0[3][1].clone()];
    for i in 0..6 {
        let (next_headers, commits) = make_reward_cycle_with_vote(
            &mut burnchain_db,
            &burnchain,
            &key_register,
            &mut headers,
            start,
            false,
        );
        update_pox_affirmation_maps(&mut burnchain_db, &headers, 6 + i, &burnchain).unwrap();
        start = vec![commits[5][0].clone()];

        let heaviest_am =
            BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
                .unwrap();
        let canonical_am =
            BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| {
                true
            })
            .unwrap();
        eprintln!(
            "rc={}: heaviest = {}, canonical = {}",
            6 + i,
            &heaviest_am,
            &canonical_am
        );
    }

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=11: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("pannn").unwrap());
    assert_eq!(
        canonical_am,
        AffirmationMap::decode("pannnpnnnnnn").unwrap()
    );

    // other affirmation map should be present
    let unaffirmed_am = AffirmationMap::decode("aannnannnnnn").unwrap();
    let am_id = BurnchainDB::get_affirmation_map_id(burnchain_db.conn(), &unaffirmed_am)
        .unwrap()
        .unwrap();
    let weight = BurnchainDB::get_affirmation_weight(burnchain_db.conn(), am_id)
        .unwrap()
        .unwrap();
    assert_eq!(weight, 9);
}

#[test]
fn test_update_pox_affirmation_maps_nothing() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(10, 5, 3, 3, 0, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits_0) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![None],
    );

    // no anchor blocks recorded, yet!
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    assert_eq!(heaviest_am, AffirmationMap::empty());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_none());

    update_pox_affirmation_maps(&mut burnchain_db, &headers, 0, &burnchain).unwrap();

    // there's only one anchor block
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());

    // the anchor block itself affirms nothing, since it isn't built on an anchor block
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("p").unwrap());

    // build a second reward cycle off of the first, but with no anchor block
    let (next_headers, commits_1) = make_reward_cycle_with_vote(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[9][0].clone()],
        false,
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 1, &burnchain).unwrap();

    // there's still one anchor block
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_none());

    // second reward cycle doesn't have an anchor block, so there's no heaviest anchor block
    // affirmation map yet
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=1: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pn").unwrap());

    // build a 3rd reward cycle, but it affirms an anchor block
    let last_commit_1 = {
        let mut last_commit = None;
        for i in 0..commits_1.len() {
            if commits_1[i][0].is_some() {
                last_commit = commits_1[i][0].clone();
            }
        }
        last_commit
    };

    let (next_headers, commits_2) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![last_commit_1],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 2, &burnchain).unwrap();

    // there's two anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 4)
        .unwrap()
        .is_none());

    // there's no anchor block in rc 1
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=2: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("pn").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pnp").unwrap());

    // build a fourth reward cycle, with no vote
    let (next_headers, commits_3) = make_reward_cycle_with_vote(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_2[9][0].clone()],
        false,
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 3, &burnchain).unwrap();

    // there are three equivalently heavy affirmation maps, but the affirmation map discovered last
    // is the heaviest.  BUT THIS TIME, MAKE THE UNCONFIRMED ORACLE DENY THAT THIS LAST
    // ANCHORED BLOCK EXISTS.
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| false)
            .unwrap();
    eprintln!(
        "rc=3 (deny): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("pn").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pnan").unwrap());

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=3 (exist): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("pn").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pnpn").unwrap());
}

#[test]
fn test_update_pox_affirmation_fork_2_cycles() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(5, 2, 2, 25, 5, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits_0) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![None],
    );

    // no anchor blocks recorded, yet!
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    assert_eq!(heaviest_am, AffirmationMap::empty());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_none());

    update_pox_affirmation_maps(&mut burnchain_db, &headers, 0, &burnchain).unwrap();

    // there's only one anchor block
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());

    // the anchor block itself affirms nothing, since it isn't built on an anchor block
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0 (true): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("p").unwrap());

    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| false)
            .unwrap();
    eprintln!(
        "rc=0 (false): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(canonical_am, AffirmationMap::decode("a").unwrap());

    // build a second reward cycle off of the first
    let (next_headers, commits_1) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[4][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 1, &burnchain).unwrap();

    // there's two anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());

    // the network affirms two anchor blocks, but the second anchor block only affirms the
    // first anchor block.
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=1 (true): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("p").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pp").unwrap());

    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| false)
            .unwrap();
    eprintln!(
        "rc=1 (false): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(canonical_am, AffirmationMap::decode("pa").unwrap());

    // build a third reward cycle off of the first, before the 2nd's anchor block
    let (next_headers, commits_2) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[1][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 2, &burnchain).unwrap();

    // there's four anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_some());

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=2 (true): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("p").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("ppp").unwrap());

    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| false)
            .unwrap();
    eprintln!(
        "rc=2 (false): heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(canonical_am, AffirmationMap::decode("paa").unwrap());

    // build a fourth reward cycle off of the third
    let (next_headers, commits_3) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_2[4][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 3, &burnchain).unwrap();

    // there's four anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 4)
        .unwrap()
        .is_some());

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=3: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("aap").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("aapp").unwrap());
}

#[test]
fn test_update_pox_affirmation_fork_duel() {
    let first_bhh = BurnchainHeaderHash([0; 32]);
    let first_timestamp = 0;
    let first_height = 0;

    let mut burnchain = Burnchain::regtest(":memory:");
    burnchain.pox_constants = PoxConstants::new(5, 2, 2, 25, 5, 99, 100);
    burnchain.first_block_height = first_height;
    burnchain.first_block_hash = first_bhh.clone();
    burnchain.first_block_timestamp = first_timestamp;

    let mut burnchain_db = BurnchainDB::connect(":memory:", &burnchain, true).unwrap();

    let first_block_header = burnchain_db.get_canonical_chain_tip().unwrap();

    let mut headers = vec![first_block_header.clone()];
    let key_register = make_simple_key_register(&first_block_header.block_hash, 0, 1);

    // first reward cycle is all (linear) commits, so it must elect an anchor block
    let (next_headers, commits_0) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![None],
    );

    // no anchor blocks recorded, yet!
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    assert_eq!(heaviest_am, AffirmationMap::empty());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_none());

    update_pox_affirmation_maps(&mut burnchain_db, &headers, 0, &burnchain).unwrap();

    // there's only one anchor block
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());

    // the anchor block itself affirms nothing, since it isn't built on an anchor block
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=0: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("p").unwrap());

    // build a second reward cycle off of the first, but at the start
    assert!(commits_0[1][0].is_some());
    let (next_headers, commits_1) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[1][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 1, &burnchain).unwrap();

    // there's two anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());

    // the network affirms two anchor blocks, but the second one wins
    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=1: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("a").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("ap").unwrap());

    // build a third reward cycle off of the first
    assert!(commits_0[4][0].clone().unwrap().block_height == 5);
    let (next_headers, commits_2) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_0[4][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 2, &burnchain).unwrap();

    // there's four anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_some());

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=2: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("pa").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("pap").unwrap());

    // build a fourth reward cycle off of the second
    assert!(commits_1[4][0].clone().unwrap().block_height == 10);
    let (next_headers, commits_3) = make_reward_cycle(
        &mut burnchain_db,
        &burnchain,
        &key_register,
        &mut headers,
        vec![commits_1[4][0].clone()],
    );
    update_pox_affirmation_maps(&mut burnchain_db, &headers, 3, &burnchain).unwrap();

    // there's four anchor blocks
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 0)
        .unwrap()
        .is_none());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 1)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 2)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 3)
        .unwrap()
        .is_some());
    assert!(BurnchainDB::get_anchor_block_commit(burnchain_db.conn(), 4)
        .unwrap()
        .is_some());

    let heaviest_am =
        BurnchainDB::get_heaviest_anchor_block_affirmation_map(burnchain_db.conn(), &burnchain)
            .unwrap();
    let canonical_am =
        BurnchainDB::get_canonical_affirmation_map(burnchain_db.conn(), &burnchain, |_, _| true)
            .unwrap();
    eprintln!(
        "rc=3: heaviest = {}, canonical = {}",
        &heaviest_am, &canonical_am
    );

    assert_eq!(heaviest_am, AffirmationMap::decode("apa").unwrap());
    assert_eq!(canonical_am, AffirmationMap::decode("apap").unwrap());
}
