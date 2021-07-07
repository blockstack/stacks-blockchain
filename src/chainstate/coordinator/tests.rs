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
use burnchains::{db::*, *};
use chainstate;
use chainstate::burn::db::sortdb::SortitionDB;
use chainstate::burn::distribution::BurnSamplePoint;
use chainstate::burn::operations::leader_block_commit::*;
use chainstate::burn::operations::*;
use chainstate::burn::*;
use chainstate::coordinator::{Error as CoordError, *};
use chainstate::stacks::db::{
    accounts::MinerReward, ClarityTx, StacksChainState, StacksHeaderInfo,
};
use chainstate::stacks::*;
use clarity_vm::clarity::ClarityConnection;
use core;
use core::*;
use monitoring::increment_stx_blocks_processed_counter;
use util::hash::Hash160;
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

lazy_static! {
    static ref BURN_BLOCK_HEADERS: Arc<AtomicU64> = Arc::new(AtomicU64::new(1));
    static ref TXIDS: Arc<AtomicU64> = Arc::new(AtomicU64::new(1));
    static ref MBLOCK_PUBKHS: Arc<AtomicU64> = Arc::new(AtomicU64::new(1));
}

pub fn next_burn_header_hash() -> BurnchainHeaderHash {
    let cur = BURN_BLOCK_HEADERS.fetch_add(1, Ordering::SeqCst);
    let mut bytes = vec![];
    bytes.extend_from_slice(&cur.to_le_bytes());
    bytes.extend_from_slice(&[0; 24]);
    BurnchainHeaderHash::from_bytes(&bytes).unwrap()
}

pub fn next_txid() -> Txid {
    let cur = TXIDS.fetch_add(1, Ordering::SeqCst);
    let mut bytes = vec![];
    bytes.extend_from_slice(&cur.to_le_bytes());
    bytes.extend_from_slice(&[1; 24]);
    Txid::from_bytes(&bytes).unwrap()
}

pub fn next_hash160() -> Hash160 {
    let cur = MBLOCK_PUBKHS.fetch_add(1, Ordering::SeqCst);
    let mut bytes = vec![];
    bytes.extend_from_slice(&cur.to_le_bytes());
    bytes.extend_from_slice(&[2; 12]);
    Hash160::from_bytes(&bytes).unwrap()
}

/// Produce a burn block, insert it into burnchain_db, and insert it into others as well
pub fn produce_burn_block<'a, I: Iterator<Item = &'a mut BurnchainDB>>(
    burnchain_db: &mut BurnchainDB,
    par: &BurnchainHeaderHash,
    mut ops: Vec<BlockstackOperationType>,
    others: I,
) -> BurnchainHeaderHash {
    let BurnchainBlockData {
        header: par_header, ..
    } = burnchain_db.get_burnchain_block(par).unwrap();
    assert_eq!(&par_header.block_hash, par);
    let block_height = par_header.block_height + 1;
    for op in ops.iter_mut() {
        op.set_block_height(block_height);
    }

    produce_burn_block_do_not_set_height(burnchain_db, par, ops, others)
}

fn get_burn_distribution(conn: &Connection, sortition: &SortitionId) -> Vec<BurnSamplePoint> {
    conn.query_row(
        "SELECT data FROM snapshot_burn_distributions WHERE sortition_id = ?",
        &[sortition],
        |row| {
            let data_str: String = row.get_unwrap(0);
            Ok(serde_json::from_str(&data_str).unwrap())
        },
    )
    .unwrap()
}

fn produce_burn_block_do_not_set_height<'a, I: Iterator<Item = &'a mut BurnchainDB>>(
    burnchain_db: &mut BurnchainDB,
    par: &BurnchainHeaderHash,
    mut ops: Vec<BlockstackOperationType>,
    others: I,
) -> BurnchainHeaderHash {
    let BurnchainBlockData {
        header: par_header, ..
    } = burnchain_db.get_burnchain_block(par).unwrap();
    assert_eq!(&par_header.block_hash, par);
    let block_height = par_header.block_height + 1;
    let timestamp = par_header.timestamp + 1;
    let num_txs = ops.len() as u64;
    let block_hash = next_burn_header_hash();
    let header = BurnchainBlockHeader {
        block_height,
        timestamp,
        num_txs,
        block_hash: block_hash.clone(),
        parent_block_hash: par.clone(),
    };

    for op in ops.iter_mut() {
        op.set_burn_header_hash(block_hash.clone());
    }

    burnchain_db
        .raw_store_burnchain_block(header.clone(), ops.clone())
        .unwrap();

    for other in others {
        other
            .raw_store_burnchain_block(header.clone(), ops.clone())
            .unwrap();
    }

    block_hash
}

fn p2pkh_from(sk: &StacksPrivateKey) -> StacksAddress {
    let pk = StacksPublicKey::from_private(sk);
    StacksAddress::from_public_keys(
        chainstate::stacks::C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &address::AddressHashMode::SerializeP2PKH,
        1,
        &vec![pk],
    )
    .unwrap()
}

pub fn setup_states(
    paths: &[&str],
    vrf_keys: &[VRFPrivateKey],
    committers: &[StacksPrivateKey],
    pox_consts: Option<PoxConstants>,
    initial_balances: Option<Vec<(PrincipalData, u64)>>,
) {
    let mut burn_block = None;
    let mut others = vec![];

    for path in paths.iter() {
        let burnchain = get_burnchain(path, pox_consts.clone());

        let sortition_db = SortitionDB::connect(
            &burnchain.get_db_path(),
            burnchain.first_block_height,
            &burnchain.first_block_hash,
            burnchain.first_block_timestamp.into(),
            true,
        )
        .unwrap();

        let burnchain_blocks_db = BurnchainDB::connect(
            &burnchain.get_burnchaindb_path(),
            burnchain.first_block_height,
            &burnchain.first_block_hash,
            burnchain.first_block_timestamp as u64,
            true,
        )
        .unwrap();

        if burn_block.is_none() {
            let first_sortition =
                SortitionDB::get_canonical_burn_chain_tip(sortition_db.conn()).unwrap();
            let first_consensus_hash = &first_sortition.consensus_hash;

            // build a bunch of VRF key registers

            let mut registers = vec![];
            for (ix, (sk, miner_sk)) in vrf_keys.iter().zip(committers.iter()).enumerate() {
                let public_key = VRFPublicKey::from_private(sk);
                let consensus_hash = first_consensus_hash.clone();
                let memo = vec![0];
                let address = p2pkh_from(miner_sk);
                let vtxindex = 1 + ix as u32;
                let block_height = 0;
                let burn_header_hash = BurnchainHeaderHash([0; 32]);
                let txid = next_txid();

                registers.push(BlockstackOperationType::LeaderKeyRegister(
                    LeaderKeyRegisterOp {
                        public_key,
                        consensus_hash,
                        memo,
                        address,
                        vtxindex,
                        block_height,
                        burn_header_hash,
                        txid,
                    },
                ));
            }

            burn_block.replace((
                burnchain_blocks_db,
                first_sortition.burn_header_hash,
                registers,
            ));
        } else {
            others.push(burnchain_blocks_db);
        }
    }

    let (mut burnchain_blocks_db, burn_header_hash, registers) = burn_block.take().unwrap();

    produce_burn_block(
        &mut burnchain_blocks_db,
        &burn_header_hash,
        registers,
        others.iter_mut(),
    );

    let block_limit = ExecutionCost::max_value();
    let initial_balances = initial_balances.unwrap_or(vec![]);
    for path in paths.iter() {
        let burnchain = get_burnchain(path, pox_consts.clone());

        let mut boot_data = ChainStateBootData::new(&burnchain, initial_balances.clone(), None);

        let post_flight_callback = move |clarity_tx: &mut ClarityTx| {
            let contract = util::boot::boot_code_id("pox", false);
            let sender = PrincipalData::from(contract.clone());

            clarity_tx.connection().as_transaction(|conn| {
                conn.run_contract_call(
                    &sender,
                    &contract,
                    "set-burnchain-parameters",
                    &[
                        Value::UInt(burnchain.first_block_height as u128),
                        Value::UInt(burnchain.pox_constants.prepare_length as u128),
                        Value::UInt(burnchain.pox_constants.reward_cycle_length as u128),
                        Value::UInt(burnchain.pox_constants.pox_rejection_fraction as u128),
                    ],
                    |_, _| false,
                )
                .expect("Failed to set burnchain parameters in PoX contract");
            });
        };

        boot_data.post_flight_callback = Some(Box::new(post_flight_callback));

        let (chain_state_db, _) = StacksChainState::open_and_exec(
            false,
            0x80000000,
            &format!("{}/chainstate/", path),
            Some(&mut boot_data),
            block_limit.clone(),
        )
        .unwrap();
    }
}

pub struct NullEventDispatcher;

impl BlockEventDispatcher for NullEventDispatcher {
    fn announce_block(
        &self,
        _block: StacksBlock,
        _metadata: StacksHeaderInfo,
        _receipts: Vec<StacksTransactionReceipt>,
        _parent: &StacksBlockId,
        _winner_txid: Txid,
        _rewards: Vec<MinerReward>,
        _rewards_info: Option<MinerRewardInfo>,
        _parent_burn_block_hash: BurnchainHeaderHash,
        _parent_burn_block_height: u32,
        _parent_burn_block_timestamp: u64,
    ) {
        assert!(
            false,
            "We should never try to announce to the null dispatcher"
        );
    }

    fn announce_burn_block(
        &self,
        _burn_block: &BurnchainHeaderHash,
        _burn_block_height: u64,
        _rewards: Vec<(StacksAddress, u64)>,
        _burns: u64,
        _slot_holders: Vec<StacksAddress>,
    ) {
    }

    fn dispatch_boot_receipts(&mut self, _receipts: Vec<StacksTransactionReceipt>) {}
}

pub fn make_coordinator<'a>(
    path: &str,
    burnchain: Option<Burnchain>,
) -> ChainsCoordinator<'a, NullEventDispatcher, (), OnChainRewardSetProvider> {
    let (tx, _) = sync_channel(100000);
    let burnchain = burnchain.unwrap_or_else(|| get_burnchain(path, None));
    ChainsCoordinator::test_new(&burnchain, 0x80000000, path, OnChainRewardSetProvider(), tx)
}

struct StubbedRewardSetProvider(Vec<StacksAddress>);

impl RewardSetProvider for StubbedRewardSetProvider {
    fn get_reward_set(
        &self,
        _current_burn_height: u64,
        chainstate: &mut StacksChainState,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
    ) -> Result<Vec<StacksAddress>, chainstate::coordinator::Error> {
        Ok(self.0.clone())
    }
}

fn make_reward_set_coordinator<'a>(
    path: &str,
    addrs: Vec<StacksAddress>,
    pox_consts: Option<PoxConstants>,
) -> ChainsCoordinator<'a, NullEventDispatcher, (), StubbedRewardSetProvider> {
    let (tx, _) = sync_channel(100000);
    ChainsCoordinator::test_new(
        &get_burnchain(path, pox_consts),
        0x80000000,
        path,
        StubbedRewardSetProvider(addrs),
        tx,
    )
}

pub fn get_burnchain(path: &str, pox_consts: Option<PoxConstants>) -> Burnchain {
    let mut b = Burnchain::regtest(&format!("{}/burnchain/db/", path));
    b.pox_constants = pox_consts
        .unwrap_or_else(|| PoxConstants::new(5, 3, 3, 25, 5, u64::max_value(), u64::max_value()));
    b
}

pub fn get_sortition_db(path: &str, pox_consts: Option<PoxConstants>) -> SortitionDB {
    let burnchain = get_burnchain(path, pox_consts);
    SortitionDB::open(&burnchain.get_db_path(), false).unwrap()
}

pub fn get_rw_sortdb(path: &str, pox_consts: Option<PoxConstants>) -> SortitionDB {
    let burnchain = get_burnchain(path, pox_consts);
    SortitionDB::open(&burnchain.get_db_path(), true).unwrap()
}

pub fn get_burnchain_db(path: &str, pox_consts: Option<PoxConstants>) -> BurnchainDB {
    let burnchain = get_burnchain(path, pox_consts);
    BurnchainDB::open(&burnchain.get_burnchaindb_path(), true).unwrap()
}

pub fn get_chainstate_path_str(path: &str) -> String {
    format!("{}/chainstate/", path)
}

pub fn get_chainstate(path: &str) -> StacksChainState {
    let (chainstate, _) =
        StacksChainState::open(false, 0x80000000, &get_chainstate_path_str(path)).unwrap();
    chainstate
}

fn make_genesis_block(
    sort_db: &SortitionDB,
    state: &mut StacksChainState,
    parent_block: &BlockHeaderHash,
    miner: &StacksPrivateKey,
    my_burn: u64,
    vrf_key: &VRFPrivateKey,
    key_index: u32,
) -> (BlockstackOperationType, StacksBlock) {
    make_genesis_block_with_recipients(
        sort_db,
        state,
        parent_block,
        miner,
        my_burn,
        vrf_key,
        key_index,
        None,
    )
}

/// build a stacks block with just the coinbase off of
///  parent_block, in the canonical sortition fork.
fn make_genesis_block_with_recipients(
    sort_db: &SortitionDB,
    state: &mut StacksChainState,
    parent_block: &BlockHeaderHash,
    miner: &StacksPrivateKey,
    my_burn: u64,
    vrf_key: &VRFPrivateKey,
    key_index: u32,
    recipients: Option<&RewardSetInfo>,
) -> (BlockstackOperationType, StacksBlock) {
    let tx_auth = TransactionAuth::from_p2pkh(miner).unwrap();

    let mut tx = StacksTransaction::new(
        TransactionVersion::Testnet,
        tx_auth,
        TransactionPayload::Coinbase(CoinbasePayload([0u8; 32])),
    );
    tx.chain_id = 0x80000000;
    tx.anchor_mode = TransactionAnchorMode::OnChainOnly;
    let mut tx_signer = StacksTransactionSigner::new(&tx);
    tx_signer.sign_origin(miner).unwrap();

    let coinbase_op = tx_signer.get_tx().unwrap();

    let sortition_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();

    let parent_stacks_header = StacksHeaderInfo::regtest_genesis();

    let proof = VRF::prove(vrf_key, sortition_tip.sortition_hash.as_bytes());

    let mut builder = StacksBlockBuilder::make_regtest_block_builder(
        &parent_stacks_header,
        proof.clone(),
        0,
        next_hash160(),
    )
    .unwrap();

    let iconn = sort_db.index_conn();
    let mut epoch_tx = builder.epoch_begin(state, &iconn).unwrap();
    builder.try_mine_tx(&mut epoch_tx, &coinbase_op).unwrap();

    let block = builder.mine_anchored_block(&mut epoch_tx);
    builder.epoch_finish(epoch_tx);

    let commit_outs = if let Some(recipients) = recipients {
        let mut commit_outs = recipients
            .recipients
            .iter()
            .map(|(a, _)| a.clone())
            .collect::<Vec<StacksAddress>>();
        if commit_outs.len() == 1 {
            commit_outs.push(StacksAddress::burn_address(false))
        }
        commit_outs
    } else {
        vec![]
    };

    let commit_op = LeaderBlockCommitOp {
        sunset_burn: 0,
        block_header_hash: block.block_hash(),
        burn_fee: my_burn,
        input: (Txid([0; 32]), 0),
        apparent_sender: BurnchainSigner {
            num_sigs: 1,
            hash_mode: address::AddressHashMode::SerializeP2PKH,
            public_keys: vec![StacksPublicKey::from_private(miner)],
        },
        key_block_ptr: 1, // all registers happen in block height 1
        key_vtxindex: (1 + key_index) as u16,
        memo: vec![],
        new_seed: VRFSeed::from_proof(&proof),
        commit_outs,

        parent_block_ptr: 0,
        parent_vtxindex: 0,

        txid: next_txid(),

        vtxindex: 1,
        block_height: 0,
        burn_parent_modulus: (BURN_BLOCK_MINED_AT_MODULUS - 1) as u8,
        burn_header_hash: BurnchainHeaderHash([0; 32]),
    };

    (BlockstackOperationType::LeaderBlockCommit(commit_op), block)
}

fn make_stacks_block(
    sort_db: &SortitionDB,
    state: &mut StacksChainState,
    burnchain: &Burnchain,
    parent_block: &BlockHeaderHash,
    parent_height: u64,
    miner: &StacksPrivateKey,
    my_burn: u64,
    vrf_key: &VRFPrivateKey,
    key_index: u32,
) -> (BlockstackOperationType, StacksBlock) {
    make_stacks_block_with_recipients(
        sort_db,
        state,
        burnchain,
        parent_block,
        parent_height,
        miner,
        my_burn,
        vrf_key,
        key_index,
        None,
    )
}

/// build a stacks block with just the coinbase off of
///  parent_block, in the canonical sortition fork of SortitionDB.
/// parent_block _must_ be included in the StacksChainState
fn make_stacks_block_with_recipients(
    sort_db: &SortitionDB,
    state: &mut StacksChainState,
    burnchain: &Burnchain,
    parent_block: &BlockHeaderHash,
    parent_height: u64,
    miner: &StacksPrivateKey,
    my_burn: u64,
    vrf_key: &VRFPrivateKey,
    key_index: u32,
    recipients: Option<&RewardSetInfo>,
) -> (BlockstackOperationType, StacksBlock) {
    make_stacks_block_with_recipients_and_sunset_burn(
        sort_db,
        state,
        burnchain,
        parent_block,
        parent_height,
        miner,
        my_burn,
        vrf_key,
        key_index,
        recipients,
        0,
        false,
    )
}

/// build a stacks block with just the coinbase off of
///  parent_block, in the canonical sortition fork of SortitionDB.
/// parent_block _must_ be included in the StacksChainState
fn make_stacks_block_with_recipients_and_sunset_burn(
    sort_db: &SortitionDB,
    state: &mut StacksChainState,
    burnchain: &Burnchain,
    parent_block: &BlockHeaderHash,
    parent_height: u64,
    miner: &StacksPrivateKey,
    my_burn: u64,
    vrf_key: &VRFPrivateKey,
    key_index: u32,
    recipients: Option<&RewardSetInfo>,
    sunset_burn: u64,
    post_sunset_burn: bool,
) -> (BlockstackOperationType, StacksBlock) {
    make_stacks_block_with_input(
        sort_db,
        state,
        burnchain,
        parent_block,
        parent_height,
        miner,
        my_burn,
        vrf_key,
        key_index,
        recipients,
        sunset_burn,
        post_sunset_burn,
        (Txid([0; 32]), 0),
    )
}

/// build a stacks block with just the coinbase off of
///  parent_block, in the canonical sortition fork of SortitionDB.
/// parent_block _must_ be included in the StacksChainState
fn make_stacks_block_with_input(
    sort_db: &SortitionDB,
    state: &mut StacksChainState,
    burnchain: &Burnchain,
    parent_block: &BlockHeaderHash,
    parent_height: u64,
    miner: &StacksPrivateKey,
    my_burn: u64,
    vrf_key: &VRFPrivateKey,
    key_index: u32,
    recipients: Option<&RewardSetInfo>,
    sunset_burn: u64,
    post_sunset_burn: bool,
    input: (Txid, u32),
) -> (BlockstackOperationType, StacksBlock) {
    let tx_auth = TransactionAuth::from_p2pkh(miner).unwrap();

    let mut tx = StacksTransaction::new(
        TransactionVersion::Testnet,
        tx_auth,
        TransactionPayload::Coinbase(CoinbasePayload([0u8; 32])),
    );
    tx.chain_id = 0x80000000;
    tx.anchor_mode = TransactionAnchorMode::OnChainOnly;
    let mut tx_signer = StacksTransactionSigner::new(&tx);
    tx_signer.sign_origin(miner).unwrap();

    let coinbase_op = tx_signer.get_tx().unwrap();

    let sortition_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    let parents_sortition = SortitionDB::get_block_snapshot_for_winning_stacks_block(
        &sort_db.index_conn(),
        &sortition_tip.sortition_id,
        parent_block,
    )
    .unwrap()
    .unwrap();

    let parent_vtxindex =
        SortitionDB::get_block_winning_vtxindex(sort_db.conn(), &parents_sortition.sortition_id)
            .unwrap()
            .unwrap();

    eprintln!(
        "Find parents stacks header: {} in sortition {}",
        &parent_block, &parents_sortition.sortition_id
    );
    let parent_stacks_header = StacksChainState::get_anchored_block_header_info(
        state.db(),
        &parents_sortition.consensus_hash,
        parent_block,
    )
    .unwrap()
    .unwrap();
    let proof = VRF::prove(vrf_key, sortition_tip.sortition_hash.as_bytes());

    let total_burn = parents_sortition.total_burn;

    let iconn = sort_db.index_conn();

    let mut builder = StacksBlockBuilder::make_regtest_block_builder(
        &parent_stacks_header,
        proof.clone(),
        total_burn,
        next_hash160(),
    )
    .unwrap();
    let mut epoch_tx = builder.epoch_begin(state, &iconn).unwrap();
    builder.try_mine_tx(&mut epoch_tx, &coinbase_op).unwrap();

    let block = builder.mine_anchored_block(&mut epoch_tx);
    builder.epoch_finish(epoch_tx);

    let commit_outs = if let Some(recipients) = recipients {
        let mut commit_outs = recipients
            .recipients
            .iter()
            .map(|(a, _)| a.clone())
            .collect::<Vec<StacksAddress>>();
        if commit_outs.len() == 1 {
            // Padding with burn address if required
            commit_outs.push(StacksAddress::burn_address(false))
        }
        commit_outs
    } else if post_sunset_burn || burnchain.is_in_prepare_phase(parent_height + 1) {
        test_debug!("block-commit in {} will burn", parent_height + 1);
        vec![StacksAddress::burn_address(false)]
    } else {
        vec![]
    };

    let commit_op = LeaderBlockCommitOp {
        sunset_burn,
        block_header_hash: block.block_hash(),
        burn_fee: my_burn,
        input,
        apparent_sender: BurnchainSigner {
            num_sigs: 1,
            hash_mode: address::AddressHashMode::SerializeP2PKH,
            public_keys: vec![StacksPublicKey::from_private(miner)],
        },
        key_block_ptr: 1, // all registers happen in block height 1
        key_vtxindex: (1 + key_index) as u16,
        memo: vec![],
        new_seed: VRFSeed::from_proof(&proof),
        commit_outs,

        parent_block_ptr: parents_sortition.block_height as u32,
        parent_vtxindex,

        txid: next_txid(),
        vtxindex: (1 + key_index) as u32,
        block_height: 0,
        burn_parent_modulus: (BURN_BLOCK_MINED_AT_MODULUS - 1) as u8,
        burn_header_hash: BurnchainHeaderHash([0; 32]),
    };

    (BlockstackOperationType::LeaderBlockCommit(commit_op), block)
}

#[test]
fn missed_block_commits() {
    let path = "/tmp/stacks-blockchain-missed_block_commits";
    let _r = std::fs::remove_dir_all(path);

    let sunset_ht = 8000;
    let pox_consts = Some(PoxConstants::new(5, 3, 3, 25, 5, 7010, sunset_ht));
    let burnchain_conf = get_burnchain(path, pox_consts.clone());

    let vrf_keys: Vec<_> = (0..50).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..50).map(|_| StacksPrivateKey::new()).collect();

    let stacker = p2pkh_from(&StacksPrivateKey::new());
    let rewards = p2pkh_from(&StacksPrivateKey::new());
    let balance = 6_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let stacked_amt = 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u128);
    let initial_balances = vec![(stacker.clone().into(), balance)];

    setup_states(
        &[path],
        &vrf_keys,
        &committers,
        pox_consts.clone(),
        Some(initial_balances),
    );

    let mut coord = make_coordinator(path, Some(burnchain_conf));

    coord.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, pox_consts.clone());

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];

    let mut last_input: Option<(Txid, u32)> = None;
    let b = get_burnchain(path, None);

    for ix in 0..vrf_keys.len() {
        let vrf_key = &vrf_keys[ix];
        let miner = &committers[ix];

        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let mut chainstate = get_chainstate(path);

        let parent = if ix == 0 {
            BlockHeaderHash([0; 32])
        } else {
            stacks_blocks[ix - 1].1.header.block_hash()
        };

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let next_mock_header = BurnchainBlockHeader {
            block_height: burnchain_tip.block_height + 1,
            block_hash: BurnchainHeaderHash([0; 32]),
            parent_block_hash: burnchain_tip.block_hash,
            num_txs: 0,
            timestamp: 1,
        };

        let reward_cycle_info = coord.get_reward_cycle_info(&next_mock_header).unwrap();
        let next_block_recipients = get_rw_sortdb(path, pox_consts.clone())
            .test_get_next_block_recipients(&b, reward_cycle_info.as_ref())
            .unwrap();

        let b = get_burnchain(path, pox_consts.clone());
        let mut ops = vec![];
        if ix % (MINING_COMMITMENT_WINDOW as usize) == 4 {
            let (mut bad_op, _) = make_stacks_block_with_input(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height - 2,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
                0,
                false,
                last_input.as_ref().unwrap().clone(),
            );
            // NOTE: intended for block block_height - 2
            last_input = Some((
                bad_op.txid(),
                if b.is_in_prepare_phase(next_mock_header.block_height - 2 + 1) {
                    2
                } else {
                    (OUTPUTS_PER_COMMIT as u32) + 1
                },
            ));
            bad_op.set_block_height(next_mock_header.block_height);
            if let BlockstackOperationType::LeaderBlockCommit(ref mut op) = bad_op {
                op.burn_parent_modulus =
                    ((next_mock_header.block_height - 2) % BURN_BLOCK_MINED_AT_MODULUS) as u8;
                op.vtxindex = 3;
            } else {
                panic!("Should be leader block commit");
            }
            test_debug!(
                "bad_op meant for block {}: {:?}",
                burnchain_tip.block_height - 2 + 1,
                &bad_op
            );
            ops.push(bad_op);
        }

        let (mut good_op, block) = if ix == 0 {
            make_genesis_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &parent,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        } else {
            make_stacks_block_with_input(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
                0,
                false,
                last_input.as_ref().unwrap().clone(),
            )
        };

        good_op.set_block_height(next_mock_header.block_height);

        let expected_winner = good_op.txid();
        ops.push(good_op);

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();

        if ix % (MINING_COMMITMENT_WINDOW as usize) == 3 {
            // produce an empty block!
            produce_burn_block(
                &mut burnchain,
                &burnchain_tip.block_hash,
                vec![],
                vec![].iter_mut(),
            );
        } else {
            // produce a block with one good op,
            last_input = Some((
                expected_winner,
                if b.is_in_prepare_phase(next_mock_header.block_height) {
                    2
                } else {
                    (OUTPUTS_PER_COMMIT as u32) + 1
                },
            ));
            produce_burn_block_do_not_set_height(
                &mut burnchain,
                &burnchain_tip.block_hash,
                ops,
                vec![].iter_mut(),
            );
        }
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let burn_distribution = get_burn_distribution(sort_db.conn(), &tip.sortition_id);
        eprintln!("{}", ix);
        if ix % (MINING_COMMITMENT_WINDOW as usize) == 3 {
            assert!(
                !tip.sortition,
                "Sortition should not have occurred because the only block commit was invalid"
            );
            // duplicate the last stacks_block
            stacks_blocks.push(stacks_blocks[ix - 1].clone());
        } else {
            // how many commit do we expect to see counted in the current window?
            let expected_window_commits = if ix >= (MINING_COMMITMENT_WINDOW as usize) {
                (MINING_COMMITMENT_WINDOW - 1) as usize
            } else {
                if ix >= 3 {
                    ix
                } else {
                    ix + 1
                }
            };
            // there were 2 burn blocks before we started mining
            let expected_window_size = cmp::min(MINING_COMMITMENT_WINDOW as usize, ix + 3);

            let min_burn = 1;
            let median_burn = if expected_window_commits > expected_window_size / 2 {
                10000
            } else if expected_window_size % 2 == 0
                && expected_window_commits == expected_window_size / 2
            {
                (10000 + 1) / 2
            } else {
                1
            };
            let last_burn = if ix % (MINING_COMMITMENT_WINDOW as usize) == 3 {
                0
            } else {
                10000
            };

            if b.is_in_prepare_phase(next_mock_header.block_height) {
                // in prepare phase -- no smoothing takes place
                assert_eq!(
                    burn_distribution[0].burns, last_burn,
                    "Burn distribution should not do windowing at ix = {} block_height = {}",
                    ix, next_mock_header.block_height
                )
            } else {
                // in reward phase -- apply min median
                assert_eq!(
                    burn_distribution[0].burns,
                    cmp::min(last_burn, median_burn),
                    "Burn distribution should match at ix = {} block_height = {}",
                    ix,
                    next_mock_header.block_height
                );
            }

            assert_eq!(&tip.winning_block_txid, &expected_winner);

            // load the block into staging
            let block_hash = block.header.block_hash();

            assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
            stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

            preprocess_block(&mut chainstate, &sort_db, &tip, block);

            // handle the stacks block
            coord.handle_new_stacks_block().unwrap();
        }
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    // 1 block of every $MINING_COMMITMENT_WINDOW is missed
    let missed_blocks = vrf_keys.len() / (MINING_COMMITMENT_WINDOW as usize);
    let expected_height = vrf_keys.len() - missed_blocks;
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        Value::UInt(expected_height as u128),
    );

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(),
                   "111111111111",
                   "PoX ID should reflect the 5 reward cycles _with_ a known anchor block, plus the 'initial' known reward cycle at genesis");
    }
}

#[test]
fn test_simple_setup() {
    let path = "/tmp/stacks-blockchain-simple-setup";
    // setup a second set of states that won't see the broadcasted blocks
    let path_blinded = "/tmp/stacks-blockchain-simple-setup.blinded";
    let _r = std::fs::remove_dir_all(path);
    let _r = std::fs::remove_dir_all(path_blinded);

    let vrf_keys: Vec<_> = (0..50).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..50).map(|_| StacksPrivateKey::new()).collect();

    setup_states(&[path, path_blinded], &vrf_keys, &committers, None, None);

    let mut coord = make_coordinator(path, None);
    let mut coord_blind = make_coordinator(path_blinded, None);

    coord.handle_new_burnchain_block().unwrap();
    coord_blind.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    let sort_db_blind = get_sortition_db(path_blinded, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db_blind
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    // at first, sortition_ids shouldn't have diverged
    //  but once the first reward cycle begins, they should diverge.
    let mut sortition_ids_diverged = false;
    let mut parent = BlockHeaderHash([0; 32]);
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks = vec![];
    let mut anchor_blocks = vec![];
    for (ix, (vrf_key, miner)) in vrf_keys.iter().zip(committers.iter()).enumerate() {
        let mut burnchain = get_burnchain_db(path, None);
        let mut chainstate = get_chainstate(path);
        let b = get_burnchain(path, None);
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let burnchain_blinded = get_burnchain_db(path_blinded, None);

        let (op, block) = if ix == 0 {
            make_genesis_block(
                &sort_db,
                &mut chainstate,
                &parent,
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        } else {
            make_stacks_block(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        };

        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            vec![op],
            [burnchain_blinded].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();
        coord_blind.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            // the "blinded" sortition db and the one that's processed all the blocks
            //   should have diverged in sortition_ids now...
            sortition_ids_diverged = true;
            // store the anchor block for this sortition for later checking
            let ic = sort_db.index_handle_at_tip();
            let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
            anchor_blocks.push(bhh);
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
        if sortition_ids_diverged {
            assert_ne!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should have diverged by block height = {}",
                blinded_tip.block_height
            );
        } else {
            assert_eq!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should not have diverged at block height = {}",
                blinded_tip.block_height
            );
        }

        // load the block into staging
        let block_hash = block.header.block_hash();

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();

        parent = block_hash;
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        Value::UInt(50)
    );

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(),
                   "111111111111",
                   "PoX ID should reflect the 10 reward cycles _with_ a known anchor block, plus the 'initial' known reward cycle at genesis");
    }

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(
            &pox_id.to_string(),
            "110000000000",
            "PoX ID should reflect the initial 'known' reward cycle at genesis"
        );
    }

    let mut pox_id_string = "1".to_string();
    // now let's start revealing stacks blocks to the blinded coordinator
    for (sortition_id, block) in stacks_blocks.iter() {
        reveal_block(
            path_blinded,
            &sort_db_blind,
            &mut coord_blind,
            sortition_id,
            block,
        );

        let pox_id_at_tip = {
            let ic = sort_db_blind.index_handle_at_tip();
            ic.get_pox_id().unwrap()
        };

        let block_hash = block.header.block_hash();
        if anchor_blocks.contains(&block_hash) {
            // just processed an anchor block, we should expect to have a pox_id
            //   that has one more one!
            pox_id_string.push('1');
        }

        println!("=> {}", pox_id_string);
        assert_eq!(
            pox_id_at_tip.to_string(),
            // right-pad pox_id_string to 11 characters
            format!("1{:0<11}", pox_id_string)
        );
    }
}

#[test]
fn test_sortition_with_reward_set() {
    let path = "/tmp/stacks-blockchain-simple-reward-set";
    let _r = std::fs::remove_dir_all(path);

    let mut vrf_keys: Vec<_> = (0..150).map(|_| VRFPrivateKey::new()).collect();
    let mut committers: Vec<_> = (0..150).map(|_| StacksPrivateKey::new()).collect();

    let reward_set_size = 4;
    let reward_set: Vec<_> = (0..reward_set_size)
        .map(|_| p2pkh_from(&StacksPrivateKey::new()))
        .collect();

    setup_states(&[path], &vrf_keys, &committers, None, None);

    let mut coord = make_reward_set_coordinator(path, reward_set, None);

    coord.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    let mut started_first_reward_cycle = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // split up the vrf keys and committers so that we have some that will be mining "correctly"
    //   and some that will be producing bad outputs

    let BURNER_OFFSET = 50;
    let mut vrf_key_burners = vrf_keys.split_off(50);
    let mut miner_burners = committers.split_off(50);

    let WRONG_OUTS_OFFSET = 100;
    let vrf_key_wrong_outs = vrf_key_burners.split_off(50);
    let miner_wrong_outs = miner_burners.split_off(50);

    let b = get_burnchain(path, None);

    // track the reward set consumption
    let mut reward_recipients = HashSet::new();
    for ix in 0..vrf_keys.len() {
        let vrf_key = &vrf_keys[ix];
        let miner = &committers[ix];

        let vrf_burner = &vrf_key_burners[ix];
        let miner_burner = &miner_burners[ix];

        let vrf_wrong_out = &vrf_key_wrong_outs[ix];
        let miner_wrong_out = &miner_wrong_outs[ix];

        let mut burnchain = get_burnchain_db(path, None);
        let mut chainstate = get_chainstate(path);

        let parent = if ix == 0 {
            BlockHeaderHash([0; 32])
        } else if ix == 49 {
            // lets mine off a block that _isn't_ a descendant of our PoX anchor
            stacks_blocks[1].1.header.block_hash()
        } else {
            stacks_blocks[ix - 1].1.header.block_hash()
        };

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let next_mock_header = BurnchainBlockHeader {
            block_height: burnchain_tip.block_height + 1,
            block_hash: BurnchainHeaderHash([0; 32]),
            parent_block_hash: burnchain_tip.block_hash,
            num_txs: 0,
            timestamp: 1,
        };

        let reward_cycle_info = coord.get_reward_cycle_info(&next_mock_header).unwrap();
        if reward_cycle_info.is_some() {
            // did we process a reward set last cycle? check if the
            //  recipient set size matches our expectation
            if started_first_reward_cycle {
                assert_eq!(reward_recipients.len(), reward_set_size);
            }
            // clear the reward recipients tracker, since those
            //  recipients are now eligible again in the new reward cycle
            reward_recipients.clear();
        }
        let next_block_recipients = get_rw_sortdb(path, None)
            .test_get_next_block_recipients(&b, reward_cycle_info.as_ref())
            .unwrap();
        if let Some(ref next_block_recipients) = next_block_recipients {
            for (addr, _) in next_block_recipients.recipients.iter() {
                assert!(
                    !reward_recipients.contains(addr),
                    "Reward set should not already contain address {}",
                    addr
                );
                eprintln!("At iteration: {}, inserting address ... {}", ix, addr);
                reward_recipients.insert(addr.clone());
            }
        }

        let b = get_burnchain(path, None);
        let (good_op, mut block) = if ix == 0 {
            make_genesis_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &parent,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        } else {
            make_stacks_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        };

        let mut expected_winner = good_op.txid();
        let mut ops = vec![good_op];

        if started_first_reward_cycle {
            // make the bad commitments
            // only create bad "burn" commitments if we know they'll be rejected:
            //   (a) we're in a reward cycle _and_ (b) there are expected recipients
            if next_block_recipients.is_some() {
                let (all_burn_op, all_burn_block) = make_stacks_block_with_recipients(
                    &sort_db,
                    &mut chainstate,
                    &b,
                    &parent,
                    burnchain_tip.block_height,
                    miner_burner,
                    10000,
                    vrf_burner,
                    (ix + BURNER_OFFSET) as u32,
                    None,
                );
                if ix == 49 {
                    // at this ix, _all_burn_block_ should be the winner
                    //   because "parent" isn't a descendant of the PoX anchor
                    expected_winner = all_burn_op.txid();
                    block = all_burn_block;
                }
                ops.push(all_burn_op);
            }

            // sometime have the wrong _number_ of recipients,
            //   other times just have the wrong set of recipients
            let recipients = if ix % 2 == 0 {
                vec![(p2pkh_from(miner_wrong_out), 0)]
            } else {
                (0..OUTPUTS_PER_COMMIT)
                    .map(|ix| (p2pkh_from(&StacksPrivateKey::new()), ix as u16))
                    .collect()
            };
            let bad_block_recipients = Some(RewardSetInfo {
                anchor_block: BlockHeaderHash([0; 32]),
                recipients,
            });
            let (bad_outs_op, _) = make_stacks_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner_wrong_out,
                10000,
                vrf_burner,
                (ix + WRONG_OUTS_OFFSET) as u32,
                bad_block_recipients.as_ref(),
            );
            ops.push(bad_outs_op);
        }

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            ops,
            vec![].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            started_first_reward_cycle = true;
            // store the anchor block for this sortition for later checking
            let ic = sort_db.index_handle_at_tip();
            let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
            anchor_blocks.push(bhh);
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        assert_eq!(&tip.winning_block_txid, &expected_winner);

        // load the block into staging
        let block_hash = block.header.block_hash();

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        // we only got to block height 49, because of the little fork at the end.
        Value::UInt(49)
    );

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(),
                   "111111111111",
                   "PoX ID should reflect the 10 reward cycles _with_ a known anchor block, plus the 'initial' known reward cycle at genesis");
    }
}

#[test]
fn test_sortition_with_burner_reward_set() {
    let path = "/tmp/stacks-blockchain-burner-reward-set";
    let _r = std::fs::remove_dir_all(path);

    let mut vrf_keys: Vec<_> = (0..150).map(|_| VRFPrivateKey::new()).collect();
    let mut committers: Vec<_> = (0..150).map(|_| StacksPrivateKey::new()).collect();

    let reward_set_size = 3;
    let mut reward_set: Vec<_> = (0..reward_set_size - 1)
        .map(|_| StacksAddress::burn_address(false))
        .collect();
    reward_set.push(p2pkh_from(&StacksPrivateKey::new()));

    setup_states(&[path], &vrf_keys, &committers, None, None);

    let mut coord = make_reward_set_coordinator(path, reward_set, None);

    coord.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    let mut started_first_reward_cycle = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // split up the vrf keys and committers so that we have some that will be mining "correctly"
    //   and some that will be producing bad outputs

    let BURNER_OFFSET = 50;
    let mut vrf_key_burners = vrf_keys.split_off(50);
    let mut miner_burners = committers.split_off(50);

    let WRONG_OUTS_OFFSET = 100;
    let vrf_key_wrong_outs = vrf_key_burners.split_off(50);
    let miner_wrong_outs = miner_burners.split_off(50);

    let b = get_burnchain(path, None);

    // track the reward set consumption
    let mut reward_recipients = HashSet::new();
    for ix in 0..vrf_keys.len() {
        let vrf_key = &vrf_keys[ix];
        let miner = &committers[ix];

        let vrf_burner = &vrf_key_burners[ix];
        let miner_burner = &miner_burners[ix];

        let vrf_wrong_out = &vrf_key_wrong_outs[ix];
        let miner_wrong_out = &miner_wrong_outs[ix];

        let mut burnchain = get_burnchain_db(path, None);
        let mut chainstate = get_chainstate(path);

        let parent = if ix == 0 {
            BlockHeaderHash([0; 32])
        } else {
            stacks_blocks[ix - 1].1.header.block_hash()
        };

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let next_mock_header = BurnchainBlockHeader {
            block_height: burnchain_tip.block_height + 1,
            block_hash: BurnchainHeaderHash([0; 32]),
            parent_block_hash: burnchain_tip.block_hash,
            num_txs: 0,
            timestamp: 1,
        };

        let reward_cycle_info = coord.get_reward_cycle_info(&next_mock_header).unwrap();
        if reward_cycle_info.is_some() {
            // did we process a reward set last cycle? check if the
            //  recipient set size matches our expectation
            if started_first_reward_cycle {
                assert_eq!(reward_recipients.len(), 2);
            }
            // clear the reward recipients tracker, since those
            //  recipients are now eligible again in the new reward cycle
            reward_recipients.clear();
        }
        let next_block_recipients = get_rw_sortdb(path, None)
            .test_get_next_block_recipients(&b, reward_cycle_info.as_ref())
            .unwrap();
        if let Some(ref next_block_recipients) = next_block_recipients {
            for (addr, _) in next_block_recipients.recipients.iter() {
                if !addr.is_burn() {
                    assert!(
                        !reward_recipients.contains(addr),
                        "Reward set should not already contain address {}",
                        addr
                    );
                }
                eprintln!("At iteration: {}, inserting address ... {}", ix, addr);
                reward_recipients.insert(addr.clone());
            }
        }

        let b = get_burnchain(path, None);
        let (good_op, block) = if ix == 0 {
            make_genesis_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &parent,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        } else {
            make_stacks_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        };

        let expected_winner = good_op.txid();
        let mut ops = vec![good_op];

        if started_first_reward_cycle {
            // sometime have the wrong _number_ of recipients,
            //   other times just have the wrong set of recipients
            let recipients = if ix % 2 == 0 {
                vec![(p2pkh_from(miner_wrong_out), 0)]
            } else {
                (0..OUTPUTS_PER_COMMIT)
                    .map(|ix| (p2pkh_from(&StacksPrivateKey::new()), ix as u16))
                    .collect()
            };
            let bad_block_recipients = Some(RewardSetInfo {
                anchor_block: BlockHeaderHash([0; 32]),
                recipients,
            });
            let (bad_outs_op, _) = make_stacks_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner_wrong_out,
                10000,
                vrf_burner,
                (ix + WRONG_OUTS_OFFSET) as u32,
                bad_block_recipients.as_ref(),
            );
            ops.push(bad_outs_op);
        }

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            ops,
            vec![].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            started_first_reward_cycle = true;
            // store the anchor block for this sortition for later checking
            let ic = sort_db.index_handle_at_tip();
            let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
            anchor_blocks.push(bhh);
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        assert_eq!(&tip.winning_block_txid, &expected_winner);

        // load the block into staging
        let block_hash = block.header.block_hash();

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        Value::UInt(50)
    );

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(),
                   "111111111111",
                   "PoX ID should reflect the 10 reward cycles _with_ a known anchor block, plus the 'initial' known reward cycle at genesis");
    }
}

#[test]
fn test_pox_btc_ops() {
    let path = "/tmp/stacks-blockchain-pox-btc-ops";
    let _r = std::fs::remove_dir_all(path);

    let sunset_ht = 8000;
    let pox_consts = Some(PoxConstants::new(5, 3, 3, 25, 5, 7010, sunset_ht));
    let burnchain_conf = get_burnchain(path, pox_consts.clone());

    let vrf_keys: Vec<_> = (0..50).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..50).map(|_| StacksPrivateKey::new()).collect();

    let stacker = p2pkh_from(&StacksPrivateKey::new());
    let rewards = p2pkh_from(&StacksPrivateKey::new());
    let balance = 6_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let stacked_amt = 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u128);
    let initial_balances = vec![(stacker.clone().into(), balance)];

    setup_states(
        &[path],
        &vrf_keys,
        &committers,
        pox_consts.clone(),
        Some(initial_balances),
    );

    let mut coord = make_coordinator(path, Some(burnchain_conf.clone()));

    coord.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, pox_consts.clone());

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    let mut started_first_reward_cycle = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // track the reward set consumption
    let mut reward_cycle_count = 0;
    let mut reward_recipients = HashSet::new();
    for ix in 0..vrf_keys.len() {
        let vrf_key = &vrf_keys[ix];
        let miner = &committers[ix];

        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let mut chainstate = get_chainstate(path);

        let parent = if ix == 0 {
            BlockHeaderHash([0; 32])
        } else {
            stacks_blocks[ix - 1].1.header.block_hash()
        };

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let next_mock_header = BurnchainBlockHeader {
            block_height: burnchain_tip.block_height + 1,
            block_hash: BurnchainHeaderHash([0; 32]),
            parent_block_hash: burnchain_tip.block_hash,
            num_txs: 0,
            timestamp: 1,
        };

        let reward_cycle_info = coord.get_reward_cycle_info(&next_mock_header).unwrap();
        if reward_cycle_info.is_some() {
            // did we process a reward set last cycle? check if the
            //  recipient set size matches our expectation
            reward_cycle_count += 1;
            if reward_cycle_count > 2 && reward_cycle_count < 6 {
                assert_eq!(reward_recipients.len(), 1);
            }
            // clear the reward recipients tracker, since those
            //  recipients are now eligible again in the new reward cycle
            reward_recipients.clear();
        }
        let next_block_recipients = get_rw_sortdb(path, pox_consts.clone())
            .test_get_next_block_recipients(&burnchain_conf, reward_cycle_info.as_ref())
            .unwrap();
        if next_mock_header.block_height >= sunset_ht {
            assert!(next_block_recipients.is_none());
        }

        if let Some(ref next_block_recipients) = next_block_recipients {
            for (addr, _) in next_block_recipients.recipients.iter() {
                eprintln!("At iteration: {}, inserting address ... {}", ix, addr);
                reward_recipients.insert(addr.clone());
            }
        }

        let b = get_burnchain(path, None);

        let (good_op, block) = if ix == 0 {
            make_genesis_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &parent,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        } else {
            make_stacks_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                1000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        };

        let expected_winner = good_op.txid();
        let mut ops = vec![good_op];

        if ix == 0 {
            // add a pre-stack-stx op
            ops.push(BlockstackOperationType::PreStx(PreStxOp {
                output: stacker.clone(),
                txid: next_txid(),
                vtxindex: 5,
                block_height: 0,
                burn_header_hash: BurnchainHeaderHash([0; 32]),
            }));
        } else if ix == 1 {
            ops.push(BlockstackOperationType::StackStx(StackStxOp {
                sender: stacker.clone(),
                reward_addr: rewards.clone(),
                stacked_ustx: stacked_amt,
                num_cycles: 4,
                txid: next_txid(),
                vtxindex: 5,
                block_height: 0,
                burn_header_hash: BurnchainHeaderHash([0; 32]),
            }));
        }

        // check our locked balance
        if ix > 0 {
            let stacks_tip =
                SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
            let mut chainstate = get_chainstate(path);
            let (stacker_balance, burn_height) = chainstate
                .with_read_only_clarity_tx(
                    &sort_db.index_conn(),
                    &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                    |conn| {
                        conn.with_clarity_db_readonly(|db| {
                            (
                                db.get_account_stx_balance(&stacker.clone().into()),
                                db.get_current_block_height(),
                            )
                        })
                    },
                )
                .unwrap();

            if ix > 2 && reward_cycle_count < 6 {
                assert_eq!(
                    stacker_balance.amount_unlocked,
                    (balance as u128) - stacked_amt,
                    "Lock should be active"
                );
                assert_eq!(stacker_balance.amount_locked, stacked_amt);
            } else {
                assert_eq!(
                    stacker_balance.get_available_balance_at_burn_block(burn_height as u64),
                    balance as u128,
                    "No lock should be active"
                );
            }
        }

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            ops,
            vec![].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            if new_burnchain_tip.block_height < sunset_ht {
                started_first_reward_cycle = true;
                // store the anchor block for this sortition for later checking
                let ic = sort_db.index_handle_at_tip();
                let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
                anchor_blocks.push(bhh);
            } else {
                // store the anchor block for this sortition for later checking
                let ic = sort_db.index_handle_at_tip();
                assert!(
                    ic.get_last_anchor_block_hash().unwrap().is_none(),
                    "No PoX anchor block should be chosen after PoX sunset"
                );
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        assert_eq!(&tip.winning_block_txid, &expected_winner);

        // load the block into staging
        let block_hash = block.header.block_hash();

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        Value::UInt(50)
    );

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(),
                   "111111111111",
                   "PoX ID should reflect the 5 reward cycles _with_ a known anchor block, plus the 'initial' known reward cycle at genesis");
    }
}

#[test]
fn test_stx_transfer_btc_ops() {
    let path = "/tmp/stacks-blockchain-stx_transfer-btc-ops";
    let _r = std::fs::remove_dir_all(path);

    let sunset_ht = 8000;
    let pox_consts = Some(PoxConstants::new(5, 3, 3, 25, 5, 7010, sunset_ht));
    let burnchain_conf = get_burnchain(path, pox_consts.clone());

    let vrf_keys: Vec<_> = (0..50).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..50).map(|_| StacksPrivateKey::new()).collect();

    let stacker = p2pkh_from(&StacksPrivateKey::new());
    let recipient = p2pkh_from(&StacksPrivateKey::new());
    let balance = 6_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let transfer_amt = 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u128);
    let initial_balances = vec![(stacker.clone().into(), balance)];

    setup_states(
        &[path],
        &vrf_keys,
        &committers,
        pox_consts.clone(),
        Some(initial_balances),
    );

    let mut coord = make_coordinator(path, Some(burnchain_conf.clone()));

    coord.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, pox_consts.clone());

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    let mut started_first_reward_cycle = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // track the reward set consumption
    let mut reward_recipients = HashSet::new();
    for ix in 0..vrf_keys.len() {
        let vrf_key = &vrf_keys[ix];
        let miner = &committers[ix];

        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let mut chainstate = get_chainstate(path);

        let parent = if ix == 0 {
            BlockHeaderHash([0; 32])
        } else {
            stacks_blocks[ix - 1].1.header.block_hash()
        };

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let next_mock_header = BurnchainBlockHeader {
            block_height: burnchain_tip.block_height + 1,
            block_hash: BurnchainHeaderHash([0; 32]),
            parent_block_hash: burnchain_tip.block_hash,
            num_txs: 0,
            timestamp: 1,
        };

        let reward_cycle_info = coord.get_reward_cycle_info(&next_mock_header).unwrap();
        if reward_cycle_info.is_some() {
            // did we process a reward set last cycle? check if the
            //  recipient set size matches our expectation
            assert_eq!(reward_recipients.len(), 0);
            // clear the reward recipients tracker, since those
            //  recipients are now eligible again in the new reward cycle
            reward_recipients.clear();
        }
        let next_block_recipients = get_rw_sortdb(path, pox_consts.clone())
            .test_get_next_block_recipients(&burnchain_conf, reward_cycle_info.as_ref())
            .unwrap();
        if next_mock_header.block_height >= sunset_ht {
            assert!(next_block_recipients.is_none());
        }

        if let Some(ref next_block_recipients) = next_block_recipients {
            for (addr, _) in next_block_recipients.recipients.iter() {
                eprintln!("At iteration: {}, inserting address ... {}", ix, addr);
                reward_recipients.insert(addr.clone());
            }
        }

        let b = get_burnchain(path, pox_consts.clone());
        let (good_op, block) = if ix == 0 {
            make_genesis_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &parent,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        } else {
            make_stacks_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                1000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        };

        let expected_winner = good_op.txid();
        let mut ops = vec![good_op];

        if ix == 0 {
            // add a pre-stack-stx op
            ops.push(BlockstackOperationType::PreStx(PreStxOp {
                output: stacker.clone(),
                txid: next_txid(),
                vtxindex: 5,
                block_height: 0,
                burn_header_hash: BurnchainHeaderHash([0; 32]),
            }));
            ops.push(BlockstackOperationType::PreStx(PreStxOp {
                output: recipient.clone(),
                txid: next_txid(),
                vtxindex: 6,
                block_height: 0,
                burn_header_hash: BurnchainHeaderHash([0; 32]),
            }));
        } else if ix == 1 {
            ops.push(BlockstackOperationType::TransferStx(TransferStxOp {
                sender: stacker.clone(),
                recipient: recipient.clone(),
                transfered_ustx: transfer_amt,
                memo: vec![],
                txid: next_txid(),
                vtxindex: 5,
                block_height: 0,
                burn_header_hash: BurnchainHeaderHash([0; 32]),
            }));
        } else if ix == 2 {
            // shouldn't be accepted -- transfer amount is too large
            ops.push(BlockstackOperationType::TransferStx(TransferStxOp {
                sender: recipient.clone(),
                recipient: stacker.clone(),
                transfered_ustx: transfer_amt + 1,
                memo: vec![],
                txid: next_txid(),
                vtxindex: 5,
                block_height: 0,
                burn_header_hash: BurnchainHeaderHash([0; 32]),
            }));
        }

        // check our locked balance
        if ix > 0 {
            let stacks_tip =
                SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
            let mut chainstate = get_chainstate(path);
            let (sender_balance, burn_height) = chainstate
                .with_read_only_clarity_tx(
                    &sort_db.index_conn(),
                    &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                    |conn| {
                        conn.with_clarity_db_readonly(|db| {
                            (
                                db.get_account_stx_balance(&stacker.clone().into()),
                                db.get_current_block_height(),
                            )
                        })
                    },
                )
                .unwrap();

            let (recipient_balance, burn_height) = chainstate
                .with_read_only_clarity_tx(
                    &sort_db.index_conn(),
                    &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                    |conn| {
                        conn.with_clarity_db_readonly(|db| {
                            (
                                db.get_account_stx_balance(&recipient.clone().into()),
                                db.get_current_block_height(),
                            )
                        })
                    },
                )
                .unwrap();

            if ix > 2 {
                assert_eq!(
                    sender_balance.get_available_balance_at_burn_block(burn_height as u64),
                    (balance as u128) - transfer_amt,
                    "Transfer should have decremented balance"
                );
                assert_eq!(
                    recipient_balance.get_available_balance_at_burn_block(burn_height as u64),
                    transfer_amt,
                    "Recipient should have incremented balance"
                );
            } else {
                assert_eq!(
                    sender_balance.get_available_balance_at_burn_block(burn_height as u64),
                    balance as u128,
                );
                assert_eq!(
                    recipient_balance.get_available_balance_at_burn_block(burn_height as u64),
                    0,
                );
            }
        }

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            ops,
            vec![].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            if new_burnchain_tip.block_height < sunset_ht {
                started_first_reward_cycle = true;
                // store the anchor block for this sortition for later checking
                let ic = sort_db.index_handle_at_tip();
                let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
                anchor_blocks.push(bhh);
            } else {
                // store the anchor block for this sortition for later checking
                let ic = sort_db.index_handle_at_tip();
                assert!(
                    ic.get_last_anchor_block_hash().unwrap().is_none(),
                    "No PoX anchor block should be chosen after PoX sunset"
                );
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        assert_eq!(&tip.winning_block_txid, &expected_winner);

        // load the block into staging
        let block_hash = block.header.block_hash();

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        Value::UInt(50)
    );

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(),
                   "111111111111",
                   "PoX ID should reflect the 5 reward cycles _with_ a known anchor block, plus the 'initial' known reward cycle at genesis");
    }
}

#[test]
fn test_initial_coinbase_reward_distributions() {
    let path = "/tmp/initial_coinbase_reward_distributions";
    let _r = std::fs::remove_dir_all(path);

    let sunset_ht = 8000;
    let pox_consts = Some(PoxConstants::new(5, 3, 3, 25, 5, 7010, sunset_ht));
    let burnchain_conf = get_burnchain(path, pox_consts.clone());

    let vrf_keys: Vec<_> = (0..50).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..50).map(|_| StacksPrivateKey::new()).collect();

    let stacker = p2pkh_from(&StacksPrivateKey::new());
    let rewards = p2pkh_from(&StacksPrivateKey::new());
    let balance = 6_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let stacked_amt = 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u128);
    let initial_balances = vec![(stacker.clone().into(), balance)];

    setup_states(
        &[path],
        &vrf_keys,
        &committers,
        pox_consts.clone(),
        Some(initial_balances),
    );

    let mut coord = make_coordinator(path, Some(burnchain_conf));

    coord.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, pox_consts.clone());

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];

    // produce some burn blocks without sortitions:
    for _ix in 0..50 {
        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            vec![],
            vec![].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();
    }
    let initial_missed_blocks = {
        let burnchain = get_burnchain_db(path, pox_consts.clone());
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        // +1 here, because the # of missed blocks is (first_sortition_height - first_burn_block_height)
        burnchain_tip.block_height + 1
    };

    let initial_block_bonus = (initial_missed_blocks as u128 * MICROSTACKS_PER_STACKS as u128)
        * 1_000
        / (INITIAL_MINING_BONUS_WINDOW as u128);

    // now we'll mine 20 burn blocks, every other one with a sortition.
    //   we should get:
    //   block  0: initial_block_bonus + 1_000STX
    //   block  1: no sortition
    //   block  2: 2*(initial_block_bonus + 1_000)
    //   ...
    //   block  8: 2*(initial_block_bonus + 1_000)
    //   block  9: no sortition
    //   block 10: 1_000 + (initial_block_bonus + 1_000)
    //   block 11: no sortition
    //   block 12: 2_000
    //   block 13: no sortition
    //   block 14: 2_000

    for ix in 0..20 {
        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        eprintln!("BURNCHAIN TIP HEIGHT = {}", burnchain_tip.block_height);
        if ix % 2 == 1 {
            produce_burn_block(
                &mut burnchain,
                &burnchain_tip.block_hash,
                vec![],
                vec![].iter_mut(),
            );
            coord.handle_new_burnchain_block().unwrap();
        } else {
            let vrf_key = &vrf_keys[ix];
            let miner = &committers[ix];

            let mut chainstate = get_chainstate(path);

            let parent = if ix == 0 {
                BlockHeaderHash([0; 32])
            } else {
                stacks_blocks[ix / 2 - 1].1.header.block_hash()
            };

            let b = get_burnchain(path, pox_consts.clone());
            let (good_op, block) = if ix == 0 {
                make_genesis_block_with_recipients(
                    &sort_db,
                    &mut chainstate,
                    &parent,
                    miner,
                    10000,
                    vrf_key,
                    ix as u32,
                    None,
                )
            } else {
                make_stacks_block_with_recipients(
                    &sort_db,
                    &mut chainstate,
                    &b,
                    &parent,
                    burnchain_tip.block_height,
                    miner,
                    1000,
                    vrf_key,
                    ix as u32,
                    None,
                )
            };
            let expected_winner = good_op.txid();
            let ops = vec![good_op];

            let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
            produce_burn_block(
                &mut burnchain,
                &burnchain_tip.block_hash,
                ops,
                vec![].iter_mut(),
            );
            // handle the sortition
            coord.handle_new_burnchain_block().unwrap();

            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            assert_eq!(&tip.winning_block_txid, &expected_winner);

            // load the block into staging
            let block_hash = block.header.block_hash();

            assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
            stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

            preprocess_block(&mut chainstate, &sort_db, &tip, block);

            // handle the stacks block
            coord.handle_new_stacks_block().unwrap();
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();

        let base_coinbase = 1_000 * MICROSTACKS_PER_STACKS as u128;
        eprintln!(
            "At index = {}, total: {}",
            ix,
            tip.accumulated_coinbase_ustx + base_coinbase
        );

        if ix % 2 == 1 {
            assert!(!tip.sortition, "Odd indexes should not produce sortitions");
        } else if ix == 0 {
            assert_eq!(
                tip.accumulated_coinbase_ustx + base_coinbase,
                initial_block_bonus + base_coinbase
            );
        } else if ix < 10 {
            assert_eq!(
                tip.accumulated_coinbase_ustx + base_coinbase,
                2 * (initial_block_bonus + base_coinbase)
            );
        } else if ix == 10 {
            assert_eq!(
                tip.accumulated_coinbase_ustx + base_coinbase,
                initial_block_bonus + (2 * base_coinbase)
            );
        } else {
            assert_eq!(
                tip.accumulated_coinbase_ustx + base_coinbase,
                2 * base_coinbase
            );
        }
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        Value::UInt(10)
    );
}

#[test]
fn test_sortition_with_sunset() {
    let path = "/tmp/stacks-blockchain-sortition-with-sunset";
    let _r = std::fs::remove_dir_all(path);

    let sunset_ht = 80;
    let pox_consts = Some(PoxConstants::new(6, 3, 3, 25, 5, 10, sunset_ht));
    let burnchain_conf = get_burnchain(path, pox_consts.clone());

    let mut vrf_keys: Vec<_> = (0..200).map(|_| VRFPrivateKey::new()).collect();
    let mut committers: Vec<_> = (0..200).map(|_| StacksPrivateKey::new()).collect();

    let reward_set_size = pox_consts.as_ref().unwrap().reward_slots() as usize;
    assert_eq!(reward_set_size, 6);
    let reward_set: Vec<_> = (0..reward_set_size)
        .map(|_| p2pkh_from(&StacksPrivateKey::new()))
        .collect();

    setup_states(&[path], &vrf_keys, &committers, pox_consts.clone(), None);

    let mut coord = make_reward_set_coordinator(path, reward_set, pox_consts.clone());

    coord.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, pox_consts.clone());

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    let mut started_first_reward_cycle = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // split up the vrf keys and committers so that we have some that will be mining "correctly"
    //   and some that will be producing bad outputs

    let WRONG_OUTS_OFFSET = 100;
    let vrf_key_wrong_outs = vrf_keys.split_off(WRONG_OUTS_OFFSET);
    let miner_wrong_outs = committers.split_off(WRONG_OUTS_OFFSET);

    // track the reward set consumption
    let mut reward_recipients = HashSet::new();
    for ix in 0..vrf_keys.len() {
        let vrf_key = &vrf_keys[ix];
        let miner = &committers[ix];

        let vrf_wrong_out = &vrf_key_wrong_outs[ix];
        let miner_wrong_out = &miner_wrong_outs[ix];

        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let mut chainstate = get_chainstate(path);

        let parent = if ix == 0 {
            BlockHeaderHash([0; 32])
        } else {
            stacks_blocks[ix - 1].1.header.block_hash()
        };

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let next_mock_header = BurnchainBlockHeader {
            block_height: burnchain_tip.block_height + 1,
            block_hash: BurnchainHeaderHash([0; 32]),
            parent_block_hash: burnchain_tip.block_hash,
            num_txs: 0,
            timestamp: 1,
        };

        let reward_cycle_info = coord.get_reward_cycle_info(&next_mock_header).unwrap();
        if reward_cycle_info.is_some() {
            // did we process a reward set last cycle? check if the
            //  recipient set size matches our expectation
            if started_first_reward_cycle {
                let last_reward_cycle_block = (sunset_ht
                    / (pox_consts.as_ref().unwrap().reward_cycle_length as u64))
                    * (pox_consts.as_ref().unwrap().reward_cycle_length as u64);
                if burnchain_tip.block_height == last_reward_cycle_block {
                    eprintln!(
                        "End of PoX (at sunset height {}): reward set size is {}",
                        burnchain_tip.block_height,
                        reward_recipients.len()
                    );
                    assert_eq!(reward_recipients.len(), 6); // still hasn't cleared yet, so still 6
                } else if burnchain_tip.block_height
                    > last_reward_cycle_block
                        + (pox_consts.as_ref().unwrap().reward_cycle_length as u64)
                {
                    eprintln!("End of PoX (beyond sunset height {} and in next reward cycle): reward set size is {}", burnchain_tip.block_height, reward_recipients.len());
                    assert_eq!(reward_recipients.len(), 0);
                } else if burnchain_tip.block_height > last_reward_cycle_block {
                    eprintln!(
                        "End of PoX (beyond sunset height {}): reward set size is {}",
                        burnchain_tip.block_height,
                        reward_recipients.len()
                    );
                    assert_eq!(reward_recipients.len(), 2); // still haven't cleared this yet, so still 2
                } else {
                    eprintln!(
                        "End of PoX (before sunset height {}): reward set size is {}",
                        burnchain_tip.block_height,
                        reward_recipients.len()
                    );
                    assert_eq!(reward_recipients.len(), reward_set_size);
                }
            }
            // clear the reward recipients tracker, since those
            //  recipients are now eligible again in the new reward cycle
            reward_recipients.clear();
        }
        let next_block_recipients = get_rw_sortdb(path, pox_consts.clone())
            .test_get_next_block_recipients(&burnchain_conf, reward_cycle_info.as_ref())
            .unwrap();
        if next_mock_header.block_height >= sunset_ht {
            assert!(next_block_recipients.is_none());
        }

        if let Some(ref next_block_recipients) = next_block_recipients {
            // this is only Some(..) if we're pre-sunset
            assert!(burnchain_tip.block_height <= sunset_ht);
            for (addr, _) in next_block_recipients.recipients.iter() {
                if !addr.is_burn() {
                    assert!(
                        !reward_recipients.contains(addr),
                        "Reward set should not already contain address {}",
                        addr
                    );
                }
                reward_recipients.insert(addr.clone());
            }
            eprintln!(
                "at {}: reward_recipients ({}) = {:?}",
                burnchain_tip.block_height,
                reward_recipients.len(),
                reward_recipients
            );
        }

        let sunset_burn = burnchain_conf.expected_sunset_burn(next_mock_header.block_height, 10000);
        let rest_commit = 10000 - sunset_burn;
        let b = get_burnchain(path, pox_consts.clone());

        let (good_op, block) = if ix == 0 {
            make_genesis_block_with_recipients(
                &sort_db,
                &mut chainstate,
                &parent,
                miner,
                10000,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
            )
        } else {
            make_stacks_block_with_recipients_and_sunset_burn(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                rest_commit,
                vrf_key,
                ix as u32,
                next_block_recipients.as_ref(),
                sunset_burn + (rand::random::<u8>() as u64),
                next_mock_header.block_height >= sunset_ht,
            )
        };

        eprintln!("good op: {:?}", &good_op);
        let expected_winner = good_op.txid();
        let mut ops = vec![good_op];

        if sunset_burn > 0 {
            let (bad_outs_op, _) = make_stacks_block_with_recipients_and_sunset_burn(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_wrong_out,
                (ix + WRONG_OUTS_OFFSET) as u32,
                next_block_recipients.as_ref(),
                sunset_burn - 1,
                false,
            );
            ops.push(bad_outs_op);
        }

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            ops,
            vec![].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            if new_burnchain_tip.block_height < sunset_ht {
                started_first_reward_cycle = true;
                // store the anchor block for this sortition for later checking
                let ic = sort_db.index_handle_at_tip();
                let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
                anchor_blocks.push(bhh);
            } else {
                // store the anchor block for this sortition for later checking
                let ic = sort_db.index_handle_at_tip();
                assert!(
                    ic.get_last_anchor_block_hash().unwrap().is_none(),
                    "No PoX anchor block should be chosen after PoX sunset"
                );
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        assert_eq!(&tip.winning_block_txid, &expected_winner);

        // load the block into staging
        let block_hash = block.header.block_hash();

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(path);
    assert_eq!(
        chainstate
            .with_read_only_clarity_tx(
                &sort_db.index_conn(),
                &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
                |conn| conn
                    .with_readonly_clarity_env(
                        false,
                        PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                        LimitedCostTracker::new_free(),
                        |env| env.eval_raw("block-height")
                    )
                    .unwrap()
            )
            .unwrap(),
        Value::UInt(100)
    );

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(),
                   "111111111111111111",
                   "PoX ID should reflect the 10 reward cycles _with_ a known anchor block, plus the 'initial' known reward cycle at genesis");
    }
}

#[test]
// This test should panic until the MARF stability issue
// https://github.com/blockstack/stacks-blockchain/issues/1805
// is resolved:
#[should_panic]
/// Test a block that is processable in 2 PoX forks:
///   block "11" should be processable in both `111` and `110`
///   (because its parent is block `0`, and nobody stacks in
///    this test, all block commits must burn)
fn test_pox_processable_block_in_different_pox_forks() {
    let path = "/tmp/stacks-blockchain.test.pox_processable_block_in_different_pox_forks";
    // setup a second set of states that won't see the broadcasted blocks
    let path_blinded =
        "/tmp/stacks-blockchain.test.pox_processable_block_in_different_pox_forks.blinded";
    let _r = std::fs::remove_dir_all(path);
    let _r = std::fs::remove_dir_all(path_blinded);

    let vrf_keys: Vec<_> = (0..12).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..12).map(|_| StacksPrivateKey::new()).collect();

    setup_states(&[path, path_blinded], &vrf_keys, &committers, None, None);

    let mut coord = make_coordinator(path, None);
    let mut coord_blind = make_coordinator(path_blinded, None);

    coord.handle_new_burnchain_block().unwrap();
    coord_blind.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    let sort_db_blind = get_sortition_db(path_blinded, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db_blind
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    // at first, sortition_ids shouldn't have diverged
    //  but once the first reward cycle begins, they should diverge.
    let mut sortition_ids_diverged = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // setup:
    //   0 - 1 - 2 - 3 - 4 - 5 - 6 - 7 - 8 - 9
    //    \_ 10 _ 11
    //  blocks `10` and `11` can be processed either
    //    in PoX fork 111 or in 110
    for (ix, (vrf_key, miner)) in vrf_keys.iter().zip(committers.iter()).enumerate() {
        let mut burnchain = get_burnchain_db(path, None);
        let mut chainstate = get_chainstate(path);
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let burnchain_blinded = get_burnchain_db(path_blinded, None);
        let b = get_burnchain(path, None);

        eprintln!("Making block {}", ix);
        let (op, block) = if ix == 0 {
            make_genesis_block(
                &sort_db,
                &mut chainstate,
                &BlockHeaderHash([0; 32]),
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        } else {
            let parent = if ix == 10 {
                stacks_blocks[0].1.header.block_hash()
            } else {
                stacks_blocks[ix - 1].1.header.block_hash()
            };
            make_stacks_block(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        };
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            vec![op],
            [burnchain_blinded].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();
        coord_blind.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            eprintln!(
                "Reward cycle start at height={}",
                new_burnchain_tip.block_height
            );
            // the "blinded" sortition db and the one that's processed all the blocks
            //   should have diverged in sortition_ids now...
            sortition_ids_diverged = true;
            // store the anchor block for this sortition for later checking
            let ic = sort_db.index_handle_at_tip();
            let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
            eprintln!(
                "Anchor block={}, selected at height={}",
                &bhh,
                SortitionDB::get_block_snapshot_for_winning_stacks_block(
                    &sort_db.index_conn(),
                    &ic.context.chain_tip,
                    &bhh
                )
                .unwrap()
                .unwrap()
                .block_height
            );
            anchor_blocks.push(bhh);
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
        if sortition_ids_diverged {
            assert_ne!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should have diverged by block height = {}",
                blinded_tip.block_height
            );
        } else {
            assert_eq!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should not have diverged at block height = {}",
                blinded_tip.block_height
            );
        }

        // load the block into staging
        let block_hash = block.header.block_hash();
        eprintln!("Block hash={}, ix={}", &block_hash, ix);

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let block_height = eval_at_chain_tip(path, &sort_db, "block-height");
    assert_eq!(block_height, Value::UInt(10));

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(0));

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "111");
    }

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "100");
    }

    // now, we reveal `0` to the blinded coordinator

    reveal_block(
        path_blinded,
        &sort_db_blind,
        &mut coord_blind,
        &stacks_blocks[0].0,
        &stacks_blocks[0].1,
    );

    // after revealing ``0``, we should now have the anchor block for
    //   the first reward cycle after the initial one

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "110");
    }

    // now, the blinded node should be able to process blocks 10 and 11
    //   10 will process fine, because its parent has consensus hash =
    //       INITIAL_CONSENSUS_HASH
    //   11 will NOT process fine, even though it _should_, because its parents
    //     consensus hash is different than the consensus hash of the parent when it was mined

    let sort_id = SortitionDB::get_block_snapshot_for_winning_stacks_block(
        &sort_db_blind.index_conn(),
        &SortitionDB::get_canonical_sortition_tip(sort_db_blind.conn()).unwrap(),
        &stacks_blocks[10].1.block_hash(),
    )
    .unwrap()
    .unwrap()
    .sortition_id;

    reveal_block(
        path_blinded,
        &sort_db_blind,
        &mut coord_blind,
        &sort_id,
        &stacks_blocks[10].1,
    );

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(2));
    eprintln!("Processed block 10 okay!");

    // won't successfully process the block
    let sort_id = SortitionDB::get_block_snapshot_for_winning_stacks_block(
        &sort_db_blind.index_conn(),
        &SortitionDB::get_canonical_sortition_tip(sort_db_blind.conn()).unwrap(),
        &stacks_blocks[11].1.block_hash(),
    )
    .unwrap()
    .unwrap()
    .sortition_id;

    reveal_block(
        path_blinded,
        &sort_db_blind,
        &mut coord_blind,
        &sort_id,
        &stacks_blocks[11].1,
    );

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(3));
    eprintln!("Processed block 11 okay!");
}

#[test]
fn test_pox_no_anchor_selected() {
    let path = "/tmp/stacks-blockchain.test.pox_fork_no_anchor_selected";
    // setup a second set of states that won't see the broadcasted blocks
    let path_blinded = "/tmp/stacks-blockchain.test.pox_fork_no_anchor_selected.blinded";
    let _r = std::fs::remove_dir_all(path);
    let _r = std::fs::remove_dir_all(path_blinded);

    let vrf_keys: Vec<_> = (0..10).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..10).map(|_| StacksPrivateKey::new()).collect();

    setup_states(&[path, path_blinded], &vrf_keys, &committers, None, None);

    let mut coord = make_coordinator(path, None);
    let mut coord_blind = make_coordinator(path_blinded, None);

    coord.handle_new_burnchain_block().unwrap();
    coord_blind.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    let sort_db_blind = get_sortition_db(path_blinded, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db_blind
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    // at first, sortition_ids shouldn't have diverged
    //  but once the first reward cycle begins, they should diverge.
    let mut sortition_ids_diverged = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // setup:
    //   0 - 1 - 2 - 3 - 4 - 5 - 6
    //    \_ 7   \_ 8 _ 9
    for (ix, (vrf_key, miner)) in vrf_keys.iter().zip(committers.iter()).enumerate() {
        let mut burnchain = get_burnchain_db(path, None);
        let mut chainstate = get_chainstate(path);
        let b = get_burnchain(path, None);
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let burnchain_blinded = get_burnchain_db(path_blinded, None);

        eprintln!("Making block {}", ix);
        let (op, block) = if ix == 0 {
            make_genesis_block(
                &sort_db,
                &mut chainstate,
                &BlockHeaderHash([0; 32]),
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        } else {
            let parent = if ix == 7 {
                stacks_blocks[0].1.header.block_hash()
            } else if ix == 8 {
                stacks_blocks[2].1.header.block_hash()
            } else {
                stacks_blocks[ix - 1].1.header.block_hash()
            };
            make_stacks_block(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        };

        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            vec![op],
            [burnchain_blinded].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();
        coord_blind.handle_new_burnchain_block().unwrap();

        let b = get_burnchain(path, None);
        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            eprintln!(
                "Reward cycle start at height={}",
                new_burnchain_tip.block_height
            );
            // processed first anchor block, not expecting a second one!
            if anchor_blocks.len() == 1 {
                let ic = sort_db.index_handle_at_tip();
                assert!(
                    ic.get_last_anchor_block_hash().unwrap().is_none(),
                    "No anchor block should have been chosen!"
                );
            } else {
                // the "blinded" sortition db and the one that's processed all the blocks
                //   should have diverged in sortition_ids now...
                sortition_ids_diverged = true;
                // store the anchor block for this sortition for later checking
                let ic = sort_db.index_handle_at_tip();
                let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
                eprintln!(
                    "Anchor block={}, selected at height={}",
                    &bhh,
                    SortitionDB::get_block_snapshot_for_winning_stacks_block(
                        &sort_db.index_conn(),
                        &ic.context.chain_tip,
                        &bhh
                    )
                    .unwrap()
                    .unwrap()
                    .block_height
                );
                anchor_blocks.push(bhh);
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
        if sortition_ids_diverged {
            assert_ne!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should have diverged by block height = {}",
                blinded_tip.block_height
            );
        } else {
            assert_eq!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should not have diverged at block height = {}",
                blinded_tip.block_height
            );
        }

        // load the block into staging
        let block_hash = block.header.block_hash();
        eprintln!("Block hash={}, ix={}", &block_hash, ix);

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let block_height = eval_at_chain_tip(path, &sort_db, "block-height");
    assert_eq!(block_height, Value::UInt(7));

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(0));

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "1111");
    }

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "1101");
    }

    for (sort_id, block) in stacks_blocks.iter() {
        reveal_block(
            path_blinded,
            &sort_db_blind,
            &mut coord_blind,
            &sort_id,
            block,
        );
    }

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "1111");
    }

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(7));
}

#[test]
fn test_pox_fork_out_of_order() {
    let path = "/tmp/stacks-blockchain.test.pox_fork_out_of_order";
    // setup a second set of states that won't see the broadcasted blocks
    let path_blinded = "/tmp/stacks-blockchain.test.pox_fork_out_of_order.blinded";
    let _r = std::fs::remove_dir_all(path);
    let _r = std::fs::remove_dir_all(path_blinded);

    let vrf_keys: Vec<_> = (0..15).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..15).map(|_| StacksPrivateKey::new()).collect();

    setup_states(&[path, path_blinded], &vrf_keys, &committers, None, None);

    let mut coord = make_coordinator(path, None);
    let mut coord_blind = make_coordinator(path_blinded, None);

    coord.handle_new_burnchain_block().unwrap();
    coord_blind.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    let sort_db_blind = get_sortition_db(path_blinded, None);

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db_blind
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    // we should have all the VRF registrations accepted
    assert_eq!(ops.accepted_ops.len(), vrf_keys.len());
    assert_eq!(ops.consumed_leader_keys.len(), 0);

    // at first, sortition_ids shouldn't have diverged
    //  but once the first reward cycle begins, they should diverge.
    let mut sortition_ids_diverged = false;
    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];
    let mut anchor_blocks = vec![];

    // setup:
    //  2 forks: 0 - 1 - 2 - 3 - 4 - 5 - 11 - 12 - 13 - 14 - 15
    //            \_ 6 _ 7 _ 8 _ 9 _ 10
    for (ix, (vrf_key, miner)) in vrf_keys.iter().zip(committers.iter()).enumerate() {
        let mut burnchain = get_burnchain_db(path, None);
        let mut chainstate = get_chainstate(path);
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let burnchain_blinded = get_burnchain_db(path_blinded, None);
        let b = get_burnchain(path, None);

        eprintln!("Making block {}", ix);
        let (op, block) = if ix == 0 {
            make_genesis_block(
                &sort_db,
                &mut chainstate,
                &BlockHeaderHash([0; 32]),
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        } else {
            let parent = if ix == 1 {
                stacks_blocks[0].1.header.block_hash()
            } else if ix == 6 {
                stacks_blocks[0].1.header.block_hash()
            } else if ix == 11 {
                stacks_blocks[5].1.header.block_hash()
            } else {
                stacks_blocks[ix - 1].1.header.block_hash()
            };
            make_stacks_block(
                &sort_db,
                &mut chainstate,
                &b,
                &parent,
                burnchain_tip.block_height,
                miner,
                10000,
                vrf_key,
                ix as u32,
            )
        };
        produce_burn_block(
            &mut burnchain,
            &burnchain_tip.block_hash,
            vec![op],
            [burnchain_blinded].iter_mut(),
        );
        // handle the sortition
        coord.handle_new_burnchain_block().unwrap();
        coord_blind.handle_new_burnchain_block().unwrap();

        let new_burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        if b.is_reward_cycle_start(new_burnchain_tip.block_height) {
            eprintln!(
                "Reward cycle start at height={}",
                new_burnchain_tip.block_height
            );
            // the "blinded" sortition db and the one that's processed all the blocks
            //   should have diverged in sortition_ids now...
            sortition_ids_diverged = true;
            // store the anchor block for this sortition for later checking
            let ic = sort_db.index_handle_at_tip();
            let bhh = ic.get_last_anchor_block_hash().unwrap().unwrap();
            eprintln!(
                "Anchor block={}, selected at height={}",
                &bhh,
                SortitionDB::get_block_snapshot_for_winning_stacks_block(
                    &sort_db.index_conn(),
                    &ic.context.chain_tip,
                    &bhh
                )
                .unwrap()
                .unwrap()
                .block_height
            );

            anchor_blocks.push(bhh);
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
        if sortition_ids_diverged {
            assert_ne!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should have diverged by block height = {}",
                blinded_tip.block_height
            );
        } else {
            assert_eq!(
                tip.sortition_id, blinded_tip.sortition_id,
                "Sortitions should not have diverged at block height = {}",
                blinded_tip.block_height
            );
        }

        // load the block into staging
        let block_hash = block.header.block_hash();
        eprintln!("Block hash={}, ix={}", &block_hash, ix);

        assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
        stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

        preprocess_block(&mut chainstate, &sort_db, &tip, block);

        // handle the stacks block
        coord.handle_new_stacks_block().unwrap();
    }

    let block_height = eval_at_chain_tip(path, &sort_db, "block-height");
    assert_eq!(block_height, Value::UInt(10));

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(0));

    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "11111");
    }

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "11000");
    }

    // now, we reveal to the blinded coordinator, but out of order.
    //  reveal block 0 first,
    //   then the 6-7-8-9-10 fork.
    //   then reveal 1-2-3-4-5
    //   then reveal 11-12-13-14

    reveal_block(
        path_blinded,
        &sort_db_blind,
        &mut coord_blind,
        &stacks_blocks[0].0,
        &stacks_blocks[0].1,
    );

    // after revealing ``0``, we should now have the anchor block for
    //   the 6-7-8-9-10 fork

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "11110");
    }

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(1));

    // reveal [6-10]
    for (_sort_id, block) in stacks_blocks[6..=10].iter() {
        // cannot use sort_id from stacks_blocks, because the blinded coordinator
        //   has different sortition_id's for blocks 6-10 (because it's missing
        //   the 2nd anchor block).
        let sort_id = SortitionDB::get_block_snapshot_for_winning_stacks_block(
            &sort_db_blind.index_conn(),
            &SortitionDB::get_canonical_sortition_tip(sort_db_blind.conn()).unwrap(),
            &block.header.block_hash(),
        )
        .unwrap()
        .unwrap()
        .sortition_id;
        reveal_block(
            path_blinded,
            &sort_db_blind,
            &mut coord_blind,
            &sort_id,
            block,
        );
    }

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "11110");
    }

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(6));

    let block_hash = eval_at_chain_tip(
        path_blinded,
        &sort_db_blind,
        "(get-block-info? header-hash u5)",
    );
    assert_eq!(
        block_hash,
        Value::some(
            Value::buff_from(stacks_blocks[9].1.header.block_hash().as_bytes().to_vec()).unwrap()
        )
        .unwrap()
    );

    // reveal [1-5]
    for (_sort_id, block) in stacks_blocks[1..=5].iter() {
        // cannot use sort_id from stacks_blocks, because the blinded coordinator
        //   has different sortition_id's for blocks 6-10 (because it's missing
        //   the 2nd anchor block).
        let sort_id = SortitionDB::get_block_snapshot_for_winning_stacks_block(
            &sort_db_blind.index_conn(),
            &SortitionDB::get_canonical_sortition_tip(sort_db_blind.conn()).unwrap(),
            &block.header.block_hash(),
        )
        .unwrap()
        .unwrap()
        .sortition_id;

        // before processing the last of these blocks, the stacks_block[9] should still
        //   be the canonical tip
        let block_hash = eval_at_chain_tip(
            path_blinded,
            &sort_db_blind,
            "(get-block-info? header-hash u5)",
        );
        assert_eq!(
            block_hash,
            Value::some(
                Value::buff_from(stacks_blocks[9].1.header.block_hash().as_bytes().to_vec())
                    .unwrap()
            )
            .unwrap()
        );

        reveal_block(
            path_blinded,
            &sort_db_blind,
            &mut coord_blind,
            &sort_id,
            block,
        );
    }

    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "11111");
    }

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(6));

    // reveal [11-14]
    for (_sort_id, block) in stacks_blocks[11..].iter() {
        // cannot use sort_id from stacks_blocks, because the blinded coordinator
        //   has different sortition_id's for blocks 6-10 (because it's missing
        //   the 2nd anchor block).
        let sort_id = SortitionDB::get_block_snapshot_for_winning_stacks_block(
            &sort_db_blind.index_conn(),
            &SortitionDB::get_canonical_sortition_tip(sort_db_blind.conn()).unwrap(),
            &block.header.block_hash(),
        )
        .unwrap()
        .unwrap()
        .sortition_id;

        reveal_block(
            path_blinded,
            &sort_db_blind,
            &mut coord_blind,
            &sort_id,
            block,
        );
    }

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(10));

    let block_hash = eval_at_chain_tip(
        path_blinded,
        &sort_db_blind,
        "(get-block-info? header-hash u9)",
    );
    assert_eq!(
        block_hash,
        Value::some(
            Value::buff_from(stacks_blocks[13].1.header.block_hash().as_bytes().to_vec()).unwrap()
        )
        .unwrap()
    );
}

fn eval_at_chain_tip(chainstate_path: &str, sort_db: &SortitionDB, eval: &str) -> Value {
    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let mut chainstate = get_chainstate(chainstate_path);
    chainstate
        .with_read_only_clarity_tx(
            &sort_db.index_conn(),
            &StacksBlockId::new(&stacks_tip.0, &stacks_tip.1),
            |conn| {
                conn.with_readonly_clarity_env(
                    false,
                    PrincipalData::parse("SP3Q4A5WWZ80REGBN0ZXNE540ECJ9JZ4A765Q5K2Q").unwrap(),
                    LimitedCostTracker::new_free(),
                    |env| env.eval_raw(eval),
                )
                .unwrap()
            },
        )
        .unwrap()
}

fn reveal_block<T: BlockEventDispatcher, N: CoordinatorNotices, U: RewardSetProvider>(
    chainstate_path: &str,
    sort_db: &SortitionDB,
    coord: &mut ChainsCoordinator<T, N, U>,
    my_sortition: &SortitionId,
    block: &StacksBlock,
) {
    let mut chainstate = get_chainstate(chainstate_path);
    let sortition = SortitionDB::get_block_snapshot(sort_db.conn(), &my_sortition)
        .unwrap()
        .unwrap();
    preprocess_block(&mut chainstate, sort_db, &sortition, block.clone());
    coord.handle_new_stacks_block().unwrap();
}

fn preprocess_block(
    chain_state: &mut StacksChainState,
    sort_db: &SortitionDB,
    my_sortition: &BlockSnapshot,
    block: StacksBlock,
) {
    let ic = sort_db.index_conn();
    let parent_consensus_hash = SortitionDB::get_block_snapshot_for_winning_stacks_block(
        &ic,
        &my_sortition.sortition_id,
        &block.header.parent_block,
    )
    .unwrap()
    .unwrap()
    .consensus_hash;
    // Preprocess the anchored block
    chain_state
        .preprocess_anchored_block(
            &ic,
            &my_sortition.consensus_hash,
            &block,
            &parent_consensus_hash,
            5,
        )
        .unwrap();
}
