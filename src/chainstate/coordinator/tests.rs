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
use std::collections::BTreeMap;
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

use deps::bitcoin::blockdata::block::{BlockHeader, LoneBlockHeader};
use deps::bitcoin::network::serialize::BitcoinHash;
use deps::bitcoin::util::hash::Sha256dHash;

lazy_static! {
    pub static ref BURN_BLOCK_HEADERS: Arc<AtomicU64> = Arc::new(AtomicU64::new(1));
    pub static ref TXIDS: Arc<AtomicU64> = Arc::new(AtomicU64::new(1));
    pub static ref MBLOCK_PUBKHS: Arc<AtomicU64> = Arc::new(AtomicU64::new(1));
    pub static ref STACKS_BLOCK_HEADERS: Arc<AtomicU64> = Arc::new(AtomicU64::new(1));
}

pub fn next_block_hash() -> BlockHeaderHash {
    let cur = STACKS_BLOCK_HEADERS.fetch_add(1, Ordering::SeqCst);
    let mut bytes = vec![];
    bytes.extend_from_slice(&cur.to_le_bytes());
    bytes.extend_from_slice(&[0; 24]);
    BlockHeaderHash::from_bytes(&bytes).unwrap()
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
    burnchain_conf: &Burnchain,
    burnchain_db: &mut BurnchainDB,
    par: &BurnchainHeaderHash,
    mut ops: Vec<BlockstackOperationType>,
    others: I,
) -> BurnchainHeaderHash {
    let BurnchainBlockData {
        header: par_header, ..
    } = BurnchainDB::get_burnchain_block(&burnchain_db.conn(), par).unwrap();
    assert_eq!(&par_header.block_hash, par);
    let block_height = par_header.block_height + 1;
    for op in ops.iter_mut() {
        op.set_block_height(block_height);
    }

    produce_burn_block_do_not_set_height(burnchain_conf, burnchain_db, par, ops, others)
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
    burnchain_conf: &Burnchain,
    burnchain_db: &mut BurnchainDB,
    par: &BurnchainHeaderHash,
    mut ops: Vec<BlockstackOperationType>,
    others: I,
) -> BurnchainHeaderHash {
    let BurnchainBlockData {
        header: par_header, ..
    } = BurnchainDB::get_burnchain_block(&burnchain_db.conn(), par).unwrap();
    assert_eq!(&par_header.block_hash, par);
    let block_height = par_header.block_height + 1;
    let timestamp = par_header.timestamp + 1;
    let num_txs = ops.len() as u64;

    let bitcoin_header = BlockHeader {
        bits: 0,
        merkle_root: Sha256dHash([0u8; 32]),
        nonce: 0,
        prev_blockhash: par.to_bitcoin_hash(),
        time: timestamp as u32,
        version: 0x20000000,
    };

    let block_hash = BurnchainHeaderHash::from_bitcoin_hash(&bitcoin_header.bitcoin_hash());

    let header = BurnchainBlockHeader {
        block_height,
        timestamp,
        num_txs,
        block_hash: block_hash.clone(),
        parent_block_hash: par.clone(),
    };

    let mut indexer = BitcoinIndexer::new_unit_test(&burnchain_conf.working_dir);
    indexer.raw_store_header(header.clone()).unwrap();

    for op in ops.iter_mut() {
        op.set_burn_header_hash(block_hash.clone());
    }

    burnchain_db
        .raw_store_burnchain_block(burnchain_conf, &indexer, header.clone(), ops.clone())
        .unwrap();

    let this_reward_cycle = burnchain_conf
        .block_height_to_reward_cycle(block_height)
        .unwrap_or(0);

    let prev_reward_cycle = burnchain_conf
        .block_height_to_reward_cycle(block_height.saturating_sub(1))
        .unwrap_or(0);

    if this_reward_cycle != prev_reward_cycle {
        // at reward cycle boundary
        test_debug!(
            "Update PoX affirmation maps for reward cycle {} ({}) block {} cycle-length {}",
            prev_reward_cycle,
            this_reward_cycle,
            block_height,
            burnchain_conf.pox_constants.reward_cycle_length
        );
        update_pox_affirmation_maps(burnchain_db, &indexer, prev_reward_cycle, burnchain_conf)
            .unwrap();
    }

    for other in others {
        other
            .raw_store_burnchain_block(burnchain_conf, &indexer, header.clone(), ops.clone())
            .unwrap();

        if this_reward_cycle != prev_reward_cycle {
            update_pox_affirmation_maps(other, &indexer, prev_reward_cycle, burnchain_conf)
                .unwrap();
        }
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
    inner_setup_states(
        paths,
        vrf_keys,
        committers,
        pox_consts,
        initial_balances,
        StacksEpochId::Epoch20,
    )
}

pub fn setup_states_2_1(
    paths: &[&str],
    vrf_keys: &[VRFPrivateKey],
    committers: &[StacksPrivateKey],
    pox_consts: Option<PoxConstants>,
    initial_balances: Option<Vec<(PrincipalData, u64)>>,
) {
    inner_setup_states(
        paths,
        vrf_keys,
        committers,
        pox_consts,
        initial_balances,
        StacksEpochId::Epoch21,
    )
}

fn inner_setup_states(
    paths: &[&str],
    vrf_keys: &[VRFPrivateKey],
    committers: &[StacksPrivateKey],
    pox_consts: Option<PoxConstants>,
    initial_balances: Option<Vec<(PrincipalData, u64)>>,
    start_epoch: StacksEpochId,
) {
    let mut burn_block = None;
    let mut others = vec![];

    for path in paths.iter() {
        let burnchain = get_burnchain(path, pox_consts.clone());

        let epochs = match start_epoch {
            StacksEpochId::Epoch20 => StacksEpoch::unit_test(burnchain.first_block_height),
            StacksEpochId::Epoch21 => StacksEpoch::unit_test_2_1(burnchain.first_block_height),
            _ => panic!("Cannot start in epoch 1.0"),
        };

        let sortition_db = SortitionDB::connect(
            &burnchain.get_db_path(),
            burnchain.first_block_height,
            &burnchain.first_block_hash,
            burnchain.first_block_timestamp.into(),
            &epochs,
            true,
        )
        .unwrap();

        let burnchain_blocks_db =
            BurnchainDB::connect(&burnchain.get_burnchaindb_path(), &burnchain, true).unwrap();

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
                path.clone(),
            ));
        } else {
            others.push(burnchain_blocks_db);
        }
    }

    let (mut burnchain_blocks_db, burn_header_hash, registers, path) = burn_block.take().unwrap();
    let burnchain = get_burnchain(path, pox_consts.clone());

    produce_burn_block(
        &burnchain,
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
                    None,
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

fn make_stacks_block_from_parent_sortition(
    sort_db: &SortitionDB,
    state: &mut StacksChainState,
    burnchain: &Burnchain,
    parent_block: &BlockHeaderHash,
    parent_height: u64,
    miner: &StacksPrivateKey,
    my_burn: u64,
    vrf_key: &VRFPrivateKey,
    key_index: u32,
    parent_sortition: BlockSnapshot,
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
        None,
        0,
        false,
        (Txid([0; 32]), 0),
        Some(parent_sortition),
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
        None,
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
    parents_sortition_opt: Option<BlockSnapshot>,
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
    let parents_sortition = if let Some(sn) = parents_sortition_opt {
        sn
    } else {
        SortitionDB::get_block_snapshot_for_winning_stacks_block(
            &sort_db.index_conn(),
            &sortition_tip.sortition_id,
            parent_block,
        )
        .unwrap()
        .unwrap()
    };

    eprintln!(
        "Find parents stacks header: {} in sortition {} (height {}, parent {}/{},{}, index block hash {})",
        &parent_block, &parents_sortition.sortition_id, parents_sortition.block_height, &parents_sortition.consensus_hash, parent_block, parent_height, &StacksBlockHeader::make_index_block_hash(&parents_sortition.consensus_hash, &parent_block)
    );

    let parent_vtxindex =
        SortitionDB::get_block_winning_vtxindex(sort_db.conn(), &parents_sortition.sortition_id)
            .unwrap()
            .unwrap();

    let parent_stacks_header = StacksChainState::get_anchored_block_header_info(
        state.db(),
        &parents_sortition.consensus_hash,
        parent_block,
    )
    .unwrap()
    .unwrap();

    eprintln!("Build off of {:?}", &parent_stacks_header);

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
                None,
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
                None,
            )
        };

        good_op.set_block_height(next_mock_header.block_height);

        let expected_winner = good_op.txid();
        ops.push(good_op);

        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();

        if ix % (MINING_COMMITMENT_WINDOW as usize) == 3 {
            // produce an empty block!
            produce_burn_block(
                &burnchain_conf,
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
                &burnchain_conf,
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
            &b,
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
            &b,
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
            &b,
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
            &b,
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
            &b,
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

    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];

    // produce some burn blocks without sortitions:
    for _ix in 0..50 {
        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        produce_burn_block(
            &burnchain_conf,
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
                &burnchain_conf,
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
                &b,
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
            &b,
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

    let pox_consts = Some(PoxConstants::new(
        5,
        2,
        2,
        25,
        5,
        u64::max_value(),
        u64::max_value(),
    ));
    let b = get_burnchain(path, pox_consts.clone());
    let b_blind = get_burnchain(path_blinded, pox_consts.clone());

    let vrf_keys: Vec<_> = (0..20).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..20).map(|_| StacksPrivateKey::new()).collect();

    setup_states_2_1(
        &[path, path_blinded],
        &vrf_keys,
        &committers,
        pox_consts.clone(),
        None,
    );

    let mut coord = make_coordinator(path, Some(b));
    let mut coord_blind = make_coordinator(path_blinded, Some(b_blind));

    coord.handle_new_burnchain_block().unwrap();
    coord_blind.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, pox_consts.clone());

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    let sort_db_blind = get_sortition_db(path_blinded, pox_consts.clone());

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

    // process sequential blocks, and their sortitions...
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock)> = vec![];

    // setup:
    // sort:1                   6                   11                      16                       21
    //      |----- rc 0 --------|------ rc 1 -------|----- rc 2 ------------|-------- rc 3 ----------|----- rc 4
    // ix:  X - 0 - 1 - 2 - 3 - 4 - 5 - 6 - 7 - 8 - 9
    //           \_____________________________________ 10 _ 11 _ 12 _ 13 _ 14 _ 15 _ 16 _ 17 _ 18 _ 19
    //
    //
    for (ix, (vrf_key, miner)) in vrf_keys.iter().zip(committers.iter()).enumerate() {
        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let burnchain_blind = get_burnchain_db(path_blinded, pox_consts.clone());
        let mut chainstate = get_chainstate(path);
        let mut chainstate_blind = get_chainstate(path_blinded);
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let burnchain_tip_blind = burnchain_blind.get_canonical_chain_tip().unwrap();
        let b = get_burnchain(path, pox_consts.clone());
        let b_blind = get_burnchain(path_blinded, pox_consts.clone());

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
            if ix < 10 {
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
            } else {
                make_stacks_block(
                    &sort_db_blind,
                    &mut chainstate_blind,
                    &b_blind,
                    &parent,
                    burnchain_tip_blind.block_height,
                    miner,
                    10000,
                    vrf_key,
                    ix as u32,
                )
            }
        };
        produce_burn_block(
            &b,
            &mut burnchain,
            &burnchain_tip.block_hash,
            vec![op],
            [burnchain_blind].iter_mut(),
        );

        // handle the sortition -- if
        loop {
            let missing_anchor_opt = coord.handle_new_burnchain_block().unwrap();
            if let Some(missing_anchor) = missing_anchor_opt {
                eprintln!(
                    "Unblinded database reports missing anchor block {:?} (ix={})",
                    &missing_anchor, ix
                );
                for (_, blk) in stacks_blocks.iter() {
                    if blk.block_hash() == missing_anchor {
                        let ic = sort_db.index_conn();
                        let tip =
                            SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
                        let sn = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                            &ic,
                            &tip.sortition_id,
                            &blk.block_hash(),
                        )
                        .unwrap()
                        .unwrap();

                        // feed this missing reward cycle data
                        let rc = b_blind
                            .block_height_to_reward_cycle(sn.block_height)
                            .unwrap();
                        let start_height = b_blind.reward_cycle_to_block_height(rc);
                        for height in start_height..sn.block_height {
                            let asn =
                                SortitionDB::get_ancestor_snapshot(&ic, height, &tip.sortition_id)
                                    .unwrap()
                                    .unwrap();
                            for (_, blk) in stacks_blocks.iter() {
                                if blk.block_hash() == asn.winning_stacks_block_hash {
                                    eprintln!("Unblinded database accepts missing anchor block ancestor {} of {} (ix={})", &blk.block_hash(), &missing_anchor, ix);
                                    preprocess_block(&mut chainstate, &sort_db, &asn, blk.clone());
                                    coord.handle_new_stacks_block().unwrap();
                                    break;
                                }
                            }
                        }

                        // *now* process this anchor block
                        eprintln!(
                            "Unblinded database processes missing anchor block {} (ix={})",
                            &missing_anchor, ix
                        );
                        preprocess_block(&mut chainstate, &sort_db, &sn, blk.clone());
                        coord.handle_new_stacks_block().unwrap();
                        break;
                    }
                }
            } else {
                coord.handle_new_stacks_block().unwrap();
                break;
            }
        }

        coord_blind.handle_new_burnchain_block().unwrap();
        coord_blind.handle_new_stacks_block().unwrap();

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();

        if ix < 10 {
            // load the block into staging and process it on the un-blinded sortition DB
            let block_hash = block.header.block_hash();
            eprintln!(
                "Block hash={}, parent={}, height={}, ix={} (not blind)",
                &block_hash, &block.header.parent_block, block.header.total_work.work, ix
            );

            assert_eq!(&tip.winning_stacks_block_hash, &block_hash);
            stacks_blocks.push((tip.sortition_id.clone(), block.clone()));

            preprocess_block(&mut chainstate, &sort_db, &tip, block.clone());

            // handle the stacks block
            coord.handle_new_stacks_block().unwrap();
        }
        if ix == 0 || ix >= 10 {
            // load the block into staging and process it on the blinded sortition DB
            let block_hash = block.header.block_hash();
            eprintln!(
                "Block hash={}, parent={}, height={}, ix={} (blind)",
                &block_hash, &block.header.parent_block, block.header.total_work.work, ix
            );

            assert_eq!(&blinded_tip.winning_stacks_block_hash, &block_hash);
            if ix != 0 {
                stacks_blocks.push((blinded_tip.sortition_id.clone(), block.clone()));
            }

            preprocess_block(&mut chainstate_blind, &sort_db_blind, &blinded_tip, block);

            // handle the stacks block
            coord_blind.handle_new_stacks_block().unwrap();
        }
        if ix == 18 {
            // right at the end of reward cycle 3 -- feed in the blocks from the blinded DB into
            // the unblinded DB
            for (i, (_, block)) in stacks_blocks.iter().enumerate() {
                if i >= 10 && i <= ix {
                    eprintln!("Mirror blocks from blinded DB to unblinded DB (simulates downloading them) i={}", i);
                    let ic = sort_db_blind.index_conn();
                    let sn = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                        &ic,
                        &tip.sortition_id,
                        &block.block_hash(),
                    )
                    .unwrap()
                    .unwrap();
                    preprocess_block(&mut chainstate, &sort_db, &sn, block.clone());
                    let _ = coord.handle_new_stacks_block();
                }
            }
        }
        if ix > 18 {
            // starting in reward cycle 4 -- this should NOT panic
            eprintln!("Mirror block {} to unblinded DB", ix);
            preprocess_block(&mut chainstate, &sort_db, &tip, stacks_blocks[ix].1.clone());
            let _ = coord.handle_new_stacks_block();
        }
    }

    // both the blinded and unblined chains should now have the same view
    let block_height = eval_at_chain_tip(path, &sort_db, "block-height");
    assert_eq!(block_height, Value::UInt(11));

    let block_height = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height, Value::UInt(11));

    // because of the affirmations, the canonical PoX ID deliberately omits anchor blocks
    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "110011");
    }
    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "110011");
    }

    // same canonical Stacks chain tip
    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let stacks_tip_blind =
        SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db_blind.conn()).unwrap();
    assert_eq!(stacks_tip, stacks_tip_blind);

    // same final consensus hash, at the start of height 20
    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();

    assert!(tip.sortition);
    assert!(blinded_tip.sortition);
    assert_eq!(
        tip.winning_stacks_block_hash,
        blinded_tip.winning_stacks_block_hash
    );
    assert_eq!(tip.burn_header_hash, blinded_tip.burn_header_hash);
    assert_eq!(tip.consensus_hash, blinded_tip.consensus_hash);
    assert_eq!(tip.block_height, 21);
    assert_eq!(blinded_tip.block_height, 21);
}

fn highest_block(sortitions: &HashMap<u64, BlockSnapshot>) -> BlockSnapshot {
    let mut max_k = 0;
    for (k, _) in sortitions.iter() {
        if *k > max_k {
            max_k = *k;
        }
    }
    sortitions.get(&max_k).clone().unwrap().to_owned()
}

fn replay_reward_cycle<'a>(
    stacks_blocks: &Vec<(SortitionId, StacksBlock, u64)>,
    b: &Burnchain,
    coord: &mut ChainsCoordinator<'a, NullEventDispatcher, (), OnChainRewardSetProvider>,
    sort_db: &SortitionDB,
    chainstate: &mut StacksChainState,
) {
    for _ in 0..b.pox_constants.reward_cycle_length {
        let missing_anchor_opt = coord.handle_new_burnchain_block().unwrap();
        if let Some(missing_anchor) = missing_anchor_opt {
            eprintln!(
                "Database {} reports missing anchor block {:?}",
                &b.working_dir, &missing_anchor
            );
            for (_, blk, ..) in stacks_blocks.iter() {
                if blk.block_hash() == missing_anchor {
                    let ic = sort_db.index_conn();
                    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
                    let sn = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                        &ic,
                        &tip.sortition_id,
                        &blk.block_hash(),
                    )
                    .unwrap()
                    .unwrap();

                    // feed this missing reward cycle data
                    let rc = b.block_height_to_reward_cycle(sn.block_height).unwrap();
                    for height in 0..sn.block_height {
                        let asn =
                            SortitionDB::get_ancestor_snapshot(&ic, height, &tip.sortition_id)
                                .unwrap()
                                .unwrap();
                        for (_, blk, ..) in stacks_blocks.iter() {
                            if blk.block_hash() == asn.winning_stacks_block_hash {
                                eprintln!(
                                    "Database {} accepts missing anchor block ancestor {} of {}",
                                    &b.working_dir,
                                    &blk.block_hash(),
                                    &missing_anchor
                                );
                                preprocess_block(chainstate, sort_db, &asn, blk.clone());
                                coord.handle_new_stacks_block().unwrap();
                                break;
                            }
                        }
                    }

                    // *now* process this anchor block
                    eprintln!(
                        "Database {} processes missing anchor block {}",
                        &b.working_dir, &missing_anchor
                    );
                    preprocess_block(chainstate, sort_db, &sn, blk.clone());
                    coord.handle_new_stacks_block().unwrap();
                    break;
                }
            }
        } else {
            coord.handle_new_stacks_block().unwrap();
            break;
        }
    }
}

fn load_sortitions(sort_db: &SortitionDB) -> HashMap<u64, BlockSnapshot> {
    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    let ic = sort_db.index_conn();
    let mut ret = HashMap::new();
    for height in 0..(tip.block_height + 1) {
        if let Some(sn) =
            SortitionDB::get_ancestor_snapshot(&ic, height, &tip.sortition_id).unwrap()
        {
            ret.insert(sn.block_height, sn);
        }
    }
    ret
}

#[test]
fn test_pox_affirmation_fork_duel() {
    let path = "/tmp/stacks-blockchain.test.pox_affirmation_fork_duel";
    // setup a second set of states that won't see the broadcasted blocks
    let path_blinded = "/tmp/stacks-blockchain.test.pox_affirmation_fork_duel.blinded";
    let _r = std::fs::remove_dir_all(path);
    let _r = std::fs::remove_dir_all(path_blinded);

    let pox_consts = Some(PoxConstants::new(
        5,
        2,
        2,
        25,
        5,
        u64::max_value(),
        u64::max_value(),
    ));
    let b = get_burnchain(path, pox_consts.clone());
    let b_blind = get_burnchain(path_blinded, pox_consts.clone());

    let vrf_keys: Vec<_> = (0..29).map(|_| VRFPrivateKey::new()).collect();
    let committers: Vec<_> = (0..29).map(|_| StacksPrivateKey::new()).collect();

    setup_states_2_1(
        &[path, path_blinded],
        &vrf_keys,
        &committers,
        pox_consts.clone(),
        None,
    );

    let mut coord = make_coordinator(path, Some(b));
    let mut coord_blind = make_coordinator(path_blinded, Some(b_blind));

    coord.handle_new_burnchain_block().unwrap();
    coord_blind.handle_new_burnchain_block().unwrap();

    let sort_db = get_sortition_db(path, pox_consts.clone());

    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    assert_eq!(tip.block_height, 1);
    assert_eq!(tip.sortition, false);
    let (_, ops) = sort_db
        .get_sortition_result(&tip.sortition_id)
        .unwrap()
        .unwrap();

    let sort_db_blind = get_sortition_db(path_blinded, pox_consts.clone());

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

    // process sequential blocks, and their sortitions, and burn block heights
    let mut stacks_blocks: Vec<(SortitionId, StacksBlock, u64)> = vec![];

    let mut snapshots: HashMap<u64, BlockSnapshot> = HashMap::new();
    let mut snapshots_blind: HashMap<u64, BlockSnapshot> = HashMap::new();

    let mut fork_num = 0;
    let mut fork_start = 0;
    let mut sortition_fork_start = 0;

    // setup (sortitions block height, with Stacks blocks):
    //
    // not blind: 2 - 3 - 4 ------------------- 10 - 11 - 12 - 13 - 14 - 15 ------------------------ 21 - 22 - 23 - 24 - 25
    // blind:      \________ 5 _ 6 _ 7 _ 8 _ 9 _____________________________ 16 _ 17 _ 18 _ 19 _ 20 ________________________ 26 _ 27 _ 28 _ 29
    //
    for (ix, (vrf_key, miner)) in vrf_keys.iter().zip(committers.iter()).enumerate() {
        let mut burnchain = get_burnchain_db(path, pox_consts.clone());
        let burnchain_blind = get_burnchain_db(path_blinded, pox_consts.clone());
        let mut chainstate = get_chainstate(path);
        let mut chainstate_blind = get_chainstate(path_blinded);
        let burnchain_tip = burnchain.get_canonical_chain_tip().unwrap();
        let burnchain_tip_blind = burnchain_blind.get_canonical_chain_tip().unwrap();
        let b = get_burnchain(path, pox_consts.clone());
        let b_blind = get_burnchain(path_blinded, pox_consts.clone());

        let prev_reward_cycle = b
            .block_height_to_reward_cycle(burnchain_tip.block_height.saturating_sub(1))
            .unwrap_or(0);
        let cur_reward_cycle = b
            .block_height_to_reward_cycle(burnchain_tip.block_height)
            .unwrap_or(0);
        let next_reward_cycle = b
            .block_height_to_reward_cycle(burnchain_tip.block_height + 1)
            .unwrap_or(0);
        let will_rc_start = cur_reward_cycle != next_reward_cycle;

        let burn_block = burnchain_tip.block_height;

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
            let (parent, parent_sortition) = if burn_block == 5 {
                fork_num += 1;
                fork_start = stacks_blocks.len() - 1;
                sortition_fork_start = highest_block(&snapshots).block_height;
                let p = stacks_blocks[0].1.header.block_hash();
                eprintln!("snapshots = {:?}", &snapshots);
                (p, snapshots.get(&2).unwrap().clone())
            } else if burn_block == 10 {
                fork_num += 1;
                let p = stacks_blocks[fork_start - 1].1.header.block_hash();
                let sn = snapshots_blind
                    .get(&(sortition_fork_start - 1))
                    .unwrap()
                    .clone();
                fork_start = stacks_blocks.len() - 2;
                sortition_fork_start = highest_block(&snapshots_blind).block_height;
                (p, sn)
            } else if burn_block == 16 || burn_block == 21 || burn_block == 26 {
                fork_num += 1;
                let p = stacks_blocks[fork_start].1.header.block_hash();
                let parent_burn_height = if burn_block == 16 { 9 } else { burn_block - 6 };

                let sn = if fork_num % 2 == 1 {
                    let sn = snapshots_blind.get(&parent_burn_height).unwrap().clone();
                    sn
                } else {
                    let sn = snapshots.get(&parent_burn_height).unwrap().clone();
                    sn
                };

                fork_start = stacks_blocks.len() - 2;
                (p, sn)
            } else {
                let p = stacks_blocks[ix - 1].1.header.block_hash();
                let sn = if fork_num % 2 == 1 {
                    highest_block(&snapshots_blind)
                } else {
                    highest_block(&snapshots)
                };
                (p, sn)
            };

            if fork_num % 2 == 0 {
                eprintln!("Making block {} off {} burn block {} parent {} {}, prev rc = {}, cur rc = {}, next rc = {}, will_rc_start? {} fork_num = {}, fork_start = {}, (not blind)",
                          ix, &parent, burn_block, parent_sortition.block_height, &parent_sortition.consensus_hash, prev_reward_cycle, cur_reward_cycle, next_reward_cycle, will_rc_start, fork_num, fork_start);
                make_stacks_block_from_parent_sortition(
                    &sort_db,
                    &mut chainstate,
                    &b,
                    &parent,
                    parent_sortition.block_height,
                    miner,
                    10000,
                    vrf_key,
                    ix as u32,
                    parent_sortition,
                )
            } else {
                eprintln!("Making block {} off {} burn block {} parent {} {}, prev rc = {}, cur rc = {}, next rc = {}, will_rc_start? {}, fork_num = {}, fork_start = {} (blind)",
                          ix, &parent, burn_block, parent_sortition.block_height, &parent_sortition.consensus_hash, prev_reward_cycle, cur_reward_cycle, next_reward_cycle, will_rc_start, fork_num, fork_start);
                make_stacks_block_from_parent_sortition(
                    &sort_db_blind,
                    &mut chainstate_blind,
                    &b_blind,
                    &parent,
                    parent_sortition.block_height,
                    miner,
                    10000,
                    vrf_key,
                    ix as u32,
                    parent_sortition,
                )
            }
        };

        eprintln!("Made block {} {}, burn block {}, prev rc = {}, cur rc = {}, next rc = {}, will_rc_start? {}", ix, block.block_hash(), burnchain_tip.block_height, prev_reward_cycle, cur_reward_cycle, next_reward_cycle, will_rc_start);
        produce_burn_block(
            &b,
            &mut burnchain,
            &burnchain_tip.block_hash,
            vec![op],
            [burnchain_blind].iter_mut(),
        );

        if burn_block == 14 {
            // blinded DB has NOT undergone a PoX reorg yet -- it believes that the anchor blocks for
            // reward cycles 1 and 2 have valid snapshots, but it's simply missing the anchor block
            // for rc 1.
            let burnchain_blind = get_burnchain_db(path_blinded, pox_consts.clone());

            let (rc1_bc, rc1_bc_md) =
                BurnchainDB::get_anchor_block_commit(burnchain_blind.conn(), 1)
                    .unwrap()
                    .unwrap();
            let (rc2_bc, rc2_bc_md) =
                BurnchainDB::get_anchor_block_commit(burnchain_blind.conn(), 2)
                    .unwrap()
                    .unwrap();

            let tip_blind =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
            let ic = sort_db_blind.index_conn();
            let handle = ic.as_handle(&tip_blind.sortition_id);

            let rc1_sn_before = handle
                .get_block_snapshot(&rc1_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            let rc2_sn_before = handle
                .get_block_snapshot(&rc2_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert!(rc1_sn_before.pox_valid);
            assert!(rc2_sn_before.pox_valid);

            eprintln!("Handle new burnchain block {} (not blind)", burn_block);
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);

            eprintln!("Handle new burnchain block {} (blind)", burn_block);
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );

            // PoX reorg has happened -- the blinded DB learned about the anchor block for rc2
            let tip_blind =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();

            test_debug!("Blind and unblind chain tips should match");
            assert_eq!(tip.block_height, tip_blind.block_height);
            assert_eq!(tip.consensus_hash, tip_blind.consensus_hash);

            // anchor blocks still on the same consensus history
            let tip_blind =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
            let ic = sort_db_blind.index_conn();
            let handle = ic.as_handle(&tip_blind.sortition_id);

            let rc1_sn = handle
                .get_block_snapshot(&rc1_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            let rc2_sn = handle
                .get_block_snapshot(&rc2_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();

            assert!(rc1_sn_before.pox_valid);
            assert!(rc2_sn_before.pox_valid);

            assert_eq!(rc1_sn_before.consensus_hash, rc1_sn.consensus_hash);
            assert_ne!(rc2_sn_before.consensus_hash, rc2_sn.consensus_hash); // different

            let rc2_sn_invalid = SortitionDB::get_block_snapshot_consensus(
                sort_db_blind.conn(),
                &rc2_sn_before.consensus_hash,
            )
            .unwrap()
            .unwrap();
            assert_eq!(rc2_sn_invalid.consensus_hash, rc2_sn_before.consensus_hash);
            assert!(!rc2_sn_invalid.pox_valid);

            // blinded DB's affirmation map is consistent with unblinded DB
            let heaviest_am = coord_blind.get_canonical_affirmation_map().unwrap();
            assert_eq!(heaviest_am, AffirmationMap::decode("paa").unwrap());
        } else if burn_block == 15 {
            // in order to keep mining on the blinded chainstate, then we'll need to make it so
            // the blinded DB wants to confirm the anchor block for rc 2.  But, it no longer believes
            // that rc 2's anchor block is canonical. We need to override this and force it to re-process.
            let mut burnchain_blind = get_burnchain_db(path_blinded, pox_consts.clone());

            let (rc1_bc, rc1_bc_md) =
                BurnchainDB::get_anchor_block_commit(burnchain_blind.conn(), 1)
                    .unwrap()
                    .unwrap();
            let (rc2_bc, rc2_bc_md) =
                BurnchainDB::get_anchor_block_commit(burnchain_blind.conn(), 2)
                    .unwrap()
                    .unwrap();
            let (rc3_bc, rc3_bc_md) =
                BurnchainDB::get_anchor_block_commit(burnchain_blind.conn(), 3)
                    .unwrap()
                    .unwrap();

            let tip_blind =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
            let ic = sort_db_blind.index_conn();
            let handle = ic.as_handle(&tip_blind.sortition_id);

            let rc1_sn_before = handle
                .get_block_snapshot(&rc1_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            let rc2_sn_before = handle
                .get_block_snapshot(&rc2_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            let rc3_sn_before = handle
                .get_block_snapshot(&rc3_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();

            // force the DB to "revert" back to assuming
            let tx = burnchain_blind.tx_begin().unwrap();
            tx.set_override_affirmation_map(1, AffirmationMap::decode("").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(2, AffirmationMap::decode("a").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(3, AffirmationMap::decode("ap").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(4, AffirmationMap::decode("apa").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(5, AffirmationMap::decode("apap").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(6, AffirmationMap::decode("apapa").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(7, AffirmationMap::decode("apapap").unwrap())
                .unwrap();
            tx.commit().unwrap();

            eprintln!("Replay rc 0 for blinded db");
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );
            eprintln!("Replay rc 1 for blinded db");
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );
            eprintln!("Replay rc 2 for blinded db");
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );

            snapshots_blind = load_sortitions(&sort_db_blind);

            // blinded DB has undergone a PoX reorg that "reverts" it -- it now believes that rc2's
            // anchor block exists, but not rc1's or rc3's.
            let tip_blind =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
            let ic = sort_db_blind.index_conn();
            let handle = ic.as_handle(&tip_blind.sortition_id);

            test_debug!(
                "Test anchor block-commit for rc1 {} in {}",
                &rc1_bc.block_header_hash,
                &rc1_bc_md.burn_block_hash
            );
            let rc1_sn = handle
                .get_block_snapshot(&rc1_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert_eq!(rc1_sn.consensus_hash, rc1_sn_before.consensus_hash);

            test_debug!(
                "Test anchor block-commit for rc2 {} in {}",
                &rc2_bc.block_header_hash,
                &rc2_bc_md.burn_block_hash
            );
            let rc2_sn = handle
                .get_block_snapshot(&rc2_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert_ne!(rc2_sn.consensus_hash, rc2_sn_before.consensus_hash);

            test_debug!(
                "Test anchor block-commit for rc3 {} in {}",
                &rc3_bc.block_header_hash,
                &rc3_bc_md.burn_block_hash
            );
            let rc3_sn = handle
                .get_block_snapshot(&rc3_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert_ne!(rc3_sn.consensus_hash, rc3_sn_before.consensus_hash);

            // old rc2 anchor block consensus hash isn't valid anymore
            let rc2_sn_invalid = SortitionDB::get_block_snapshot_consensus(
                sort_db_blind.conn(),
                &rc2_sn_before.consensus_hash,
            )
            .unwrap()
            .unwrap();
            assert!(!rc2_sn_invalid.pox_valid);

            // blinded DB's affirmation map is consistent with its original history
            let heaviest_am = coord_blind.get_canonical_affirmation_map().unwrap();
            assert_eq!(heaviest_am, AffirmationMap::decode("apa").unwrap());
        } else if burn_block == 19 {
            // merge both chains' views
            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            let tip_blind =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();

            assert_ne!(tip.consensus_hash, tip_blind.consensus_hash);

            eprintln!("Handle new burnchain block {} (not blind)", burn_block);
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);

            eprintln!("Handle new burnchain block {} (blind)", burn_block);
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );
            replay_reward_cycle(
                &stacks_blocks,
                &b_blind,
                &mut coord_blind,
                &sort_db_blind,
                &mut chainstate_blind,
            );

            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            let tip_blind =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();
            assert_eq!(tip.consensus_hash, tip_blind.consensus_hash);

            // the unblinded DB's affirmation map is consistent with the blinded DB's history
            let heaviest_am = coord.get_canonical_affirmation_map().unwrap();
            assert_eq!(heaviest_am, AffirmationMap::decode("apaa").unwrap());
        } else if burn_block == 20 {
            // the unblinded DB wants to confirm the anchor block for rc 1, but it no longer believes
            // that rc 1 is canonical. We need to override this and force it to re-process.
            let mut burnchain = get_burnchain_db(path, pox_consts.clone());

            let (rc1_bc, rc1_bc_md) = BurnchainDB::get_anchor_block_commit(burnchain.conn(), 1)
                .unwrap()
                .unwrap();
            let (rc2_bc, rc2_bc_md) = BurnchainDB::get_anchor_block_commit(burnchain.conn(), 2)
                .unwrap()
                .unwrap();
            let (rc3_bc, rc3_bc_md) = BurnchainDB::get_anchor_block_commit(burnchain.conn(), 3)
                .unwrap()
                .unwrap();
            let (rc4_bc, rc4_bc_md) = BurnchainDB::get_anchor_block_commit(burnchain.conn(), 4)
                .unwrap()
                .unwrap();

            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            let ic = sort_db.index_conn();
            let handle = ic.as_handle(&tip.sortition_id);

            let rc1_sn_before = handle
                .get_block_snapshot(&rc1_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            let rc2_sn_before = handle
                .get_block_snapshot(&rc2_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            let rc3_sn_before = handle
                .get_block_snapshot(&rc3_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            let rc4_sn_before = handle
                .get_block_snapshot(&rc4_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();

            let tx = burnchain.tx_begin().unwrap();
            tx.set_override_affirmation_map(1, AffirmationMap::decode("").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(2, AffirmationMap::decode("p").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(3, AffirmationMap::decode("pa").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(4, AffirmationMap::decode("pap").unwrap())
                .unwrap();
            tx.set_override_affirmation_map(5, AffirmationMap::decode("papa").unwrap())
                .unwrap();
            tx.commit().unwrap();

            eprintln!("Replay rc 0 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 1 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 2 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 3 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 4 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);

            snapshots = load_sortitions(&sort_db);

            // unblinded DB has undergone a PoX reorg that "reverts" it -- it now believes that rc1's
            // anchor block exists as well as rc3's, but not rc2's or rc4's.
            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            let ic = sort_db.index_conn();
            let handle = ic.as_handle(&tip.sortition_id);

            test_debug!(
                "Test anchor block-commit for rc1 {} in {}",
                &rc1_bc.block_header_hash,
                &rc1_bc_md.burn_block_hash
            );
            let rc1_sn = handle
                .get_block_snapshot(&rc1_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert_eq!(rc1_sn.consensus_hash, rc1_sn_before.consensus_hash);

            test_debug!(
                "Test anchor block-commit for rc2 {} in {}",
                &rc2_bc.block_header_hash,
                &rc2_bc_md.burn_block_hash
            );
            let rc2_sn = handle
                .get_block_snapshot(&rc2_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert_ne!(rc2_sn.consensus_hash, rc2_sn_before.consensus_hash);

            test_debug!(
                "Test anchor block-commit for rc3 {} in {}",
                &rc3_bc.block_header_hash,
                &rc3_bc_md.burn_block_hash
            );
            let rc3_sn = handle
                .get_block_snapshot(&rc3_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert_ne!(rc3_sn.consensus_hash, rc3_sn_before.consensus_hash);

            test_debug!(
                "Test anchor block-commit for rc4 {} in {}",
                &rc4_bc.block_header_hash,
                &rc4_bc_md.burn_block_hash
            );
            let rc4_sn = handle
                .get_block_snapshot(&rc4_bc_md.burn_block_hash)
                .unwrap()
                .unwrap();
            assert_ne!(rc4_sn.consensus_hash, rc4_sn_before.consensus_hash);

            // old rc2 anchor block consensus hash isn't valid anymore
            let rc2_sn_invalid = SortitionDB::get_block_snapshot_consensus(
                sort_db.conn(),
                &rc2_sn_before.consensus_hash,
            )
            .unwrap()
            .unwrap();
            assert!(!rc2_sn_invalid.pox_valid);

            // old rc4 anchor block consensus hash isn't valid anymore
            let rc4_sn_invalid = SortitionDB::get_block_snapshot_consensus(
                sort_db.conn(),
                &rc4_sn_before.consensus_hash,
            )
            .unwrap()
            .unwrap();
            assert!(!rc4_sn_invalid.pox_valid);

            // blinded DB's affirmation map is consistent with its original history
            let heaviest_am = coord.get_canonical_affirmation_map().unwrap();
            assert_eq!(heaviest_am, AffirmationMap::decode("papa").unwrap());
        } else if burn_block == 29 {
            let tx = burnchain.tx_begin().unwrap();
            tx.clear_override_affirmation_map(1).unwrap();
            tx.clear_override_affirmation_map(2).unwrap();
            tx.clear_override_affirmation_map(3).unwrap();
            tx.clear_override_affirmation_map(4).unwrap();
            tx.clear_override_affirmation_map(5).unwrap();
            tx.clear_override_affirmation_map(6).unwrap();
            tx.clear_override_affirmation_map(7).unwrap();
            tx.commit().unwrap();

            // unblinded chain syncs with blinded chain
            eprintln!("Handle new burnchain block {} (not blind)", burn_block);

            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 0 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 1 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 2 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 3 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 4 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 5 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);
            eprintln!("Replay rc 6 for unblinded db");
            replay_reward_cycle(&stacks_blocks, &b, &mut coord, &sort_db, &mut chainstate);

            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            for burn_height in (burn_block - 10)..burn_block {
                let ancestor = SortitionDB::get_ancestor_snapshot(
                    &sort_db.index_conn(),
                    burn_height,
                    &tip.sortition_id,
                )
                .unwrap()
                .unwrap();
                for (_, blk, bh) in stacks_blocks.iter() {
                    if ancestor.sortition
                        && ancestor.winning_stacks_block_hash == blk.block_hash()
                        && *bh == burn_height
                    {
                        eprintln!(
                            "Replay {} from {} (not blind)",
                            burn_height,
                            &blk.block_hash()
                        );
                        preprocess_block(&mut chainstate, &sort_db, &ancestor, blk.clone());
                        coord.handle_new_stacks_block().unwrap();
                    }
                }
            }

            let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
            let blinded_tip =
                SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();

            let tip_at_29 =
                SortitionDB::get_ancestor_snapshot(&sort_db.index_conn(), 29, &tip.sortition_id)
                    .unwrap()
                    .unwrap();
            let blinded_tip_at_29 = SortitionDB::get_ancestor_snapshot(
                &sort_db_blind.index_conn(),
                29,
                &blinded_tip.sortition_id,
            )
            .unwrap()
            .unwrap();

            assert_eq!(tip_at_29.consensus_hash, blinded_tip_at_29.consensus_hash);
        } else {
            eprintln!("Handle new burnchain block {} (not blind)", burn_block);
            for _ in 0..(2 * b.pox_constants.reward_cycle_length + 1) {
                coord.handle_new_burnchain_block().unwrap();
                coord.handle_new_stacks_block().unwrap();
            }

            eprintln!("Handle new burnchain block {} (blind)", burn_block);
            for _ in 0..(2 * b.pox_constants.reward_cycle_length + 1) {
                coord_blind.handle_new_burnchain_block().unwrap();
                coord_blind.handle_new_stacks_block().unwrap();
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
        let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();

        snapshots.insert(tip.block_height, tip.clone());
        snapshots_blind.insert(blinded_tip.block_height, blinded_tip.clone());

        if fork_num % 2 == 0 {
            // load the block into staging and process it on the un-blinded sortition DB
            let block_hash = block.header.block_hash();
            eprintln!("Block hash={}, parent={}, height={}, burn_block={}, sortition_tip={}, ix={} (not blind)", &block_hash, &block.header.parent_block, block.header.total_work.work, burn_block, &tip.sortition_id, ix);

            stacks_blocks.push((tip.sortition_id.clone(), block.clone(), tip.block_height));

            if tip.winning_stacks_block_hash == block_hash {
                eprintln!("Preprocess {} (not blind)", &block_hash);
                preprocess_block(&mut chainstate, &sort_db, &tip, block.clone());
            } else {
                eprintln!("Will NOT preprocess {} (not blind)", &block_hash);
            }

            // handle the stacks block
            coord.handle_new_stacks_block().unwrap();
        }
        if ix == 0 || (fork_num % 2) == 1 {
            // load the block into staging and process it on the blinded sortition DB
            let block_hash = block.header.block_hash();
            eprintln!("Block hash={}, parent={}, height={}, burn_block={}, sortition_tip={}, ix={} (blind)", &block_hash, &block.header.parent_block, block.header.total_work.work, burn_block, &blinded_tip.sortition_id, ix);

            if ix != 0 {
                stacks_blocks.push((
                    blinded_tip.sortition_id.clone(),
                    block.clone(),
                    blinded_tip.block_height,
                ));
            }

            if blinded_tip.winning_stacks_block_hash == block_hash {
                eprintln!("Preprocess {} (blind)", &block_hash);
                preprocess_block(&mut chainstate_blind, &sort_db_blind, &blinded_tip, block);
            } else {
                eprintln!("Will NOT preprocess {} (blind)", &block_hash);
            }

            // handle the stacks block
            coord_blind.handle_new_stacks_block().unwrap();
        }
    }

    // unblinded chain goes to burn block 30; blinded chain goes to burn block 29.
    // But, they share the same history.
    let tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn()).unwrap();
    let blinded_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db_blind.conn()).unwrap();

    assert_eq!(tip.block_height, 30);
    assert_eq!(blinded_tip.block_height, 29);

    let tip_29 = SortitionDB::get_ancestor_snapshot(
        &sort_db.index_conn(),
        blinded_tip.block_height,
        &tip.sortition_id,
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        tip_29.winning_stacks_block_hash,
        blinded_tip.winning_stacks_block_hash
    );
    assert_eq!(tip_29.burn_header_hash, blinded_tip.burn_header_hash);
    assert_eq!(tip_29.consensus_hash, blinded_tip.consensus_hash);

    let heaviest_am = coord.get_canonical_affirmation_map().unwrap();
    assert_eq!(heaviest_am, AffirmationMap::decode("apapap").unwrap());

    let block_height = eval_at_chain_tip(path, &sort_db, "block-height");
    assert_eq!(block_height, Value::UInt(11));

    // the blinded burnchain DB is doing just fine -- it even has the next Stacks block!
    let heaviest_am = coord_blind.get_canonical_affirmation_map().unwrap();
    assert_eq!(heaviest_am, AffirmationMap::decode("apapap").unwrap());

    let block_height_blind = eval_at_chain_tip(path_blinded, &sort_db_blind, "block-height");
    assert_eq!(block_height_blind, Value::UInt(12));

    let stacks_tip = SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db.conn()).unwrap();
    let stacks_tip_blind =
        SortitionDB::get_canonical_stacks_chain_tip_hash(sort_db_blind.conn()).unwrap();
    let stacks_tip_blind_11 = {
        let mut chainstate = get_chainstate(path_blinded);
        let mut tx = chainstate.index_tx_begin().unwrap();
        let hdr = StacksChainState::get_index_tip_ancestor(
            &mut tx,
            &StacksBlockHeader::make_index_block_hash(&stacks_tip_blind.0, &stacks_tip_blind.1),
            block_height.expect_u128() as u64,
        )
        .unwrap()
        .unwrap();
        (hdr.consensus_hash, hdr.anchored_header.block_hash())
    };

    assert_eq!(stacks_tip, stacks_tip_blind_11);

    // because of the affirmations, the canonical PoX ID deliberately omits anchor blocks
    {
        let ic = sort_db_blind.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "1101010");
    }
    {
        let ic = sort_db.index_handle_at_tip();
        let pox_id = ic.get_pox_id().unwrap();
        assert_eq!(&pox_id.to_string(), "1101010");
    }
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
            &b,
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
            &b,
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
    test_debug!(
        "Canonical chain tip at {} is {:?}",
        chainstate_path,
        &stacks_tip
    );
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
