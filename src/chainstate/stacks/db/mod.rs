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

use std::collections::{btree_map::Entry, BTreeMap};
use std::fmt;
use std::fs;
use std::io;
use std::io::prelude::*;
use std::ops::{Deref, DerefMut};
use std::path::{Path, PathBuf};

use rusqlite::types::ToSql;
use rusqlite::Connection;
use rusqlite::OpenFlags;
use rusqlite::Row;
use rusqlite::Transaction;
use rusqlite::NO_PARAMS;

use burnchains::bitcoin::address::BitcoinAddress;
use burnchains::{Address, Burnchain, BurnchainParameters, PoxConstants};
use chainstate::burn::db::sortdb::BlockHeaderCache;
use chainstate::burn::db::sortdb::*;
use chainstate::burn::db::sortdb::{SortitionDB, SortitionDBConn};
use chainstate::burn::ConsensusHash;
use chainstate::stacks::boot::*;
use chainstate::stacks::db::accounts::*;
use chainstate::stacks::db::blocks::*;
use chainstate::stacks::db::unconfirmed::UnconfirmedState;
use chainstate::stacks::events::*;
use chainstate::stacks::index::marf::{
    MarfConnection, BLOCK_HASH_TO_HEIGHT_MAPPING_KEY, BLOCK_HEIGHT_TO_HASH_MAPPING_KEY, MARF,
};
use chainstate::stacks::index::storage::TrieFileStorage;
use chainstate::stacks::index::MarfTrieId;
use chainstate::stacks::Error;
use chainstate::stacks::*;
use chainstate::stacks::{
    C32_ADDRESS_VERSION_MAINNET_MULTISIG, C32_ADDRESS_VERSION_MAINNET_SINGLESIG,
    C32_ADDRESS_VERSION_TESTNET_MULTISIG, C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
};
use clarity_vm::clarity::{
    ClarityBlockConnection, ClarityConnection, ClarityInstance, ClarityReadOnlyConnection,
    Error as clarity_error,
};
use core::*;
use net::atlas::BNS_CHARS_REGEX;
use net::Error as net_error;
use util::db::Error as db_error;
use util::db::{
    db_mkdirs, query_count, query_row, tx_begin_immediate, tx_busy_handler, DBConn, DBTx,
    FromColumn, FromRow, IndexDBConn, IndexDBTx,
};
use util::hash::to_hex;
use vm::analysis::analysis_db::AnalysisDatabase;
use vm::analysis::run_analysis;
use vm::ast::build_ast;
use vm::contexts::OwnedEnvironment;
use vm::costs::{ExecutionCost, LimitedCostTracker};
use vm::database::{
    BurnStateDB, ClarityDatabase, HeadersDB, STXBalance, SqliteConnection, NULL_BURN_STATE_DB,
};
use vm::representations::ClarityName;
use vm::representations::ContractName;
use vm::types::TupleData;
use {monitoring, util};

use crate::clarity_vm::database::marf::MarfedKV;
use crate::types::chainstate::{
    MARFValue, StacksAddress, StacksBlockHeader, StacksBlockId, StacksMicroblockHeader,
};
use crate::types::proof::{ClarityMarfTrieId, TrieHash};
use crate::util::boot::{boot_code_addr, boot_code_id};
use vm::Value;

pub mod accounts;
pub mod blocks;
pub mod contracts;
pub mod headers;
pub mod transactions;
pub mod unconfirmed;

lazy_static! {
    pub static ref TRANSACTION_LOG: bool =
        std::env::var("STACKS_TRANSACTION_LOG") == Ok("1".into());
}

pub struct StacksChainState {
    pub mainnet: bool,
    pub chain_id: u32,
    pub clarity_state: ClarityInstance,
    pub state_index: MARF<StacksBlockId>,
    pub blocks_path: String,
    pub clarity_state_index_path: String, // path to clarity MARF
    pub clarity_state_index_root: String, // path to dir containing clarity MARF and side-store
    pub root_path: String,
    pub block_limit: ExecutionCost,
    pub unconfirmed_state: Option<UnconfirmedState>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StacksAccount {
    pub principal: PrincipalData,
    pub nonce: u64,
    pub stx_balance: STXBalance,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MinerPaymentSchedule {
    pub address: StacksAddress,
    pub block_hash: BlockHeaderHash,
    pub consensus_hash: ConsensusHash,
    pub parent_block_hash: BlockHeaderHash,
    pub parent_consensus_hash: ConsensusHash,
    pub coinbase: u128,
    pub tx_fees_anchored: u128,
    pub tx_fees_streamed: u128,
    pub stx_burns: u128,
    pub burnchain_commit_burn: u64,
    pub burnchain_sortition_burn: u64,
    pub miner: bool, // is this a schedule payment for the block's miner?
    pub stacks_block_height: u64,
    pub vtxindex: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StacksHeaderInfo {
    pub anchored_header: StacksBlockHeader,
    pub microblock_tail: Option<StacksMicroblockHeader>,
    pub block_height: u64,
    pub index_root: TrieHash,
    pub consensus_hash: ConsensusHash,
    pub burn_header_hash: BurnchainHeaderHash,
    pub burn_header_height: u32,
    pub burn_header_timestamp: u64,
    pub anchored_block_size: u64,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MinerRewardInfo {
    pub from_block_consensus_hash: ConsensusHash,
    pub from_stacks_block_hash: BlockHeaderHash,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StacksEpochReceipt {
    pub header: StacksHeaderInfo,
    pub tx_receipts: Vec<StacksTransactionReceipt>,
    pub matured_rewards: Vec<MinerReward>,
    pub matured_rewards_info: Option<MinerRewardInfo>,
    pub parent_microblocks_cost: ExecutionCost,
    pub anchored_block_cost: ExecutionCost,
    pub parent_burn_block_hash: BurnchainHeaderHash,
    pub parent_burn_block_height: u32,
    pub parent_burn_block_timestamp: u64,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DBConfig {
    pub version: String,
    pub mainnet: bool,
    pub chain_id: u32,
}

impl StacksHeaderInfo {
    pub fn index_block_hash(&self) -> StacksBlockId {
        self.anchored_header.index_block_hash(&self.consensus_hash)
    }

    pub fn regtest_genesis() -> StacksHeaderInfo {
        let burnchain_params = BurnchainParameters::bitcoin_regtest();
        StacksHeaderInfo {
            anchored_header: StacksBlockHeader::genesis_block_header(),
            microblock_tail: None,
            block_height: 0,
            index_root: TrieHash([0u8; 32]),
            burn_header_hash: burnchain_params.first_block_hash.clone(),
            burn_header_height: burnchain_params.first_block_height as u32,
            consensus_hash: ConsensusHash::empty(),
            burn_header_timestamp: 0,
            anchored_block_size: 0,
        }
    }

    pub fn genesis(
        root_hash: TrieHash,
        first_burnchain_block_hash: &BurnchainHeaderHash,
        first_burnchain_block_height: u32,
        first_burnchain_block_timestamp: u64,
    ) -> StacksHeaderInfo {
        StacksHeaderInfo {
            anchored_header: StacksBlockHeader::genesis_block_header(),
            microblock_tail: None,
            block_height: 0,
            index_root: root_hash,
            burn_header_hash: first_burnchain_block_hash.clone(),
            burn_header_height: first_burnchain_block_height,
            consensus_hash: FIRST_BURNCHAIN_CONSENSUS_HASH.clone(),
            burn_header_timestamp: first_burnchain_block_timestamp,
            anchored_block_size: 0,
        }
    }

    pub fn is_first_mined(&self) -> bool {
        self.anchored_header.is_first_mined()
    }
}

impl FromRow<DBConfig> for DBConfig {
    fn from_row<'a>(row: &'a Row) -> Result<DBConfig, db_error> {
        let version: String = row.get_unwrap("version");
        let mainnet_i64: i64 = row.get_unwrap("mainnet");
        let chain_id_i64: i64 = row.get_unwrap("chain_id");

        let mainnet = mainnet_i64 != 0;
        let chain_id = chain_id_i64 as u32;

        Ok(DBConfig {
            version,
            mainnet,
            chain_id,
        })
    }
}

impl FromRow<StacksHeaderInfo> for StacksHeaderInfo {
    fn from_row<'a>(row: &'a Row) -> Result<StacksHeaderInfo, db_error> {
        let block_height = u64::from_column(row, "block_height")?;
        let index_root = TrieHash::from_column(row, "index_root")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;
        let burn_header_height = u64::from_column(row, "burn_header_height")? as u32;
        let burn_header_timestamp = u64::from_column(row, "burn_header_timestamp")?;
        let stacks_header = StacksBlockHeader::from_row(row)?;
        let anchored_block_size_str: String = row.get_unwrap("block_size");
        let anchored_block_size = anchored_block_size_str
            .parse::<u64>()
            .map_err(|_| db_error::ParseError)?;

        if block_height != stacks_header.total_work.work {
            return Err(db_error::ParseError);
        }

        Ok(StacksHeaderInfo {
            anchored_header: stacks_header,
            microblock_tail: None,
            block_height: block_height,
            index_root: index_root,
            consensus_hash: consensus_hash,
            burn_header_hash: burn_header_hash,
            burn_header_height: burn_header_height,
            burn_header_timestamp: burn_header_timestamp,
            anchored_block_size: anchored_block_size,
        })
    }
}

pub type StacksDBTx<'a> = IndexDBTx<'a, (), StacksBlockId>;
pub type StacksDBConn<'a> = IndexDBConn<'a, (), StacksBlockId>;

pub struct ClarityTx<'a> {
    block: ClarityBlockConnection<'a>,
    pub config: DBConfig,
}

impl ClarityConnection for ClarityTx<'_> {
    fn with_clarity_db_readonly_owned<F, R>(&mut self, to_do: F) -> R
    where
        F: FnOnce(ClarityDatabase) -> (R, ClarityDatabase),
    {
        ClarityConnection::with_clarity_db_readonly_owned(&mut self.block, to_do)
    }

    fn with_analysis_db_readonly<F, R>(&mut self, to_do: F) -> R
    where
        F: FnOnce(&mut AnalysisDatabase) -> R,
    {
        self.block.with_analysis_db_readonly(to_do)
    }
}

impl<'a> ClarityTx<'a> {
    pub fn get_root_hash(&mut self) -> TrieHash {
        self.block.get_root_hash()
    }

    pub fn cost_so_far(&self) -> ExecutionCost {
        self.block.cost_so_far()
    }

    /// Set the ClarityTx's cost tracker.
    /// Returns the replaced cost tracker.
    fn set_cost_tracker(&mut self, new_tracker: LimitedCostTracker) -> LimitedCostTracker {
        self.block.set_cost_tracker(new_tracker)
    }

    /// Run `todo` in this ClarityTx with `new_tracker`.
    /// Returns the result of `todo` and the `new_tracker`
    pub fn with_temporary_cost_tracker<F, R>(
        &mut self,
        new_tracker: LimitedCostTracker,
        todo: F,
    ) -> (R, LimitedCostTracker)
    where
        F: FnOnce(&mut ClarityTx) -> R,
    {
        let original_tracker = self.set_cost_tracker(new_tracker);
        let result = todo(self);
        let new_tracker = self.set_cost_tracker(original_tracker);
        (result, new_tracker)
    }

    #[cfg(test)]
    pub fn commit_block(self) -> () {
        self.block.commit_block();
    }

    pub fn commit_mined_block(self, block_hash: &StacksBlockId) -> ExecutionCost {
        self.block.commit_mined_block(block_hash).get_total()
    }

    pub fn commit_to_block(
        self,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> () {
        let index_block_hash = StacksBlockHeader::make_index_block_hash(consensus_hash, block_hash);
        self.block.commit_to_block(&index_block_hash);
    }

    pub fn commit_unconfirmed(self) -> () {
        self.block.commit_unconfirmed();
    }

    pub fn rollback_block(self) -> () {
        self.block.rollback_block()
    }

    pub fn rollback_unconfirmed(self) -> () {
        self.block.rollback_unconfirmed()
    }

    pub fn reset_cost(&mut self, cost: ExecutionCost) -> () {
        self.block.reset_block_cost(cost);
    }

    pub fn connection(&mut self) -> &mut ClarityBlockConnection<'a> {
        &mut self.block
    }

    pub fn increment_ustx_liquid_supply(&mut self, incr_by: u128) {
        self.connection()
            .as_transaction(|tx| {
                tx.with_clarity_db(|db| {
                    db.increment_ustx_liquid_supply(incr_by)
                        .map_err(|e| e.into())
                })
            })
            .expect("FATAL: `ust-liquid-supply` overflowed");
    }
}

pub struct ChainstateTx<'a> {
    pub config: DBConfig,
    pub blocks_path: String,
    pub tx: StacksDBTx<'a>,
    pub root_path: String,
}

impl<'a> ChainstateTx<'a> {
    pub fn new(
        tx: StacksDBTx<'a>,
        blocks_path: String,
        root_path: String,
        config: DBConfig,
    ) -> ChainstateTx<'a> {
        ChainstateTx {
            config,
            blocks_path,
            tx,
            root_path,
        }
    }

    pub fn get_blocks_path(&self) -> &String {
        &self.blocks_path
    }

    pub fn commit(self) -> Result<(), db_error> {
        self.tx.commit()
    }

    pub fn get_config(&self) -> &DBConfig {
        &self.config
    }

    pub fn log_transactions_processed(
        &self,
        block_id: &StacksBlockId,
        events: &[StacksTransactionReceipt],
    ) {
        if *TRANSACTION_LOG {
            let insert =
                "INSERT INTO transactions (txid, index_block_hash, tx_hex, result) VALUES (?, ?, ?, ?)";
            for tx_event in events.iter() {
                let txid = tx_event.transaction.txid();
                let tx_hex = to_hex(&tx_event.transaction.serialize_to_vec());
                let result = tx_event.result.to_string();
                let params: &[&dyn ToSql] = &[&txid, block_id, &tx_hex, &result];
                if let Err(e) = self.tx.tx().execute(insert, params) {
                    warn!("Failed to log TX: {}", e);
                }
            }
        }
        for tx_event in events.iter() {
            let txid = tx_event.transaction.txid();
            if let Err(e) = monitoring::log_transaction_processed(&txid, &self.root_path) {
                warn!("Failed to monitor TX processed: {:?}", e; "txid" => %txid);
            }
        }
    }
}

impl<'a> Deref for ChainstateTx<'a> {
    type Target = StacksDBTx<'a>;
    fn deref(&self) -> &StacksDBTx<'a> {
        &self.tx
    }
}

impl<'a> DerefMut for ChainstateTx<'a> {
    fn deref_mut(&mut self) -> &mut StacksDBTx<'a> {
        &mut self.tx
    }
}

/// Opaque structure for streaming block and microblock data from disk
#[derive(Debug, PartialEq, Clone)]
pub struct BlockStreamData {
    index_block_hash: StacksBlockId, // index block hash of the block to download
    rowid: Option<i64>,              // used when reading a blob out of staging
    offset: u64, // offset into whatever is being read (the blob, or the file in the chunk store)
    total_bytes: u64, // total number of bytes read.

    // used only for microblocks
    is_microblock: bool,
    microblock_hash: BlockHeaderHash,
    parent_index_block_hash: StacksBlockId,
    seq: u16, // only used for unconfirmed microblocks
    unconfirmed: bool,
    num_mblocks_buf: [u8; 4],
    num_mblocks_ptr: usize,
}

pub const CHAINSTATE_VERSION: &'static str = "1";

const CHAINSTATE_INITIAL_SCHEMA: &'static [&'static str] = &[
    "PRAGMA foreign_keys = ON;",
    r#"
    -- Anchored stacks block headers
    CREATE TABLE block_headers(
        version INTEGER NOT NULL,
        total_burn TEXT NOT NULL,       -- converted to/from u64
        total_work TEXT NOT NULL,       -- converted to/from u64
        proof TEXT NOT NULL,
        parent_block TEXT NOT NULL,             -- hash of parent Stacks block
        parent_microblock TEXT NOT NULL,
        parent_microblock_sequence INTEGER NOT NULL,
        tx_merkle_root TEXT NOT NULL,
        state_index_root TEXT NOT NULL,
        microblock_pubkey_hash TEXT NOT NULL,
        
        block_hash TEXT NOT NULL,                   -- NOTE: this is *not* unique, since two burn chain forks can commit to the same Stacks block.
        index_block_hash TEXT UNIQUE NOT NULL,      -- NOTE: this is the hash of the block hash and consensus hash of the burn block that selected it, 
                                                    -- and is guaranteed to be globally unique (across all Stacks forks and across all PoX forks).
                                                    -- index_block_hash is the block hash fed into the MARF index.

        -- internal use only
        block_height INTEGER NOT NULL,
        index_root TEXT NOT NULL,                    -- root hash of the internal, not-consensus-critical MARF that allows us to track chainstate /fork metadata
        consensus_hash TEXT UNIQUE NOT NULL,         -- all consensus hashes are guaranteed to be unique
        burn_header_hash TEXT NOT NULL,              -- burn header hash corresponding to the consensus hash (NOT guaranteed to be unique, since we can have 2+ blocks per burn block if there's a PoX fork)
        burn_header_height INT NOT NULL,             -- height of the burnchain block header that generated this consensus hash
        burn_header_timestamp INT NOT NULL,          -- timestamp from burnchain block header that generated this consensus hash
        parent_block_id TEXT NOT NULL,               -- NOTE: this is the parent index_block_hash

        cost TEXT NOT NULL,
        block_size TEXT NOT NULL,       -- converted to/from u64

        PRIMARY KEY(consensus_hash,block_hash)
    );"#,
    "CREATE INDEX index_block_hash_to_primary_key ON block_headers(index_block_hash,consensus_hash,block_hash);",
    "CREATE INDEX block_headers_hash_index ON block_headers(block_hash,block_height);",
    "CREATE INDEX block_index_hash_index ON block_headers(index_block_hash,consensus_hash,block_hash);",
    r#"
    -- scheduled payments
    -- no designated primary key since there can be duplicate entries
    CREATE TABLE payments(
        address TEXT NOT NULL,              -- miner that produced this block and microblock stream
        block_hash TEXT NOT NULL,
        consensus_hash TEXT NOT NULL,
        parent_block_hash TEXT NOT NULL,
        parent_consensus_hash TEXT NOT NULL,
        coinbase TEXT NOT NULL,             -- encodes u128
        tx_fees_anchored TEXT NOT NULL,     -- encodes u128
        tx_fees_streamed TEXT NOT NULL,     -- encodes u128
        stx_burns TEXT NOT NULL,            -- encodes u128
        burnchain_commit_burn INT NOT NULL,
        burnchain_sortition_burn INT NOT NULL,
        miner INT NOT NULL,
        
        -- internal use
        stacks_block_height INTEGER NOT NULL,
        index_block_hash TEXT NOT NULL,     -- NOTE: can't enforce UNIQUE here, because there will be multiple entries per block
        vtxindex INT NOT NULL               -- user burn support vtxindex
    );"#,
    r#"
    -- users who supported miners
    CREATE TABLE user_supporters(
        address TEXT NOT NULL,
        support_burn INT NOT NULL,
        block_hash TEXT NOT NULL,
        consensus_hash TEXT NOT NULL,

        PRIMARY KEY(address,block_hash,consensus_hash)
    );"#,
    r#"
    CREATE TABLE db_config(
        version TEXT NOT NULL,
        mainnet INTEGER NOT NULL,
        chain_id INTEGER NOT NULL
    );"#,
    r#"
    -- Staging microblocks -- preprocessed microblocks queued up for subsequent processing and inclusion in the chunk store.
    CREATE TABLE staging_microblocks(anchored_block_hash TEXT NOT NULL,     -- this is the hash of the parent anchored block
                                     consensus_hash TEXT NOT NULL,          -- this is the hash of the burn chain block that holds the parent anchored block's block-commit
                                     index_block_hash TEXT NOT NULL,        -- this is the anchored block's index hash
                                     microblock_hash TEXT NOT NULL,
                                     parent_hash TEXT NOT NULL,             -- previous microblock
                                     index_microblock_hash TEXT NOT NULL,   -- this is the hash of consensus_hash and microblock_hash
                                     sequence INT NOT NULL,
                                     processed INT NOT NULL,
                                     orphaned INT NOT NULL,
                                     PRIMARY KEY(anchored_block_hash,consensus_hash,microblock_hash)
    );"#,
    "CREATE INDEX staging_microblocks_index_hash ON staging_microblocks(index_block_hash);",
    r#"
    -- Staging microblocks data
    CREATE TABLE staging_microblocks_data(block_hash TEXT NOT NULL,
                                          block_data BLOB NOT NULL,
                                          PRIMARY KEY(block_hash)
    );"#,
    r#"
    -- Invalidated staging microblocks data
    CREATE TABLE invalidated_microblocks_data(block_hash TEXT NOT NULL,
                                              block_data BLOB NOT NULL,
                                              PRIMARY KEY(block_hash)
    );"#,
    r#"
    -- Staging blocks -- preprocessed blocks queued up for subsequent processing and inclusion in the chunk store.
    CREATE TABLE staging_blocks(anchored_block_hash TEXT NOT NULL,
                                parent_anchored_block_hash TEXT NOT NULL,
                                consensus_hash TEXT NOT NULL,
                                -- parent_consensus_hash is the consensus hash of the parent sortition of the sortition that chose this block
                                parent_consensus_hash TEXT NOT NULL,
                                parent_microblock_hash TEXT NOT NULL,
                                parent_microblock_seq INT NOT NULL,
                                microblock_pubkey_hash TEXT NOT NULL,
                                height INT NOT NULL,
                                attachable INT NOT NULL,            -- set to 1 if this block's parent is processed; 0 if not
                                orphaned INT NOT NULL,              -- set to 1 if this block can never be attached
                                processed INT NOT NULL,
                                commit_burn INT NOT NULL,
                                sortition_burn INT NOT NULL,
                                index_block_hash TEXT NOT NULL,           -- used internally; hash of consensus hash and block header
                                download_time INT NOT NULL,               -- how long the block was in-flight
                                arrival_time INT NOT NULL,                -- when this block was stored
                                processed_time INT NOT NULL,              -- when this block was processed
                                PRIMARY KEY(anchored_block_hash,consensus_hash)
    );"#,
    "CREATE INDEX processed_stacks_blocks ON staging_blocks(processed,anchored_block_hash,consensus_hash);",
    "CREATE INDEX orphaned_stacks_blocks ON staging_blocks(orphaned,anchored_block_hash,consensus_hash);",
    "CREATE INDEX parent_blocks ON staging_blocks(parent_anchored_block_hash);",
    "CREATE INDEX parent_consensus_hashes ON staging_blocks(parent_consensus_hash);",
    "CREATE INDEX index_block_hashes ON staging_blocks(index_block_hash);",
    r#"
    -- users who burned in support of a block
    CREATE TABLE staging_user_burn_support(anchored_block_hash TEXT NOT NULL,
                                           consensus_hash TEXT NOT NULL,
                                           address TEXT NOT NULL,
                                           burn_amount INT NOT NULL,
                                           vtxindex INT NOT NULL
    );"#,
    r#"
    CREATE TABLE transactions(
        id INTEGER PRIMARY KEY,
        txid TEXT NOT NULL,
        index_block_hash TEXT NOT NULL,
        tx_hex TEXT NOT NULL,
        result TEXT NOT NULL,
        UNIQUE (txid,index_block_hash)
    );"#,
    "CREATE INDEX txid_tx_index ON transactions(txid);",
    "CREATE INDEX index_block_hash_tx_index ON transactions(index_block_hash);",
];

#[cfg(test)]
pub const MINER_REWARD_MATURITY: u64 = 2; // small for testing purposes

#[cfg(not(test))]
pub const MINER_REWARD_MATURITY: u64 = 100;

pub const MINER_FEE_MINIMUM_BLOCK_USAGE: u64 = 80; // miner must share the first F% of the anchored block tx fees, and gets 100% - F% exclusively

pub const MINER_FEE_WINDOW: u64 = 24; // number of blocks (B) used to smooth over the fraction of tx fees they share from anchored blocks

// fraction (out of 100) of the coinbase a user will receive for reporting a microblock stream fork
pub const POISON_MICROBLOCK_COMMISSION_FRACTION: u128 = 5;

#[derive(Debug, Clone)]
pub struct ChainstateAccountBalance {
    pub address: String,
    pub amount: u64,
}

#[derive(Debug, Clone)]
pub struct ChainstateAccountLockup {
    pub address: String,
    pub amount: u64,
    pub block_height: u64,
}

#[derive(Debug, Clone)]
pub struct ChainstateBNSNamespace {
    pub namespace_id: String,
    pub importer: String,
    pub buckets: String,
    pub base: u64,
    pub coeff: u64,
    pub nonalpha_discount: u64,
    pub no_vowel_discount: u64,
    pub lifetime: u64,
}

#[derive(Debug, Clone)]
pub struct ChainstateBNSName {
    pub fully_qualified_name: String,
    pub owner: String,
    pub zonefile_hash: String,
}

impl ChainstateAccountLockup {
    pub fn new(address: StacksAddress, amount: u64, block_height: u64) -> ChainstateAccountLockup {
        ChainstateAccountLockup {
            address: address.to_string(),
            amount,
            block_height,
        }
    }
}

pub struct ChainStateBootData {
    pub first_burnchain_block_hash: BurnchainHeaderHash,
    pub first_burnchain_block_height: u32,
    pub first_burnchain_block_timestamp: u32,
    pub initial_balances: Vec<(PrincipalData, u64)>,
    pub pox_constants: PoxConstants,
    pub post_flight_callback: Option<Box<dyn FnOnce(&mut ClarityTx) -> ()>>,
    pub get_bulk_initial_lockups:
        Option<Box<dyn FnOnce() -> Box<dyn Iterator<Item = ChainstateAccountLockup>>>>,
    pub get_bulk_initial_balances:
        Option<Box<dyn FnOnce() -> Box<dyn Iterator<Item = ChainstateAccountBalance>>>>,
    pub get_bulk_initial_namespaces:
        Option<Box<dyn FnOnce() -> Box<dyn Iterator<Item = ChainstateBNSNamespace>>>>,
    pub get_bulk_initial_names:
        Option<Box<dyn FnOnce() -> Box<dyn Iterator<Item = ChainstateBNSName>>>>,
}

impl ChainStateBootData {
    pub fn new(
        burnchain: &Burnchain,
        initial_balances: Vec<(PrincipalData, u64)>,
        post_flight_callback: Option<Box<dyn FnOnce(&mut ClarityTx) -> ()>>,
    ) -> ChainStateBootData {
        ChainStateBootData {
            first_burnchain_block_hash: burnchain.first_block_hash.clone(),
            first_burnchain_block_height: burnchain.first_block_height as u32,
            first_burnchain_block_timestamp: burnchain.first_block_timestamp,
            initial_balances,
            pox_constants: burnchain.pox_constants.clone(),
            post_flight_callback,
            get_bulk_initial_lockups: None,
            get_bulk_initial_balances: None,
            get_bulk_initial_namespaces: None,
            get_bulk_initial_names: None,
        }
    }
}

impl StacksChainState {
    fn instantiate_db(
        mainnet: bool,
        chain_id: u32,
        marf_path: &str,
    ) -> Result<MARF<StacksBlockId>, Error> {
        let mut marf = StacksChainState::open_index(marf_path)?;
        let mut dbtx = StacksDBTx::new(&mut marf, ());

        {
            let tx = dbtx.tx();

            for cmd in CHAINSTATE_INITIAL_SCHEMA {
                tx.execute_batch(cmd)?;
            }

            tx.execute(
                "INSERT INTO db_config (version,mainnet,chain_id) VALUES (?1,?2,?3)",
                &[
                    &CHAINSTATE_VERSION,
                    &(if mainnet { 1 } else { 0 }) as &dyn ToSql,
                    &chain_id as &dyn ToSql,
                ],
            )?;
        }

        dbtx.instantiate_index()?;
        dbtx.commit()?;
        Ok(marf)
    }

    fn open_db(
        mainnet: bool,
        chain_id: u32,
        index_path: &str,
    ) -> Result<MARF<StacksBlockId>, Error> {
        let create_flag = fs::metadata(index_path).is_err();

        if create_flag {
            // instantiate!
            StacksChainState::instantiate_db(mainnet, chain_id, index_path)
        } else {
            let marf = StacksChainState::open_index(index_path)?;
            // sanity check
            let db_config = query_row::<DBConfig, _>(
                marf.sqlite_conn(),
                &"SELECT * FROM db_config LIMIT 1".to_string(),
                NO_PARAMS,
            )?
            .expect("CORRUPTION: no db_config found");

            if db_config.mainnet != mainnet {
                error!(
                    "Invalid chain state database: expected mainnet = {}, got {}",
                    mainnet, db_config.mainnet
                );
                return Err(Error::InvalidChainstateDB);
            }

            if db_config.version != CHAINSTATE_VERSION {
                error!(
                    "Invalid chain state database: expected version = {}, got {}",
                    CHAINSTATE_VERSION, db_config.version
                );
                return Err(Error::InvalidChainstateDB);
            }

            if db_config.chain_id != chain_id {
                error!(
                    "Invalid chain ID: expected {}, got {}",
                    chain_id, db_config.chain_id
                );
                return Err(Error::InvalidChainstateDB);
            }

            Ok(marf)
        }
    }

    pub fn open_index(marf_path: &str) -> Result<MARF<StacksBlockId>, Error> {
        test_debug!("Open MARF index at {}", marf_path);
        let marf =
            MARF::from_path(marf_path).map_err(|e| Error::DBError(db_error::IndexError(e)))?;
        Ok(marf)
    }

    /// Idempotent `mkdir -p`
    fn mkdirs(path: &PathBuf) -> Result<(), Error> {
        match fs::metadata(path) {
            Ok(md) => {
                if !md.is_dir() {
                    error!("Not a directory: {:?}", path);
                    return Err(Error::DBError(db_error::ExistsError));
                }
                Ok(())
            }
            Err(e) => {
                if e.kind() != io::ErrorKind::NotFound {
                    return Err(Error::DBError(db_error::IOError(e)));
                }
                fs::create_dir_all(path).map_err(|e| Error::DBError(db_error::IOError(e)))
            }
        }
    }

    fn parse_genesis_address(addr: &str, mainnet: bool) -> PrincipalData {
        // Typical entries are BTC encoded addresses that need converted to STX
        let mut stacks_address = match BitcoinAddress::from_b58(&addr) {
            Ok(addr) => StacksAddress::from_bitcoin_address(&addr),
            // A few addresses (from legacy placeholder accounts) are already STX addresses
            _ => match StacksAddress::from_string(addr) {
                Some(addr) => addr,
                None => panic!("Failed to parsed genesis address {}", addr),
            },
        };
        // Convert a given address to the currently running network mode (mainnet vs testnet).
        // All addresses from the Stacks 1.0 import data should be mainnet, but we'll handle either case.
        stacks_address.version = if mainnet {
            match stacks_address.version {
                C32_ADDRESS_VERSION_TESTNET_SINGLESIG => C32_ADDRESS_VERSION_MAINNET_SINGLESIG,
                C32_ADDRESS_VERSION_TESTNET_MULTISIG => C32_ADDRESS_VERSION_MAINNET_MULTISIG,
                _ => stacks_address.version,
            }
        } else {
            match stacks_address.version {
                C32_ADDRESS_VERSION_MAINNET_SINGLESIG => C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
                C32_ADDRESS_VERSION_MAINNET_MULTISIG => C32_ADDRESS_VERSION_TESTNET_MULTISIG,
                _ => stacks_address.version,
            }
        };
        let principal: PrincipalData = stacks_address.into();
        return principal;
    }

    /// Install the boot code into the chain history.
    fn install_boot_code(
        chainstate: &mut StacksChainState,
        mainnet: bool,
        boot_data: &mut ChainStateBootData,
    ) -> Result<Vec<StacksTransactionReceipt>, Error> {
        info!("Building genesis block");

        let tx_version = if mainnet {
            TransactionVersion::Mainnet
        } else {
            TransactionVersion::Testnet
        };

        let boot_code_address = boot_code_addr(mainnet);

        let boot_code_auth = TransactionAuth::Standard(TransactionSpendingCondition::Singlesig(
            SinglesigSpendingCondition {
                signer: boot_code_address.bytes.clone(),
                hash_mode: SinglesigHashMode::P2PKH,
                key_encoding: TransactionPublicKeyEncoding::Uncompressed,
                nonce: 0,
                tx_fee: 0,
                signature: MessageSignature::empty(),
            },
        ));

        let mut boot_code_account = StacksAccount {
            principal: PrincipalData::Standard(boot_code_address.into()),
            nonce: 0,
            stx_balance: STXBalance::zero(),
        };

        let mut initial_liquid_ustx = 0u128;
        let mut receipts = vec![];

        {
            let mut clarity_tx = chainstate.genesis_block_begin(
                &NULL_BURN_STATE_DB,
                &BURNCHAIN_BOOT_CONSENSUS_HASH,
                &BOOT_BLOCK_HASH,
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            );
            let boot_code = if mainnet {
                *boot::STACKS_BOOT_CODE_MAINNET
            } else {
                *boot::STACKS_BOOT_CODE_TESTNET
            };
            for (boot_code_name, boot_code_contract) in boot_code.iter() {
                debug!(
                    "Instantiate boot code contract '{}' ({} bytes)...",
                    boot_code_name,
                    boot_code_contract.len()
                );

                let smart_contract = TransactionPayload::SmartContract(TransactionSmartContract {
                    name: ContractName::try_from(boot_code_name.to_string())
                        .expect("FATAL: invalid boot-code contract name"),
                    code_body: StacksString::from_str(boot_code_contract)
                        .expect("FATAL: invalid boot code body"),
                });

                let boot_code_smart_contract = StacksTransaction::new(
                    tx_version.clone(),
                    boot_code_auth.clone(),
                    smart_contract,
                );

                let tx_receipt = clarity_tx.connection().as_transaction(|clarity| {
                    StacksChainState::process_transaction_payload(
                        clarity,
                        &boot_code_smart_contract,
                        &boot_code_account,
                    )
                })?;
                receipts.push(tx_receipt);

                boot_code_account.nonce += 1;
            }

            let mut allocation_events: Vec<StacksTransactionEvent> = vec![];
            if boot_data.initial_balances.len() > 0 {
                warn!(
                    "Seeding {} balances coming from the config",
                    boot_data.initial_balances.len()
                );
            }
            for (address, amount) in boot_data.initial_balances.iter() {
                clarity_tx.connection().as_transaction(|clarity| {
                    StacksChainState::account_genesis_credit(clarity, address, (*amount).into())
                });
                initial_liquid_ustx = initial_liquid_ustx
                    .checked_add(*amount as u128)
                    .expect("FATAL: liquid STX overflow");
                let mint_event = StacksTransactionEvent::STXEvent(STXEventType::STXMintEvent(
                    STXMintEventData {
                        recipient: address.clone(),
                        amount: *amount as u128,
                    },
                ));
                allocation_events.push(mint_event);
            }

            clarity_tx.connection().as_transaction(|clarity| {
                // Balances
                if let Some(get_balances) = boot_data.get_bulk_initial_balances.take() {
                    info!("Importing accounts from Stacks 1.0");
                    let mut balances_count = 0;
                    let initial_balances = get_balances();
                    for balance in initial_balances {
                        balances_count = balances_count + 1;
                        let stx_address =
                            StacksChainState::parse_genesis_address(&balance.address, mainnet);
                        StacksChainState::account_genesis_credit(
                            clarity,
                            &stx_address,
                            balance.amount.into(),
                        );
                        initial_liquid_ustx = initial_liquid_ustx
                            .checked_add(balance.amount as u128)
                            .expect("FATAL: liquid STX overflow");
                        let mint_event = StacksTransactionEvent::STXEvent(
                            STXEventType::STXMintEvent(STXMintEventData {
                                recipient: stx_address,
                                amount: balance.amount.into(),
                            }),
                        );
                        allocation_events.push(mint_event);
                    }
                    info!("Seeding {} balances coming from chain dump", balances_count);
                }

                // Lockups
                if let Some(get_schedules) = boot_data.get_bulk_initial_lockups.take() {
                    info!("Initializing chain with lockups");
                    let mut lockups_per_block: BTreeMap<u64, Vec<Value>> = BTreeMap::new();
                    let initial_lockups = get_schedules();
                    for schedule in initial_lockups {
                        let stx_address =
                            StacksChainState::parse_genesis_address(&schedule.address, mainnet);
                        let value = Value::Tuple(
                            TupleData::from_data(vec![
                                ("recipient".into(), Value::Principal(stx_address)),
                                ("amount".into(), Value::UInt(schedule.amount.into())),
                            ])
                            .unwrap(),
                        );
                        match lockups_per_block.entry(schedule.block_height) {
                            Entry::Occupied(schedules) => {
                                schedules.into_mut().push(value);
                            }
                            Entry::Vacant(entry) => {
                                let schedules = vec![value];
                                entry.insert(schedules);
                            }
                        };
                    }

                    let lockup_contract_id = boot_code_id("lockup", mainnet);
                    clarity
                        .with_clarity_db(|db| {
                            for (block_height, schedule) in lockups_per_block.into_iter() {
                                let key = Value::UInt(block_height.into());
                                let value = Value::list_from(schedule).unwrap();
                                db.insert_entry_unknown_descriptor(
                                    &lockup_contract_id,
                                    "lockups",
                                    key,
                                    value,
                                )?;
                            }
                            Ok(())
                        })
                        .unwrap();
                }

                // BNS Namespace
                let bns_contract_id = boot_code_id("bns", mainnet);
                if let Some(get_namespaces) = boot_data.get_bulk_initial_namespaces.take() {
                    info!("Initializing chain with namespaces");
                    clarity
                        .with_clarity_db(|db| {
                            let initial_namespaces = get_namespaces();
                            for entry in initial_namespaces {
                                let namespace = {
                                    if !BNS_CHARS_REGEX.is_match(&entry.namespace_id) {
                                        panic!("Invalid namespace characters");
                                    }
                                    let buffer = entry.namespace_id.as_bytes();
                                    Value::buff_from(buffer.to_vec()).expect("Invalid namespace")
                                };

                                let importer = {
                                    let address = StacksChainState::parse_genesis_address(
                                        &entry.importer,
                                        mainnet,
                                    );
                                    Value::Principal(address)
                                };

                                let revealed_at = Value::UInt(0);
                                let launched_at = Value::UInt(0);
                                let lifetime = Value::UInt(entry.lifetime.into());
                                let price_function = {
                                    let base = Value::UInt(entry.base.into());
                                    let coeff = Value::UInt(entry.coeff.into());
                                    let nonalpha_discount =
                                        Value::UInt(entry.nonalpha_discount.into());
                                    let no_vowel_discount =
                                        Value::UInt(entry.no_vowel_discount.into());
                                    let buckets: Vec<_> = entry
                                        .buckets
                                        .split(";")
                                        .map(|e| Value::UInt(e.parse::<u64>().unwrap().into()))
                                        .collect();
                                    assert_eq!(buckets.len(), 16);

                                    TupleData::from_data(vec![
                                        ("buckets".into(), Value::list_from(buckets).unwrap()),
                                        ("base".into(), base),
                                        ("coeff".into(), coeff),
                                        ("nonalpha-discount".into(), nonalpha_discount),
                                        ("no-vowel-discount".into(), no_vowel_discount),
                                    ])
                                    .unwrap()
                                };

                                let namespace_props = Value::Tuple(
                                    TupleData::from_data(vec![
                                        ("revealed-at".into(), revealed_at),
                                        ("launched-at".into(), Value::some(launched_at).unwrap()),
                                        ("lifetime".into(), lifetime),
                                        ("namespace-import".into(), importer),
                                        ("can-update-price-function".into(), Value::Bool(true)),
                                        ("price-function".into(), Value::Tuple(price_function)),
                                    ])
                                    .unwrap(),
                                );

                                db.insert_entry_unknown_descriptor(
                                    &bns_contract_id,
                                    "namespaces",
                                    namespace,
                                    namespace_props,
                                )?;
                            }
                            Ok(())
                        })
                        .unwrap();
                }

                // BNS Names
                if let Some(get_names) = boot_data.get_bulk_initial_names.take() {
                    info!("Initializing chain with names");
                    clarity
                        .with_clarity_db(|db| {
                            let initial_names = get_names();
                            for entry in initial_names {
                                let components: Vec<_> =
                                    entry.fully_qualified_name.split(".").collect();
                                assert_eq!(components.len(), 2);

                                let namespace = {
                                    let namespace_str = components[1];
                                    if !BNS_CHARS_REGEX.is_match(&namespace_str) {
                                        panic!("Invalid namespace characters");
                                    }
                                    let buffer = namespace_str.as_bytes();
                                    Value::buff_from(buffer.to_vec()).expect("Invalid namespace")
                                };

                                let name = {
                                    let name_str = components[0].to_string();
                                    if !BNS_CHARS_REGEX.is_match(&name_str) {
                                        panic!("Invalid name characters");
                                    }
                                    let buffer = name_str.as_bytes();
                                    Value::buff_from(buffer.to_vec()).expect("Invalid name")
                                };

                                let fqn = Value::Tuple(
                                    TupleData::from_data(vec![
                                        ("namespace".into(), namespace),
                                        ("name".into(), name),
                                    ])
                                    .unwrap(),
                                );

                                let owner_address =
                                    StacksChainState::parse_genesis_address(&entry.owner, mainnet);

                                let zonefile_hash = {
                                    if entry.zonefile_hash.len() == 0 {
                                        Value::buff_from(vec![]).unwrap()
                                    } else {
                                        let buffer = Hash160::from_hex(&entry.zonefile_hash)
                                            .expect("Invalid zonefile_hash");
                                        Value::buff_from(buffer.to_bytes().to_vec()).unwrap()
                                    }
                                };

                                let expected_asset_type =
                                    db.get_nft_key_type(&bns_contract_id, "names")?;
                                db.set_nft_owner(
                                    &bns_contract_id,
                                    "names",
                                    &fqn,
                                    &owner_address,
                                    &expected_asset_type,
                                )?;

                                let registered_at = Value::UInt(0);
                                let name_props = Value::Tuple(
                                    TupleData::from_data(vec![
                                        (
                                            "registered-at".into(),
                                            Value::some(registered_at).unwrap(),
                                        ),
                                        ("imported-at".into(), Value::none()),
                                        ("revoked-at".into(), Value::none()),
                                        ("zonefile-hash".into(), zonefile_hash),
                                    ])
                                    .unwrap(),
                                );

                                db.insert_entry_unknown_descriptor(
                                    &bns_contract_id,
                                    "name-properties",
                                    fqn.clone(),
                                    name_props,
                                )?;

                                db.insert_entry_unknown_descriptor(
                                    &bns_contract_id,
                                    "owner-name",
                                    Value::Principal(owner_address),
                                    fqn,
                                )?;
                            }
                            Ok(())
                        })
                        .unwrap();
                }
                info!("Saving Genesis block. This could take a while");
            });

            let allocations_tx = StacksTransaction::new(
                tx_version.clone(),
                boot_code_auth,
                TransactionPayload::TokenTransfer(
                    PrincipalData::Standard(boot_code_address.into()),
                    0,
                    TokenTransferMemo([0u8; 34]),
                ),
            );
            let allocations_receipt = StacksTransactionReceipt::from_stx_transfer(
                allocations_tx,
                allocation_events,
                Value::okay_true(),
                ExecutionCost::zero(),
            );
            receipts.push(allocations_receipt);

            if let Some(callback) = boot_data.post_flight_callback.take() {
                callback(&mut clarity_tx);
            }

            // Setup burnchain parameters for pox contract
            let pox_constants = &boot_data.pox_constants;
            let contract = util::boot::boot_code_id("pox", mainnet);
            let sender = PrincipalData::from(contract.clone());
            let params = vec![
                Value::UInt(boot_data.first_burnchain_block_height as u128),
                Value::UInt(pox_constants.prepare_length as u128),
                Value::UInt(pox_constants.reward_cycle_length as u128),
                Value::UInt(pox_constants.pox_rejection_fraction as u128),
            ];
            clarity_tx.connection().as_transaction(|conn| {
                conn.run_contract_call(
                    &sender,
                    &contract,
                    "set-burnchain-parameters",
                    &params,
                    |_, _| false,
                )
                .expect("Failed to set burnchain parameters in PoX contract");
            });

            clarity_tx
                .connection()
                .as_transaction(|tx| {
                    tx.with_clarity_db(|db| {
                        db.increment_ustx_liquid_supply(initial_liquid_ustx)
                            .map_err(|e| e.into())
                    })
                })
                .expect("FATAL: `ustx-liquid-supply` overflowed");

            clarity_tx.commit_to_block(&FIRST_BURNCHAIN_CONSENSUS_HASH, &FIRST_STACKS_BLOCK_HASH);
        }

        // verify that genesis root hash is as expected
        {
            let genesis_root_hash = chainstate.clarity_state.with_marf(|marf| {
                let index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &FIRST_BURNCHAIN_CONSENSUS_HASH,
                    &FIRST_STACKS_BLOCK_HASH,
                );
                marf.get_root_hash_at(&index_block_hash).unwrap()
            });

            info!("Computed Clarity state genesis"; "root_hash" => %genesis_root_hash);

            if mainnet {
                assert_eq!(
                    &genesis_root_hash.to_string(),
                    MAINNET_2_0_GENESIS_ROOT_HASH,
                    "Incorrect root hash for genesis block computed. expected={} computed={}",
                    MAINNET_2_0_GENESIS_ROOT_HASH,
                    genesis_root_hash.to_string()
                )
            }
        }

        {
            // add a block header entry for the boot code
            let mut tx = chainstate.index_tx_begin()?;
            let parent_hash = StacksBlockId::sentinel();
            let first_index_hash = StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            );

            test_debug!(
                "Boot code headers index_put_begin {}-{}",
                &parent_hash,
                &first_index_hash
            );

            tx.put_indexed_begin(&parent_hash, &first_index_hash)?;
            let first_root_hash = tx.put_indexed_all(&vec![], &vec![])?;

            test_debug!(
                "Boot code headers index_commit {}-{}",
                &parent_hash,
                &first_index_hash
            );

            let first_tip_info = StacksHeaderInfo::genesis(
                first_root_hash,
                &boot_data.first_burnchain_block_hash,
                boot_data.first_burnchain_block_height,
                boot_data.first_burnchain_block_timestamp as u64,
            );

            StacksChainState::insert_stacks_block_header(
                &mut tx,
                &parent_hash,
                &first_tip_info,
                &ExecutionCost::zero(),
            )?;
            tx.commit()?;
        }

        debug!("Finish install boot code");
        Ok(receipts)
    }

    pub fn open(
        mainnet: bool,
        chain_id: u32,
        path_str: &str,
    ) -> Result<(StacksChainState, Vec<StacksTransactionReceipt>), Error> {
        StacksChainState::open_and_exec(
            mainnet,
            chain_id,
            path_str,
            None,
            ExecutionCost::max_value(),
        )
    }

    /// Re-open the chainstate -- i.e. to get a new handle to it using an existing chain state's
    /// parameters
    pub fn reopen(&self) -> Result<(StacksChainState, Vec<StacksTransactionReceipt>), Error> {
        StacksChainState::open(self.mainnet, self.chain_id, &self.root_path)
    }

    /// Re-open the chainstate -- i.e. to get a new handle to it using an existing chain state's
    /// parameters, but with a block limit
    pub fn reopen_limited(
        &self,
        budget: ExecutionCost,
    ) -> Result<(StacksChainState, Vec<StacksTransactionReceipt>), Error> {
        StacksChainState::open_and_exec(self.mainnet, self.chain_id, &self.root_path, None, budget)
    }

    pub fn open_testnet<F>(
        chain_id: u32,
        path_str: &str,
        boot_data: Option<&mut ChainStateBootData>,
        block_limit: ExecutionCost,
    ) -> Result<(StacksChainState, Vec<StacksTransactionReceipt>), Error> {
        StacksChainState::open_and_exec(false, chain_id, path_str, boot_data, block_limit)
    }

    pub fn open_with_block_limit(
        mainnet: bool,
        chain_id: u32,
        path_str: &str,
        block_limit: ExecutionCost,
    ) -> Result<(StacksChainState, Vec<StacksTransactionReceipt>), Error> {
        StacksChainState::open_and_exec(mainnet, chain_id, path_str, None, block_limit)
    }

    pub fn open_and_exec(
        mainnet: bool,
        chain_id: u32,
        path_str: &str,
        boot_data: Option<&mut ChainStateBootData>,
        block_limit: ExecutionCost,
    ) -> Result<(StacksChainState, Vec<StacksTransactionReceipt>), Error> {
        let path = PathBuf::from(path_str);

        StacksChainState::mkdirs(&path)?;

        let mut blocks_path = path.clone();

        blocks_path.push("blocks");
        StacksChainState::mkdirs(&blocks_path)?;

        let blocks_path_root = blocks_path
            .to_str()
            .ok_or_else(|| Error::DBError(db_error::ParseError))?
            .to_string();

        let mut state_path = path;

        state_path.push("vm");
        StacksChainState::mkdirs(&state_path)?;

        state_path.push("clarity");
        let clarity_state_index_root = state_path
            .to_str()
            .ok_or_else(|| Error::DBError(db_error::ParseError))?
            .to_string();

        state_path.push("marf.sqlite");
        let clarity_state_index_marf = state_path
            .to_str()
            .ok_or_else(|| Error::DBError(db_error::ParseError))?
            .to_string();

        state_path.pop();
        state_path.pop();

        state_path.push("index.sqlite");
        let header_index_root = state_path
            .to_str()
            .ok_or_else(|| Error::DBError(db_error::ParseError))?
            .to_string();

        let init_required = match fs::metadata(&clarity_state_index_marf) {
            Ok(_) => false,
            Err(_) => true,
        };

        let state_index = StacksChainState::open_db(mainnet, chain_id, &header_index_root)?;

        let vm_state = MarfedKV::open(
            &clarity_state_index_root,
            Some(&StacksBlockHeader::make_index_block_hash(
                &MINER_BLOCK_CONSENSUS_HASH,
                &MINER_BLOCK_HEADER_HASH,
            )),
        )
        .map_err(|e| Error::ClarityError(e.into()))?;

        let clarity_state = ClarityInstance::new(mainnet, vm_state, block_limit.clone());

        let mut chainstate = StacksChainState {
            mainnet: mainnet,
            chain_id: chain_id,
            clarity_state: clarity_state,
            state_index: state_index,
            blocks_path: blocks_path_root,
            clarity_state_index_path: clarity_state_index_marf,
            clarity_state_index_root: clarity_state_index_root,
            root_path: path_str.to_string(),
            block_limit: block_limit,
            unconfirmed_state: None,
        };

        let mut receipts = vec![];
        match (init_required, boot_data) {
            (true, Some(boot_data)) => {
                let mut res =
                    StacksChainState::install_boot_code(&mut chainstate, mainnet, boot_data)?;
                receipts.append(&mut res);
            }
            (true, None) => {
                panic!(
                    "StacksChainState initialization is required, but boot_data was not passed."
                );
            }
            (false, _) => {}
        }

        Ok((chainstate, receipts))
    }

    pub fn config(&self) -> DBConfig {
        DBConfig {
            mainnet: self.mainnet,
            chain_id: self.chain_id,
            version: CHAINSTATE_VERSION.to_string(),
        }
    }

    /// Begin a transaction against the (indexed) stacks chainstate DB.
    /// Does not create a Clarity instance.
    pub fn index_tx_begin<'a>(&'a mut self) -> Result<StacksDBTx<'a>, Error> {
        Ok(StacksDBTx::new(&mut self.state_index, ()))
    }

    pub fn index_conn<'a>(&'a self) -> Result<StacksDBConn<'a>, Error> {
        Ok(StacksDBConn::new(&self.state_index, ()))
    }

    /// Begin a transaction against the underlying DB
    /// Does not create a Clarity instance, and does not affect the MARF.
    pub fn db_tx_begin<'a>(&'a mut self) -> Result<DBTx<'a>, Error> {
        self.state_index.storage_tx().map_err(Error::DBError)
    }

    /// Simultaneously begin a transaction against both the headers and blocks.
    /// Used when considering a new block to append the chain state.
    pub fn chainstate_tx_begin<'a>(
        &'a mut self,
    ) -> Result<(ChainstateTx<'a>, &'a mut ClarityInstance), Error> {
        let config = self.config();
        let blocks_path = self.blocks_path.clone();
        let clarity_instance = &mut self.clarity_state;
        let inner_tx = StacksDBTx::new(&mut self.state_index, ());

        let chainstate_tx =
            ChainstateTx::new(inner_tx, blocks_path, self.root_path.clone(), config);

        Ok((chainstate_tx, clarity_instance))
    }

    // NOTE: used for testing in the stacks testnet code.
    // DO NOT CALL FROM PRODUCTION
    pub fn clarity_eval_read_only(
        &mut self,
        burn_dbconn: &dyn BurnStateDB,
        parent_id_bhh: &StacksBlockId,
        contract: &QualifiedContractIdentifier,
        code: &str,
    ) -> Value {
        let result = self.clarity_state.eval_read_only(
            parent_id_bhh,
            self.state_index.sqlite_conn(),
            burn_dbconn,
            contract,
            code,
        );
        result.unwrap()
    }

    pub fn clarity_eval_read_only_checked(
        &mut self,
        burn_dbconn: &dyn BurnStateDB,
        parent_id_bhh: &StacksBlockId,
        contract: &QualifiedContractIdentifier,
        code: &str,
    ) -> Result<Value, Error> {
        self.clarity_state
            .eval_read_only(
                parent_id_bhh,
                self.state_index.sqlite_conn(),
                burn_dbconn,
                contract,
                code,
            )
            .map_err(Error::ClarityError)
    }

    pub fn db(&self) -> &DBConn {
        self.state_index.sqlite_conn()
    }

    /// Begin processing an epoch's transactions within the context of a chainstate transaction
    pub fn chainstate_block_begin<'a>(
        chainstate_tx: &'a ChainstateTx<'a>,
        clarity_instance: &'a mut ClarityInstance,
        burn_dbconn: &'a dyn BurnStateDB,
        parent_consensus_hash: &ConsensusHash,
        parent_block: &BlockHeaderHash,
        new_consensus_hash: &ConsensusHash,
        new_block: &BlockHeaderHash,
    ) -> ClarityTx<'a> {
        let conf = chainstate_tx.config.clone();
        StacksChainState::inner_clarity_tx_begin(
            conf,
            chainstate_tx.deref().deref(),
            clarity_instance,
            burn_dbconn,
            parent_consensus_hash,
            parent_block,
            new_consensus_hash,
            new_block,
        )
    }

    /// Begin a transaction against the Clarity VM, _outside of_ the context of a chainstate
    /// transaction.  Used by the miner for producing blocks.
    pub fn block_begin<'a>(
        &'a mut self,
        burn_dbconn: &'a dyn BurnStateDB,
        parent_consensus_hash: &ConsensusHash,
        parent_block: &BlockHeaderHash,
        new_consensus_hash: &ConsensusHash,
        new_block: &BlockHeaderHash,
    ) -> ClarityTx<'a> {
        let conf = self.config();
        StacksChainState::inner_clarity_tx_begin(
            conf,
            self.state_index.sqlite_conn(),
            &mut self.clarity_state,
            burn_dbconn,
            parent_consensus_hash,
            parent_block,
            new_consensus_hash,
            new_block,
        )
    }

    /// Begin a transaction against the Clarity VM for initiating the genesis block
    ///  the genesis block is special cased because it must be evaluated _before_ the
    ///  cost contract is loaded in the boot code.
    pub fn genesis_block_begin<'a>(
        &'a mut self,
        burn_dbconn: &'a dyn BurnStateDB,
        parent_consensus_hash: &ConsensusHash,
        parent_block: &BlockHeaderHash,
        new_consensus_hash: &ConsensusHash,
        new_block: &BlockHeaderHash,
    ) -> ClarityTx<'a> {
        let conf = self.config();
        let db = self.state_index.sqlite_conn();
        let clarity_instance = &mut self.clarity_state;

        // mix burn header hash and stacks block header hash together, since the stacks block hash
        // it not guaranteed to be globally unique (but the burn header hash _is_).
        let parent_index_block =
            StacksChainState::get_parent_index_block(parent_consensus_hash, parent_block);

        let new_index_block =
            StacksBlockHeader::make_index_block_hash(new_consensus_hash, new_block);

        test_debug!(
            "Begin processing genesis Stacks block off of {}/{}",
            parent_consensus_hash,
            parent_block
        );
        test_debug!(
            "Child MARF index root:  {} = {} + {}",
            new_index_block,
            new_consensus_hash,
            new_block
        );
        test_debug!(
            "Parent MARF index root: {} = {} + {}",
            parent_index_block,
            parent_consensus_hash,
            parent_block
        );

        let inner_clarity_tx = clarity_instance.begin_genesis_block(
            &parent_index_block,
            &new_index_block,
            db,
            burn_dbconn,
        );

        test_debug!("Got clarity TX!");
        ClarityTx {
            block: inner_clarity_tx,
            config: conf,
        }
    }

    pub fn with_clarity_marf<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut MARF<StacksBlockId>) -> R,
    {
        self.clarity_state.with_marf(f)
    }

    fn begin_read_only_clarity_tx<'a>(
        &'a mut self,
        burn_dbconn: &'a dyn BurnStateDB,
        index_block: &StacksBlockId,
    ) -> ClarityReadOnlyConnection<'a> {
        self.clarity_state.read_only_connection(
            &index_block,
            self.state_index.sqlite_conn(),
            burn_dbconn,
        )
    }

    /// Run to_do on the state of the Clarity VM at the given chain tip.
    /// Returns Some(x: R) if the given parent_tip exists.
    /// Returns None if not
    pub fn with_read_only_clarity_tx<F, R>(
        &mut self,
        burn_dbconn: &dyn BurnStateDB,
        parent_tip: &StacksBlockId,
        to_do: F,
    ) -> Option<R>
    where
        F: FnOnce(&mut ClarityReadOnlyConnection) -> R,
    {
        match StacksChainState::has_stacks_block(self.db(), parent_tip) {
            Ok(true) => {}
            Ok(false) => {
                return None;
            }
            Err(e) => {
                warn!("Failed to query for {}: {:?}", parent_tip, &e);
                return None;
            }
        }
        let mut conn = self.begin_read_only_clarity_tx(burn_dbconn, parent_tip);
        let result = to_do(&mut conn);
        Some(result)
    }

    /// Run to_do on the unconfirmed Clarity VM state
    pub fn with_read_only_unconfirmed_clarity_tx<F, R>(
        &mut self,
        burn_dbconn: &dyn BurnStateDB,
        to_do: F,
    ) -> Result<Option<R>, Error>
    where
        F: FnOnce(&mut ClarityReadOnlyConnection) -> R,
    {
        if let Some(ref unconfirmed) = self.unconfirmed_state.as_ref() {
            if !unconfirmed.is_readable() {
                return Ok(None);
            }
        }

        let mut unconfirmed_state_opt = self.unconfirmed_state.take();
        let res = if let Some(ref mut unconfirmed_state) = unconfirmed_state_opt {
            let mut conn = unconfirmed_state
                .clarity_inst
                .read_only_connection_checked(
                    &unconfirmed_state.unconfirmed_chain_tip,
                    self.db(),
                    burn_dbconn,
                )?;
            let result = to_do(&mut conn);
            Some(result)
        } else {
            None
        };
        self.unconfirmed_state = unconfirmed_state_opt;
        Ok(res)
    }

    /// Run to_do on the unconfirmed Clarity VM state if the tip refers to the unconfirmed state;
    /// otherwise run to_do on the confirmed state of the Clarity VM. If the tip doesn't exist,
    /// then return None.
    pub fn maybe_read_only_clarity_tx<F, R>(
        &mut self,
        burn_dbconn: &dyn BurnStateDB,
        parent_tip: &StacksBlockId,
        to_do: F,
    ) -> Result<Option<R>, Error>
    where
        F: FnOnce(&mut ClarityReadOnlyConnection) -> R,
    {
        let unconfirmed = if let Some(ref unconfirmed_state) = self.unconfirmed_state {
            *parent_tip == unconfirmed_state.unconfirmed_chain_tip
                && unconfirmed_state.is_readable()
        } else {
            false
        };

        if unconfirmed {
            self.with_read_only_unconfirmed_clarity_tx(burn_dbconn, to_do)
        } else {
            Ok(self.with_read_only_clarity_tx(burn_dbconn, parent_tip, to_do))
        }
    }

    fn get_parent_index_block(
        parent_consensus_hash: &ConsensusHash,
        parent_block: &BlockHeaderHash,
    ) -> StacksBlockId {
        if *parent_block == BOOT_BLOCK_HASH {
            // begin boot block
            StacksBlockId::sentinel()
        } else if *parent_block == FIRST_STACKS_BLOCK_HASH {
            // begin first-ever block
            StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            )
        } else {
            // subsequent block
            StacksBlockHeader::make_index_block_hash(parent_consensus_hash, parent_block)
        }
    }

    /// Begin an unconfirmed VM transaction, if there's no other open transaction for it.
    pub fn chainstate_begin_unconfirmed<'a>(
        conf: DBConfig,
        headers_db: &'a dyn HeadersDB,
        clarity_instance: &'a mut ClarityInstance,
        burn_dbconn: &'a dyn BurnStateDB,
        tip: &StacksBlockId,
    ) -> ClarityTx<'a> {
        let inner_clarity_tx = clarity_instance.begin_unconfirmed(tip, headers_db, burn_dbconn);
        ClarityTx {
            block: inner_clarity_tx,
            config: conf,
        }
    }

    /// Open a Clarity transaction against this chainstate's unconfirmed state, if it exists.
    pub fn begin_unconfirmed<'a>(
        &'a mut self,
        burn_dbconn: &'a dyn BurnStateDB,
    ) -> Option<ClarityTx<'a>> {
        let conf = self.config();
        if let Some(ref mut unconfirmed) = self.unconfirmed_state {
            if !unconfirmed.is_writable() {
                debug!("Unconfirmed state is not writable; cannot begin unconfirmed Clarity Tx");
                return None;
            }

            Some(StacksChainState::chainstate_begin_unconfirmed(
                conf,
                self.state_index.sqlite_conn(),
                &mut unconfirmed.clarity_inst,
                burn_dbconn,
                &unconfirmed.confirmed_chain_tip,
            ))
        } else {
            debug!("Unconfirmed state is not instantiated; cannot begin unconfirmed Clarity Tx");
            None
        }
    }

    /// Create a Clarity VM database transaction
    fn inner_clarity_tx_begin<'a>(
        conf: DBConfig,
        headers_db: &'a Connection,
        clarity_instance: &'a mut ClarityInstance,
        burn_dbconn: &'a dyn BurnStateDB,
        parent_consensus_hash: &ConsensusHash,
        parent_block: &BlockHeaderHash,
        new_consensus_hash: &ConsensusHash,
        new_block: &BlockHeaderHash,
    ) -> ClarityTx<'a> {
        // mix consensus hash and stacks block header hash together, since the stacks block hash
        // it not guaranteed to be globally unique (but the pair is)
        let parent_index_block =
            StacksChainState::get_parent_index_block(parent_consensus_hash, parent_block);

        let new_index_block =
            StacksBlockHeader::make_index_block_hash(new_consensus_hash, new_block);

        test_debug!(
            "Begin processing Stacks block off of {}/{}",
            parent_consensus_hash,
            parent_block
        );
        test_debug!(
            "Child MARF index root:  {} = {} + {}",
            new_index_block,
            new_consensus_hash,
            new_block
        );
        test_debug!(
            "Parent MARF index root: {} = {} + {}",
            parent_index_block,
            parent_consensus_hash,
            parent_block
        );

        let inner_clarity_tx = clarity_instance.begin_block(
            &parent_index_block,
            &new_index_block,
            headers_db,
            burn_dbconn,
        );

        test_debug!("Got clarity TX!");
        ClarityTx {
            block: inner_clarity_tx,
            config: conf,
        }
    }

    /// Get the appropriate MARF index hash to use to identify a chain tip, given a block header
    pub fn get_index_hash(
        consensus_hash: &ConsensusHash,
        header: &StacksBlockHeader,
    ) -> StacksBlockId {
        if consensus_hash == &FIRST_BURNCHAIN_CONSENSUS_HASH {
            StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            )
        } else {
            header.index_block_hash(consensus_hash)
        }
    }

    /// Record the microblock public key hash for a block into the MARF'ed Clarity DB
    pub fn insert_microblock_pubkey_hash(
        clarity_tx: &mut ClarityTx,
        height: u32,
        mblock_pubkey_hash: &Hash160,
    ) -> Result<(), Error> {
        clarity_tx
            .connection()
            .as_transaction(|tx| {
                tx.with_clarity_db(|ref mut db| {
                    db.insert_microblock_pubkey_hash_height(mblock_pubkey_hash, height)
                        .expect("FATAL: failed to store microblock public key hash to Clarity DB");
                    Ok(())
                })
            })
            .expect("FATAL: failed to store microblock public key hash");
        Ok(())
    }

    /// Get the block height at which a microblock public key hash was used, if any
    pub fn has_microblock_pubkey_hash(
        clarity_tx: &mut ClarityTx,
        mblock_pubkey_hash: &Hash160,
    ) -> Result<Option<u32>, Error> {
        let height_opt = clarity_tx
            .connection()
            .with_clarity_db_readonly::<_, Result<_, ()>>(|ref mut db| {
                let height_opt = db.get_microblock_pubkey_hash_height(mblock_pubkey_hash);
                Ok(height_opt)
            })
            .expect("FATAL: failed to query microblock public key hash");
        Ok(height_opt)
    }

    /// Append a Stacks block to an existing Stacks block, and grant the miner the block reward.
    /// Return the new Stacks header info.
    pub fn advance_tip<'a>(
        headers_tx: &mut StacksDBTx<'a>,
        parent_tip: &StacksBlockHeader,
        parent_consensus_hash: &ConsensusHash,
        new_tip: &StacksBlockHeader,
        new_consensus_hash: &ConsensusHash,
        new_burn_header_hash: &BurnchainHeaderHash,
        new_burnchain_height: u32,
        new_burnchain_timestamp: u64,
        microblock_tail_opt: Option<StacksMicroblockHeader>,
        block_reward: &MinerPaymentSchedule,
        user_burns: &Vec<StagingUserBurnSupport>,
        anchor_block_cost: &ExecutionCost,
        anchor_block_size: u64,
    ) -> Result<StacksHeaderInfo, Error> {
        if new_tip.parent_block != FIRST_STACKS_BLOCK_HASH {
            // not the first-ever block, so linkage must occur
            assert_eq!(new_tip.parent_block, parent_tip.block_hash());
        }

        assert_eq!(
            parent_tip
                .total_work
                .work
                .checked_add(1)
                .expect("Block height overflow"),
            new_tip.total_work.work
        );

        let parent_hash = StacksChainState::get_index_hash(parent_consensus_hash, parent_tip);

        // store each indexed field
        test_debug!(
            "Headers index_put_begin {}-{}",
            &parent_hash,
            &new_tip.index_block_hash(new_consensus_hash)
        );
        headers_tx
            .put_indexed_begin(&parent_hash, &new_tip.index_block_hash(new_consensus_hash))?;
        let root_hash = headers_tx.put_indexed_all(&vec![], &vec![])?;
        test_debug!(
            "Headers index_indexed_all finished {}-{}",
            &parent_hash,
            &new_tip.index_block_hash(new_consensus_hash)
        );

        let new_tip_info = StacksHeaderInfo {
            anchored_header: new_tip.clone(),
            microblock_tail: microblock_tail_opt,
            index_root: root_hash,
            block_height: new_tip.total_work.work,
            consensus_hash: new_consensus_hash.clone(),
            burn_header_hash: new_burn_header_hash.clone(),
            burn_header_height: new_burnchain_height,
            burn_header_timestamp: new_burnchain_timestamp,
            anchored_block_size: anchor_block_size,
        };

        StacksChainState::insert_stacks_block_header(
            headers_tx,
            &parent_hash,
            &new_tip_info,
            anchor_block_cost,
        )?;
        StacksChainState::insert_miner_payment_schedule(headers_tx, block_reward, user_burns)?;

        debug!(
            "Advanced to new tip! {}/{}",
            new_consensus_hash,
            new_tip.block_hash()
        );
        Ok(new_tip_info)
    }
}

#[cfg(test)]
pub mod test {
    use std::{env, fs};

    use chainstate::stacks::db::*;
    use chainstate::stacks::*;
    use stx_genesis::GenesisData;
    use vm::database::NULL_BURN_STATE_DB;

    use crate::util::boot::boot_code_test_addr;

    use super::*;

    pub fn instantiate_chainstate(
        mainnet: bool,
        chain_id: u32,
        test_name: &str,
    ) -> StacksChainState {
        instantiate_chainstate_with_balances(mainnet, chain_id, test_name, vec![])
    }

    pub fn instantiate_chainstate_with_balances(
        mainnet: bool,
        chain_id: u32,
        test_name: &str,
        balances: Vec<(StacksAddress, u64)>,
    ) -> StacksChainState {
        let path = chainstate_path(test_name);
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            }
            Err(_) => {}
        };

        let initial_balances = balances
            .into_iter()
            .map(|(addr, balance)| (PrincipalData::from(addr), balance))
            .collect();

        let mut boot_data = ChainStateBootData {
            initial_balances,
            post_flight_callback: None,
            first_burnchain_block_hash: BurnchainHeaderHash::zero(),
            first_burnchain_block_height: 0,
            first_burnchain_block_timestamp: 0,
            pox_constants: PoxConstants::testnet_default(),
            get_bulk_initial_lockups: None,
            get_bulk_initial_balances: None,
            get_bulk_initial_names: None,
            get_bulk_initial_namespaces: None,
        };

        StacksChainState::open_and_exec(
            mainnet,
            chain_id,
            &path,
            Some(&mut boot_data),
            ExecutionCost::max_value(),
        )
        .unwrap()
        .0
    }

    pub fn open_chainstate(mainnet: bool, chain_id: u32, test_name: &str) -> StacksChainState {
        let path = chainstate_path(test_name);
        StacksChainState::open(mainnet, chain_id, &path).unwrap().0
    }

    pub fn chainstate_path(test_name: &str) -> String {
        format!("/tmp/blockstack-test-chainstate-{}", test_name)
    }

    #[test]
    fn test_instantiate_chainstate() {
        let mut chainstate = instantiate_chainstate(false, 0x80000000, "instantiate-chainstate");

        // verify that the boot code is there
        let mut conn = chainstate.block_begin(
            &NULL_BURN_STATE_DB,
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
            &MINER_BLOCK_CONSENSUS_HASH,
            &MINER_BLOCK_HEADER_HASH,
        );

        for (boot_contract_name, _) in STACKS_BOOT_CODE_TESTNET.iter() {
            let boot_contract_id = QualifiedContractIdentifier::new(
                boot_code_test_addr().into(),
                ContractName::try_from(boot_contract_name.to_string()).unwrap(),
            );
            let contract_res =
                StacksChainState::get_contract(&mut conn, &boot_contract_id).unwrap();
            assert!(contract_res.is_some());
        }
    }

    #[test]
    fn test_chainstate_sampled_genesis_consistency() {
        // Test root hash for the test chainstate data set
        let mut boot_data = ChainStateBootData {
            initial_balances: vec![],
            first_burnchain_block_hash: BurnchainHeaderHash::zero(),
            first_burnchain_block_height: 0,
            first_burnchain_block_timestamp: 0,
            pox_constants: PoxConstants::testnet_default(),
            post_flight_callback: None,
            get_bulk_initial_lockups: Some(Box::new(|| {
                Box::new(GenesisData::new(true).read_lockups().map(|item| {
                    ChainstateAccountLockup {
                        address: item.address,
                        amount: item.amount,
                        block_height: item.block_height,
                    }
                }))
            })),
            get_bulk_initial_balances: Some(Box::new(|| {
                Box::new(GenesisData::new(true).read_balances().map(|item| {
                    ChainstateAccountBalance {
                        address: item.address,
                        amount: item.amount,
                    }
                }))
            })),
            get_bulk_initial_namespaces: Some(Box::new(|| {
                Box::new(GenesisData::new(true).read_namespaces().map(|item| {
                    ChainstateBNSNamespace {
                        namespace_id: item.namespace_id,
                        importer: item.importer,
                        buckets: item.buckets,
                        base: item.base as u64,
                        coeff: item.coeff as u64,
                        nonalpha_discount: item.nonalpha_discount as u64,
                        no_vowel_discount: item.no_vowel_discount as u64,
                        lifetime: item.lifetime as u64,
                    }
                }))
            })),
            get_bulk_initial_names: Some(Box::new(|| {
                Box::new(
                    GenesisData::new(true)
                        .read_names()
                        .map(|item| ChainstateBNSName {
                            fully_qualified_name: item.fully_qualified_name,
                            owner: item.owner,
                            zonefile_hash: item.zonefile_hash,
                        }),
                )
            })),
        };

        let path = chainstate_path("genesis-consistency-chainstate-test");
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            }
            Err(_) => {}
        };

        let mut chainstate = StacksChainState::open_and_exec(
            false,
            0x80000000,
            &path,
            Some(&mut boot_data),
            ExecutionCost::max_value(),
        )
        .unwrap()
        .0;

        let genesis_root_hash = chainstate.clarity_state.with_marf(|marf| {
            let index_block_hash = StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            );
            marf.get_root_hash_at(&index_block_hash).unwrap()
        });

        // If the genesis data changed, then this test will fail.
        // Just update the expected value
        assert_eq!(
            genesis_root_hash.to_string(),
            "c771616ff6acb710051238c9f4a3c48020a6d70cda637d34b89f2311a7e27886"
        );
    }

    #[test]
    fn test_chainstate_full_genesis_consistency() {
        if env::var("CIRCLE_CI_TEST") != Ok("1".into()) {
            return;
        }

        // Test root hash for the final chainstate data set
        let mut boot_data = ChainStateBootData {
            initial_balances: vec![],
            first_burnchain_block_hash: BurnchainHeaderHash::from_hex(
                BITCOIN_MAINNET_FIRST_BLOCK_HASH,
            )
            .unwrap(),
            first_burnchain_block_height: BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT as u32,
            first_burnchain_block_timestamp: BITCOIN_MAINNET_FIRST_BLOCK_TIMESTAMP,
            pox_constants: PoxConstants::mainnet_default(),
            post_flight_callback: None,
            get_bulk_initial_lockups: Some(Box::new(|| {
                Box::new(GenesisData::new(false).read_lockups().map(|item| {
                    ChainstateAccountLockup {
                        address: item.address,
                        amount: item.amount,
                        block_height: item.block_height,
                    }
                }))
            })),
            get_bulk_initial_balances: Some(Box::new(|| {
                Box::new(GenesisData::new(false).read_balances().map(|item| {
                    ChainstateAccountBalance {
                        address: item.address,
                        amount: item.amount,
                    }
                }))
            })),
            get_bulk_initial_namespaces: Some(Box::new(|| {
                Box::new(GenesisData::new(false).read_namespaces().map(|item| {
                    ChainstateBNSNamespace {
                        namespace_id: item.namespace_id,
                        importer: item.importer,
                        buckets: item.buckets,
                        base: item.base as u64,
                        coeff: item.coeff as u64,
                        nonalpha_discount: item.nonalpha_discount as u64,
                        no_vowel_discount: item.no_vowel_discount as u64,
                        lifetime: item.lifetime as u64,
                    }
                }))
            })),
            get_bulk_initial_names: Some(Box::new(|| {
                Box::new(
                    GenesisData::new(false)
                        .read_names()
                        .map(|item| ChainstateBNSName {
                            fully_qualified_name: item.fully_qualified_name,
                            owner: item.owner,
                            zonefile_hash: item.zonefile_hash,
                        }),
                )
            })),
        };

        let path = chainstate_path("genesis-consistency-chainstate");
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            }
            Err(_) => {}
        };

        let mut chainstate = StacksChainState::open_and_exec(
            true,
            0x000000001,
            &path,
            Some(&mut boot_data),
            ExecutionCost::max_value(),
        )
        .unwrap()
        .0;

        let genesis_root_hash = chainstate.clarity_state.with_marf(|marf| {
            let index_block_hash = StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            );
            marf.get_root_hash_at(&index_block_hash).unwrap()
        });

        // If the genesis data changed, then this test will fail.
        // Just update the expected value
        assert_eq!(
            format!("{}", genesis_root_hash),
            MAINNET_2_0_GENESIS_ROOT_HASH
        );
    }
}
