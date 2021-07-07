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

use std::collections::HashMap;
use std::convert::{From, TryFrom, TryInto};
use std::io::{ErrorKind, Write};
use std::ops::Deref;
use std::ops::DerefMut;
use std::{cmp, fmt, fs, str::FromStr};

use rand;
use rand::RngCore;
use rusqlite::types::ToSql;
use rusqlite::Row;
use rusqlite::Transaction;
use rusqlite::TransactionBehavior;
use rusqlite::{Connection, OpenFlags, OptionalExtension, NO_PARAMS};
use sha2::{Digest, Sha512Trunc256};

use address::AddressHashMode;
use burnchains::bitcoin::BitcoinNetworkType;
use burnchains::{Address, PublicKey, Txid};
use burnchains::{
    Burnchain, BurnchainBlockHeader, BurnchainRecipient, BurnchainStateTransition,
    BurnchainStateTransitionOps, BurnchainTransaction, BurnchainView, Error as BurnchainError,
    PoxConstants,
};
use chainstate::burn::operations::{
    leader_block_commit::{MissedBlockCommit, RewardSetInfo, OUTPUTS_PER_COMMIT},
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp, PreStxOp, StackStxOp,
    TransferStxOp, UserBurnSupportOp,
};
use chainstate::burn::Opcodes;
use chainstate::burn::{BlockSnapshot, ConsensusHash, OpsHash, SortitionHash};
use chainstate::coordinator::{Error as CoordinatorError, PoxAnchorBlockStatus, RewardCycleInfo};
use chainstate::stacks::db::{StacksChainState, StacksHeaderInfo};
use chainstate::stacks::index::marf::MarfConnection;
use chainstate::stacks::index::marf::MARF;
use chainstate::stacks::index::storage::TrieFileStorage;
use chainstate::stacks::index::{Error as MARFError, MarfTrieId};
use chainstate::stacks::StacksPublicKey;
use chainstate::stacks::*;
use chainstate::ChainstateDB;
use core::FIRST_BURNCHAIN_CONSENSUS_HASH;
use core::FIRST_STACKS_BLOCK_HASH;
use net::neighbors::MAX_NEIGHBOR_BLOCK_DELAY;
use net::{Error as NetError, Error};
use util::db::tx_begin_immediate;
use util::db::tx_busy_handler;
use util::db::Error as db_error;
use util::db::{
    db_mkdirs, query_count, query_row, query_row_columns, query_row_panic, query_rows, sql_pragma,
    u64_to_sql, DBConn, FromColumn, FromRow, IndexDBConn, IndexDBTx,
};
use util::get_epoch_time_secs;
use util::hash::{hex_bytes, to_hex, Hash160, Sha512Trunc256Sum};
use util::log;
use util::secp256k1::MessageSignature;
use util::strings::StacksString;
use util::vrf::*;
use vm::representations::{ClarityName, ContractName};
use vm::types::Value;

use crate::types::chainstate::StacksAddress;
use crate::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, MARFValue, PoxId, SortitionId, VRFSeed,
};
use crate::types::proof::{ClarityMarfTrieId, TrieHash};

const BLOCK_HEIGHT_MAX: u64 = ((1 as u64) << 63) - 1;

pub const REWARD_WINDOW_START: u64 = 144 * 15;
pub const REWARD_WINDOW_END: u64 = 144 * 90 + REWARD_WINDOW_START;

pub type BlockHeaderCache = HashMap<ConsensusHash, (Option<BlockHeaderHash>, ConsensusHash)>;

// for using BurnchainHeaderHash values as block hashes in a MARF
impl From<BurnchainHeaderHash> for BlockHeaderHash {
    fn from(bhh: BurnchainHeaderHash) -> BlockHeaderHash {
        BlockHeaderHash(bhh.0)
    }
}

// for using BurnchainHeaderHash values as block hashes in a MARF
impl From<BlockHeaderHash> for BurnchainHeaderHash {
    fn from(bhh: BlockHeaderHash) -> BurnchainHeaderHash {
        BurnchainHeaderHash(bhh.0)
    }
}

impl FromRow<SortitionId> for SortitionId {
    fn from_row<'a>(row: &'a Row) -> Result<SortitionId, db_error> {
        SortitionId::from_column(row, "sortition_id")
    }
}

impl FromRow<MissedBlockCommit> for MissedBlockCommit {
    fn from_row<'a>(row: &'a Row) -> Result<MissedBlockCommit, db_error> {
        let intended_sortition = SortitionId::from_column(row, "intended_sortition_id")?;
        let input_json: String = row.get_unwrap("input");
        let input =
            serde_json::from_str(&input_json).map_err(|e| db_error::SerializationError(e))?;
        let txid = Txid::from_column(row, "txid")?;

        Ok(MissedBlockCommit {
            input,
            txid,
            intended_sortition,
        })
    }
}

impl FromRow<BlockSnapshot> for BlockSnapshot {
    fn from_row<'a>(row: &'a Row) -> Result<BlockSnapshot, db_error> {
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;
        let burn_header_timestamp = u64::from_column(row, "burn_header_timestamp")?;
        let parent_burn_header_hash =
            BurnchainHeaderHash::from_column(row, "parent_burn_header_hash")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let ops_hash = OpsHash::from_column(row, "ops_hash")?;
        let total_burn_str: String = row.get_unwrap("total_burn");
        let sortition: bool = row.get_unwrap("sortition");
        let sortition_hash = SortitionHash::from_column(row, "sortition_hash")?;
        let winning_block_txid = Txid::from_column(row, "winning_block_txid")?;
        let winning_stacks_block_hash =
            BlockHeaderHash::from_column(row, "winning_stacks_block_hash")?;
        let index_root = TrieHash::from_column(row, "index_root")?;
        let num_sortitions = u64::from_column(row, "num_sortitions")?;

        // information we learn about the stacks block this snapshot committedto
        let stacks_block_accepted: bool = row.get_unwrap("stacks_block_accepted");
        let stacks_block_height = u64::from_column(row, "stacks_block_height")?;
        let arrival_index = u64::from_column(row, "arrival_index")?;

        // information about what we have determined about the stacks chain tip.
        // This is memoized to a given canonical chain tip block.
        let canonical_stacks_tip_height = u64::from_column(row, "canonical_stacks_tip_height")?;
        let canonical_stacks_tip_hash =
            BlockHeaderHash::from_column(row, "canonical_stacks_tip_hash")?;
        let canonical_stacks_tip_consensus_hash =
            ConsensusHash::from_column(row, "canonical_stacks_tip_consensus_hash")?;

        // identifiers derived from PoX forking state
        let sortition_id = SortitionId::from_column(row, "sortition_id")?;
        let parent_sortition_id = SortitionId::from_column(row, "parent_sortition_id")?;
        let pox_valid = row.get_unwrap("pox_valid");

        let accumulated_coinbase_ustx_str: String = row.get_unwrap("accumulated_coinbase_ustx");
        let accumulated_coinbase_ustx = accumulated_coinbase_ustx_str
            .parse::<u128>()
            .expect("DB CORRUPTION: failed to parse stored value");

        let total_burn = total_burn_str
            .parse::<u64>()
            .map_err(|_e| db_error::ParseError)?;

        let snapshot = BlockSnapshot {
            block_height: block_height,
            burn_header_timestamp: burn_header_timestamp,
            burn_header_hash: burn_header_hash,
            parent_burn_header_hash: parent_burn_header_hash,
            consensus_hash: consensus_hash,
            ops_hash: ops_hash,
            total_burn: total_burn,
            sortition: sortition,
            sortition_hash: sortition_hash,
            winning_block_txid: winning_block_txid,
            winning_stacks_block_hash: winning_stacks_block_hash,
            index_root: index_root,
            num_sortitions: num_sortitions,

            stacks_block_accepted: stacks_block_accepted,
            stacks_block_height: stacks_block_height,
            arrival_index: arrival_index,

            canonical_stacks_tip_height: canonical_stacks_tip_height,
            canonical_stacks_tip_hash: canonical_stacks_tip_hash,
            canonical_stacks_tip_consensus_hash: canonical_stacks_tip_consensus_hash,

            sortition_id,
            parent_sortition_id,
            pox_valid,
            accumulated_coinbase_ustx,
        };
        Ok(snapshot)
    }
}

impl FromRow<LeaderKeyRegisterOp> for LeaderKeyRegisterOp {
    fn from_row<'a>(row: &'a Row) -> Result<LeaderKeyRegisterOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let public_key = VRFPublicKey::from_column(row, "public_key")?;
        let memo_hex: String = row.get_unwrap("memo");
        let address = StacksAddress::from_column(row, "address")?;

        let memo_bytes = hex_bytes(&memo_hex).map_err(|_e| db_error::ParseError)?;

        let memo = memo_bytes.to_vec();

        let leader_key_row = LeaderKeyRegisterOp {
            txid: txid,
            vtxindex: vtxindex,
            block_height: block_height,
            burn_header_hash: burn_header_hash,

            consensus_hash: consensus_hash,
            public_key: public_key,
            memo: memo,
            address: address,
        };

        Ok(leader_key_row)
    }
}

impl FromRow<LeaderBlockCommitOp> for LeaderBlockCommitOp {
    fn from_row<'a>(row: &'a Row) -> Result<LeaderBlockCommitOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;
        let block_header_hash = BlockHeaderHash::from_column(row, "block_header_hash")?;
        let new_seed = VRFSeed::from_column(row, "new_seed")?;
        let parent_block_ptr: u32 = row.get_unwrap("parent_block_ptr");
        let parent_vtxindex: u16 = row.get_unwrap("parent_vtxindex");
        let key_block_ptr: u32 = row.get_unwrap("key_block_ptr");
        let key_vtxindex: u16 = row.get_unwrap("key_vtxindex");
        let memo_hex: String = row.get_unwrap("memo");
        let burn_fee_str: String = row.get_unwrap("burn_fee");
        let input_json: String = row.get_unwrap("input");
        let apparent_sender_json: String = row.get_unwrap("apparent_sender");
        let sunset_burn_str: String = row.get_unwrap("sunset_burn");

        let commit_outs = serde_json::from_value(row.get_unwrap("commit_outs"))
            .expect("Unparseable value stored to database");

        let memo_bytes = hex_bytes(&memo_hex).map_err(|_e| db_error::ParseError)?;

        let memo = memo_bytes.to_vec();

        let input =
            serde_json::from_str(&input_json).map_err(|e| db_error::SerializationError(e))?;

        let apparent_sender = serde_json::from_str(&apparent_sender_json)
            .map_err(|e| db_error::SerializationError(e))?;

        let burn_fee = burn_fee_str
            .parse::<u64>()
            .expect("DB Corruption: Sunset burn is not parseable as u64");

        let sunset_burn = sunset_burn_str
            .parse::<u64>()
            .expect("DB Corruption: Sunset burn is not parseable as u64");

        let burn_parent_modulus: u8 = row.get_unwrap("burn_parent_modulus");

        let block_commit = LeaderBlockCommitOp {
            block_header_hash,
            new_seed,
            parent_block_ptr,
            parent_vtxindex,
            key_block_ptr,
            key_vtxindex,
            memo,
            burn_parent_modulus,

            burn_fee,
            input,
            apparent_sender,
            commit_outs,
            sunset_burn,
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
        };
        Ok(block_commit)
    }
}

impl FromRow<UserBurnSupportOp> for UserBurnSupportOp {
    fn from_row<'a>(row: &'a Row) -> Result<UserBurnSupportOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;

        let address = StacksAddress::from_column(row, "address")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let public_key = VRFPublicKey::from_column(row, "public_key")?;
        let key_block_ptr: u32 = row.get_unwrap("key_block_ptr");
        let key_vtxindex: u16 = row.get_unwrap("key_vtxindex");
        let block_header_hash_160 = Hash160::from_column(row, "block_header_hash_160")?;

        let burn_fee_str: String = row.get_unwrap("burn_fee");

        let burn_fee = burn_fee_str
            .parse::<u64>()
            .map_err(|_e| db_error::ParseError)?;

        let user_burn = UserBurnSupportOp {
            address: address,
            consensus_hash: consensus_hash,
            public_key: public_key,
            key_block_ptr: key_block_ptr,
            key_vtxindex: key_vtxindex,
            block_header_hash_160: block_header_hash_160,
            burn_fee: burn_fee,

            txid: txid,
            vtxindex: vtxindex,
            block_height: block_height,
            burn_header_hash: burn_header_hash,
        };
        Ok(user_burn)
    }
}

impl FromRow<StackStxOp> for StackStxOp {
    fn from_row<'a>(row: &'a Row) -> Result<StackStxOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;

        let sender = StacksAddress::from_column(row, "sender_addr")?;
        let reward_addr = StacksAddress::from_column(row, "reward_addr")?;
        let stacked_ustx_str: String = row.get_unwrap("stacked_ustx");
        let stacked_ustx = u128::from_str_radix(&stacked_ustx_str, 10)
            .expect("CORRUPTION: bad u128 written to sortdb");
        let num_cycles = row.get_unwrap("num_cycles");

        Ok(StackStxOp {
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
            sender,
            reward_addr,
            stacked_ustx,
            num_cycles,
        })
    }
}

impl FromRow<TransferStxOp> for TransferStxOp {
    fn from_row<'a>(row: &'a Row) -> Result<TransferStxOp, db_error> {
        let txid = Txid::from_column(row, "txid")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let block_height = u64::from_column(row, "block_height")?;
        let burn_header_hash = BurnchainHeaderHash::from_column(row, "burn_header_hash")?;

        let sender = StacksAddress::from_column(row, "sender_addr")?;
        let recipient = StacksAddress::from_column(row, "recipient_addr")?;
        let transfered_ustx_str: String = row.get_unwrap("transfered_ustx");
        let transfered_ustx = u128::from_str_radix(&transfered_ustx_str, 10)
            .expect("CORRUPTION: bad u128 written to sortdb");
        let memo_hex: String = row.get_unwrap("memo");
        let memo = hex_bytes(&memo_hex).map_err(|_| db_error::Corruption)?;

        Ok(TransferStxOp {
            txid,
            vtxindex,
            block_height,
            burn_header_hash,
            sender,
            recipient,
            transfered_ustx,
            memo,
        })
    }
}

struct AcceptedStacksBlockHeader {
    pub tip_consensus_hash: ConsensusHash, // PoX tip
    pub consensus_hash: ConsensusHash,     // stacks block consensus hash
    pub block_hash: BlockHeaderHash,       // stacks block hash
    pub height: u64,                       // stacks block height
}

pub struct InitialMiningBonus {
    pub total_reward: u128,
    pub per_block: u128,
}

impl FromRow<AcceptedStacksBlockHeader> for AcceptedStacksBlockHeader {
    fn from_row<'a>(row: &'a Row) -> Result<AcceptedStacksBlockHeader, db_error> {
        let tip_consensus_hash = ConsensusHash::from_column(row, "tip_consensus_hash")?;
        let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")?;
        let block_hash = BlockHeaderHash::from_column(row, "stacks_block_hash")?;
        let height = u64::from_column(row, "block_height")?;

        Ok(AcceptedStacksBlockHeader {
            tip_consensus_hash,
            consensus_hash,
            block_hash,
            height,
        })
    }
}

pub const SORTITION_DB_VERSION: &'static str = "1";

const SORTITION_DB_INITIAL_SCHEMA: &'static [&'static str] = &[
    r#"
    PRAGMA foreign_keys = ON;
    "#,
    r#"
    -- sortition snapshots -- snapshot of all transactions processed in a burn block
    -- organizes the set of forks in the burn chain as well.
    CREATE TABLE snapshots(
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,
        sortition_id TEXT UNIQUE NOT NULL,
        parent_sortition_id TEXT NOT NULL,
        burn_header_timestamp INT NOT NULL,
        parent_burn_header_hash TEXT NOT NULL,
        consensus_hash TEXT UNIQUE NOT NULL,
        ops_hash TEXT NOT NULL,
        total_burn TEXT NOT NULL,
        sortition INTEGER NOT NULL,
        sortition_hash TEXT NOT NULL,
        winning_block_txid TEXT NOT NULL,
        winning_stacks_block_hash TEXT NOT NULL,
        index_root TEXT UNIQUE NOT NULL,

        num_sortitions INTEGER NOT NULL,

        stacks_block_accepted INTEGER NOT NULL,        -- set to 1 if we fetched and processed this Stacks block
        stacks_block_height INTEGER NOT NULL,           -- set to the height of the stacks block, once it's processed
        arrival_index INTEGER NOT NULL,                 -- (global) order in which this Stacks block was processed

        canonical_stacks_tip_height INTEGER NOT NULL,   -- height of highest known Stacks fork in this burn chain fork
        canonical_stacks_tip_hash TEXT NOT NULL,        -- hash of highest known Stacks fork's tip block in this burn chain fork
        canonical_stacks_tip_consensus_hash TEXT NOT NULL,   -- burn hash of highest known Stacks fork's tip block in this burn chain fork

        pox_valid INTEGER NOT NULL,

        accumulated_coinbase_ustx TEXT NOT NULL,

        PRIMARY KEY(sortition_id)
    );"#,
    "CREATE INDEX snapshots_block_hashes ON snapshots(block_height,index_root,winning_stacks_block_hash);",
    "CREATE INDEX snapshots_block_stacks_hashes ON snapshots(num_sortitions,index_root,winning_stacks_block_hash);",
    "CREATE INDEX snapshots_block_heights ON snapshots(burn_header_hash,block_height);",
    "CREATE INDEX snapshots_block_winning_hash ON snapshots(winning_stacks_block_hash);",
    "CREATE INDEX block_arrivals ON snapshots(arrival_index,burn_header_hash);",
    "CREATE INDEX arrival_indexes ON snapshots(arrival_index);",
    r#"
    CREATE TABLE snapshot_transition_ops(
      sortition_id TEXT PRIMARY KEY,
      accepted_ops TEXT NOT NULL,
      consumed_keys TEXT NOT NULL
    );"#,
    r#"
    -- all leader keys registered in the blockchain.
    -- contains pointers to the burn block and fork in which they occur
    CREATE TABLE leader_keys(
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,
        sortition_id TEXT NOT NULL,
        
        consensus_hash TEXT NOT NULL,
        public_key TEXT NOT NULL,
        memo TEXT,
        address TEXT NOT NULL,

        PRIMARY KEY(txid,sortition_id),
        FOREIGN KEY(sortition_id) REFERENCES snapshots(sortition_id)
    );"#,
    r#"
    CREATE TABLE block_commits(
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,
        sortition_id TEXT NOT NULL,

        block_header_hash TEXT NOT NULL,
        new_seed TEXT NOT NULL,
        parent_block_ptr INTEGER NOT NULL,
        parent_vtxindex INTEGER NOT NULL,
        key_block_ptr INTEGER NOT NULL,
        key_vtxindex INTEGER NOT NULL,
        memo TEXT,
        commit_outs TEXT,
        burn_fee TEXT NOT NULL,     -- use text to encode really big numbers
        sunset_burn TEXT NOT NULL,     -- use text to encode really big numbers
        input TEXT NOT NULL,
        apparent_sender TEXT NOT NULL,
        burn_parent_modulus INTEGER NOT NULL,

        PRIMARY KEY(txid,sortition_id),
        FOREIGN KEY(sortition_id) REFERENCES snapshots(sortition_id)
    );"#,
    r#"
    CREATE TABLE user_burn_support(
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,
        sortition_id TEXT NOT NULL,

        address TEXT NOT NULL,
        consensus_hash TEXT NOT NULL,
        public_key TEXT NOT NULL,
        key_block_ptr INTEGER NOT NULL,
        key_vtxindex INTEGER NOT NULL,
        block_header_hash_160 TEXT NOT NULL,

        burn_fee TEXT NOT NULL,

        PRIMARY KEY(txid,sortition_id),
        FOREIGN KEY(sortition_id) REFERENCES snapshots(sortition_id)
    );"#,
    r#"
    CREATE TABLE stack_stx (
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,

        sender_addr TEXT NOT NULL,
        reward_addr TEXT NOT NULL,
        stacked_ustx TEXT NOT NULL,
        num_cycles INTEGER NOT NULL,

        PRIMARY KEY(txid)
    );"#,
    r#"
    CREATE TABLE transfer_stx (
        txid TEXT NOT NULL,
        vtxindex INTEGER NOT NULL,
        block_height INTEGER NOT NULL,
        burn_header_hash TEXT NOT NULL,

        sender_addr TEXT NOT NULL,
        recipient_addr TEXT NOT NULL,
        transfered_ustx TEXT NOT NULL,
        memo TEXT NOT NULL,

        PRIMARY KEY(txid)
    );"#,
    r#"
    CREATE TABLE missed_commits (
        txid TEXT NOT NULL,
        input TEXT NOT NULL,
        intended_sortition_id TEXT NOT NULL,

        PRIMARY KEY(txid, intended_sortition_id)
    );"#,
    r#"
    CREATE TABLE canonical_accepted_stacks_blocks(
        tip_consensus_hash TEXT NOT NULL,
        consensus_hash TEXT NOT NULL,
        stacks_block_hash TEXT NOT NULL,
        block_height INTEGER NOT NULL,
        PRIMARY KEY(consensus_hash, stacks_block_hash)
    );"#,
    "CREATE INDEX canonical_stacks_blocks ON canonical_accepted_stacks_blocks(tip_consensus_hash,stacks_block_hash);",
    "CREATE TABLE db_config(version TEXT NOT NULL);",
];

pub struct SortitionDB {
    pub readwrite: bool,
    pub marf: MARF<SortitionId>,
    pub first_block_height: u64,
    pub first_burn_header_hash: BurnchainHeaderHash,
}

#[derive(Clone)]
pub struct SortitionDBTxContext {
    pub first_block_height: u64,
}

#[derive(Clone)]
pub struct SortitionHandleContext {
    pub first_block_height: u64,
    pub chain_tip: SortitionId,
}

pub type SortitionDBConn<'a> = IndexDBConn<'a, SortitionDBTxContext, SortitionId>;
pub type SortitionDBTx<'a> = IndexDBTx<'a, SortitionDBTxContext, SortitionId>;

///
/// These structs are used to keep an open "handle" to the
///   sortition db -- this is just the db/marf connection
///   and a chain tip. This mostly just makes the job of callers
///   much simpler, because they don't have to worry about passing
///   around the open chain tip everywhere.
///
pub type SortitionHandleConn<'a> = IndexDBConn<'a, SortitionHandleContext, SortitionId>;
pub type SortitionHandleTx<'a> = IndexDBTx<'a, SortitionHandleContext, SortitionId>;

///
/// This trait is used for functions that
///  can accept either a SortitionHandleConn or a SortitionDBConn
///
pub trait SortitionContext: Clone {
    fn first_block_height(&self) -> u64;
}

impl SortitionContext for SortitionHandleContext {
    fn first_block_height(&self) -> u64 {
        self.first_block_height
    }
}

impl SortitionContext for SortitionDBTxContext {
    fn first_block_height(&self) -> u64 {
        self.first_block_height
    }
}

fn get_block_commit_by_txid(
    conn: &Connection,
    txid: &Txid,
) -> Result<Option<LeaderBlockCommitOp>, db_error> {
    let qry = "SELECT * FROM block_commits WHERE txid = ?1 LIMIT 1";
    query_row(conn, qry, &[&txid])
}

fn get_ancestor_sort_id<C: SortitionContext>(
    ic: &IndexDBConn<'_, C, SortitionId>,
    block_height: u64,
    tip_block_hash: &SortitionId,
) -> Result<Option<SortitionId>, db_error> {
    let adjusted_height = match get_adjusted_block_height(&ic.context, block_height) {
        Some(x) => x,
        None => return Ok(None),
    };

    ic.get_ancestor_block_hash(adjusted_height, &tip_block_hash)
}

fn get_ancestor_sort_id_tx<C: SortitionContext>(
    ic: &mut IndexDBTx<'_, C, SortitionId>,
    block_height: u64,
    tip_block_hash: &SortitionId,
) -> Result<Option<SortitionId>, db_error> {
    let adjusted_height = match get_adjusted_block_height(&ic.context, block_height) {
        Some(x) => x,
        None => return Ok(None),
    };

    ic.get_ancestor_block_hash(adjusted_height, &tip_block_hash)
}

fn get_adjusted_block_height<C: SortitionContext>(context: &C, block_height: u64) -> Option<u64> {
    let first_block_height = context.first_block_height();
    if block_height < first_block_height {
        return None;
    }

    Some(block_height - first_block_height)
}

struct db_keys;
impl db_keys {
    /// store an entry that maps from a PoX anchor's <stacks-block-header-hash> to <sortition-id of last block in prepare phase that chose it>
    pub fn pox_anchor_to_prepare_end(block_hash: &BlockHeaderHash) -> String {
        format!("sortition_db::pox_anchor_to_prepare_end::{}", block_hash)
    }

    pub fn pox_last_anchor() -> &'static str {
        "sortition_db::last_anchor_block"
    }

    pub fn pox_reward_set_size() -> &'static str {
        "sortition_db::reward_set::size"
    }

    pub fn pox_reward_set_entry(ix: u16) -> String {
        format!("sortition_db::reward_set::entry::{}", ix)
    }

    /// store an entry for retrieving the PoX identifier (i.e., the PoX bitvector) for this PoX fork
    pub fn pox_identifier() -> &'static str {
        "sortition_db::pox_identifier"
    }

    pub fn initial_mining_bonus_remaining() -> &'static str {
        "sortition_db::initial_mining::remaining"
    }

    pub fn initial_mining_bonus_per_block() -> &'static str {
        "sortition_db::initial_mining::per_block"
    }

    pub fn sortition_id_for_bhh(bhh: &BurnchainHeaderHash) -> String {
        format!("sortition_db::sortition_id_for_bhh::{}", bhh)
    }
    pub fn vrf_key_status(key: &VRFPublicKey) -> String {
        format!("sortition_db::vrf::{}", key.to_hex())
    }
    pub fn stacks_block_present(block_hash: &BlockHeaderHash) -> String {
        format!("sortition_db::sortition_block_hash::{}", block_hash)
    }
    pub fn last_sortition() -> &'static str {
        "sortition_db::last_sortition"
    }

    /// MARF index key for a processed stacks block.  Maps to its height.
    pub fn stacks_block_index(stacks_block_hash: &BlockHeaderHash) -> String {
        format!("sortition_db::stacks::block::{}", stacks_block_hash)
    }

    /// MARF index value for a processed stacks block
    fn stacks_block_index_value(height: u64) -> String {
        format!("{}", height)
    }

    /// MARF index key for the highest arrival index processed in a fork
    pub fn stacks_block_max_arrival_index() -> String {
        "sortition_db::stacks::block::max_arrival_index".to_string()
    }

    /// MARF index value for the highest arrival index processed in a fork
    fn stacks_block_max_arrival_index_value(index: u64) -> String {
        format!("{}", index)
    }

    pub fn reward_set_size_to_string(size: usize) -> String {
        to_hex(
            &u16::try_from(size)
                .expect("BUG: maximum reward set size should be u16")
                .to_le_bytes(),
        )
    }

    pub fn reward_set_size_from_string(size: &str) -> u16 {
        let bytes = hex_bytes(size).expect("CORRUPTION: bad format written for reward set size");
        let mut byte_buff = [0; 2];
        byte_buff.copy_from_slice(&bytes[0..2]);
        u16::from_le_bytes(byte_buff)
    }
}

impl<'a> SortitionHandleTx<'a> {
    /// begin a MARF transaction with this connection
    ///  this is used by _writing_ contexts
    pub fn begin(
        conn: &'a mut SortitionDB,
        parent_chain_tip: &SortitionId,
    ) -> Result<SortitionHandleTx<'a>, db_error> {
        if !conn.readwrite {
            return Err(db_error::ReadOnly);
        }

        let handle = SortitionHandleTx::new(
            &mut conn.marf,
            SortitionHandleContext {
                chain_tip: parent_chain_tip.clone(),
                first_block_height: conn.first_block_height,
            },
        );

        Ok(handle)
    }

    /// Uses the handle's current fork identifier to get a block snapshot by
    ///   burnchain block header
    /// If the burn header hash is _not_ in the current fork, then this will return Ok(None)
    pub fn get_block_snapshot(
        &mut self,
        burn_header_hash: &BurnchainHeaderHash,
        chain_tip: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let sortition_identifier_key = db_keys::sortition_id_for_bhh(burn_header_hash);
        let sortition_id = match self.get_indexed(&chain_tip, &sortition_identifier_key)? {
            None => return Ok(None),
            Some(x) => SortitionId::from_hex(&x).expect("FATAL: bad Sortition ID stored in DB"),
        };

        SortitionDB::get_block_snapshot(self.tx(), &sortition_id)
    }

    /// Get a leader key at a specific location in the burn chain's fork history, given the
    /// matching block commit's fork index root (block_height and vtxindex are the leader's
    /// calculated location in this fork).
    /// Returns None if there is no leader key at this location.
    pub fn get_leader_key_at(
        &mut self,
        key_block_height: u64,
        key_vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderKeyRegisterOp>, db_error> {
        assert!(key_block_height < BLOCK_HEIGHT_MAX);
        let ancestor_snapshot =
            match SortitionDB::get_ancestor_snapshot_tx(self, key_block_height, tip)? {
                Some(sn) => sn,
                None => {
                    return Ok(None);
                }
            };

        let qry = "SELECT * FROM leader_keys WHERE sortition_id = ?1 AND block_height = ?2 AND vtxindex = ?3 LIMIT 2";
        let args: &[&dyn ToSql] = &[
            &ancestor_snapshot.sortition_id,
            &u64_to_sql(key_block_height)?,
            &key_vtxindex,
        ];
        query_row_panic(self.tx(), qry, args, || {
            format!(
                "Multiple keys at {},{} in {}",
                key_block_height, key_vtxindex, tip
            )
        })
    }

    /// Find the VRF public keys consumed by each block candidate in the given list.
    /// The burn DB should have a key for each candidate; otherwise the candidate would not have
    /// been accepted.
    pub fn get_consumed_leader_keys(
        &mut self,
        parent_tip: &BlockSnapshot,
        block_candidates: &Vec<LeaderBlockCommitOp>,
    ) -> Result<Vec<LeaderKeyRegisterOp>, db_error> {
        // get the set of VRF keys consumed by these commits
        let mut leader_keys = vec![];
        for i in 0..block_candidates.len() {
            let leader_key_block_height = block_candidates[i].key_block_ptr as u64;
            let leader_key_vtxindex = block_candidates[i].key_vtxindex as u32;
            let leader_key = self
                .get_leader_key_at(
                    leader_key_block_height,
                    leader_key_vtxindex,
                    &parent_tip.sortition_id,
                )?
                .expect(&format!(
                    "FATAL: no leader key for accepted block commit {} (at {},{})",
                    &block_candidates[i].txid, leader_key_block_height, leader_key_vtxindex
                ));

            leader_keys.push(leader_key);
        }

        Ok(leader_keys)
    }

    /// Get a block commit by its content-addressed location in a specific sortition.
    pub fn get_block_commit(
        &self,
        txid: &Txid,
        sortition_id: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        SortitionDB::get_block_commit(self.tx(), txid, sortition_id)
    }

    pub fn get_consensus_at(
        &mut self,
        block_height: u64,
    ) -> Result<Option<ConsensusHash>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let chain_tip = self.context.chain_tip.clone();

        match SortitionDB::get_ancestor_snapshot_tx(self, block_height, &chain_tip)? {
            Some(sn) => Ok(Some(sn.consensus_hash)),
            None => Ok(None),
        }
    }

    /// Do we expect a stacks block in this particular fork?
    /// i.e. is this block hash part of the fork history identified by tip_block_hash?
    pub fn expects_stacks_block_in_fork(
        &mut self,
        block_hash: &BlockHeaderHash,
    ) -> Result<bool, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        self.get_indexed(&chain_tip, &db_keys::stacks_block_present(block_hash))
            .map(|result| result.is_some())
    }

    /// Get the latest block snapshot on this fork where a sortition occured.
    /// Search snapshots up to (but excluding) the given block height.
    /// Will always return a snapshot -- even if it's the initial sentinel snapshot.
    pub fn get_last_snapshot_with_sortition(
        &mut self,
        burn_block_height: u64,
    ) -> Result<BlockSnapshot, db_error> {
        assert!(burn_block_height < BLOCK_HEIGHT_MAX);
        test_debug!(
            "Get snapshot at from sortition tip {}, expect height {}",
            &self.context.chain_tip,
            burn_block_height
        );
        let chain_tip = self.context.chain_tip.clone();

        let get_from = match get_ancestor_sort_id_tx(self, burn_block_height, &chain_tip)? {
            Some(sortition_id) => sortition_id,
            None => {
                error!(
                    "No blockheight {} ancestor at sortition identifier {}",
                    burn_block_height, &self.context.chain_tip
                );
                return Err(db_error::NotFoundError);
            }
        };

        let ancestor_hash = match self.get_indexed(&get_from, &db_keys::last_sortition())? {
            Some(hex_str) => BurnchainHeaderHash::from_hex(&hex_str).expect(&format!(
                "FATAL: corrupt database: failed to parse {} into a hex string",
                &hex_str
            )),
            None => {
                // no prior sortitions, so get the first
                return SortitionDB::get_first_block_snapshot(self.tx());
            }
        };

        self.get_block_snapshot(&ancestor_hash, &chain_tip)
            .map(|snapshot_opt| {
                snapshot_opt.expect(&format!(
                    "FATAL: corrupt index: no snapshot {}",
                    ancestor_hash
                ))
            })
    }

    /// Determine whether or not a leader key has been consumed by a subsequent block commitment in
    /// this fork's history.
    /// Will return false if the leader key does not exist.
    pub fn is_leader_key_consumed(
        &mut self,
        leader_key: &LeaderKeyRegisterOp,
    ) -> Result<bool, db_error> {
        assert!(leader_key.block_height < BLOCK_HEIGHT_MAX);
        let chain_tip = self.context.chain_tip.clone();

        let key_status =
            match self.get_indexed(&chain_tip, &db_keys::vrf_key_status(&leader_key.public_key))? {
                Some(status_str) => {
                    if status_str == "1" {
                        // key is still available
                        false
                    } else if status_str == "0" {
                        // key is consumed
                        true
                    } else {
                        panic!("Invalid key status string {}", status_str);
                    }
                }
                None => {
                    // never before seen
                    false
                }
            };

        Ok(key_status)
    }

    /// Get a parent block commit at a specific location in the burn chain on a particular fork.
    /// Returns None if there is no block commit at this location.
    pub fn get_block_commit_parent(
        &mut self,
        block_height: u64,
        vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let ancestor_id = match get_ancestor_sort_id_tx(self, block_height, tip)? {
            Some(id) => id,
            None => {
                return Ok(None);
            }
        };

        SortitionDB::get_block_commit_of_sortition(self.tx(), &ancestor_id, block_height, vtxindex)
    }

    pub fn has_VRF_public_key(&mut self, key: &VRFPublicKey) -> Result<bool, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let key_status = self
            .get_indexed(&chain_tip, &db_keys::vrf_key_status(key))?
            .is_some();
        Ok(key_status)
    }

    fn check_fresh_consensus_hash<F>(
        &mut self,
        consensus_hash_lifetime: u64,
        check: F,
    ) -> Result<bool, db_error>
    where
        F: Fn(&ConsensusHash) -> bool,
    {
        let chain_tip = self.context.chain_tip.clone();
        let first_snapshot = SortitionDB::get_first_block_snapshot(self.tx())?;
        let mut last_snapshot =
            SortitionDB::get_block_snapshot(self.tx(), &self.context.chain_tip)?
                .ok_or_else(|| db_error::NotFoundError)?;
        let current_block_height = last_snapshot.block_height;

        let mut oldest_height = if current_block_height < consensus_hash_lifetime {
            0
        } else {
            current_block_height - consensus_hash_lifetime
        };

        if oldest_height < first_snapshot.block_height {
            oldest_height = first_snapshot.block_height;
        }

        if check(&last_snapshot.consensus_hash) {
            return Ok(true);
        }

        for _i in oldest_height..current_block_height {
            let ancestor_snapshot = self
                .get_block_snapshot(&last_snapshot.parent_burn_header_hash, &chain_tip)?
                .expect(&format!(
                    "Discontiguous index: missing block {}",
                    last_snapshot.parent_burn_header_hash
                ));
            if check(&ancestor_snapshot.consensus_hash) {
                return Ok(true);
            }
            last_snapshot = ancestor_snapshot;
        }

        return Ok(false);
    }

    /// Find out whether or not a given consensus hash is "recent" enough to be used in this fork.
    pub fn is_fresh_consensus_hash(
        &mut self,
        consensus_hash_lifetime: u64,
        consensus_hash: &ConsensusHash,
    ) -> Result<bool, db_error> {
        self.check_fresh_consensus_hash(consensus_hash_lifetime, |fresh_hash| {
            fresh_hash == consensus_hash
        })
    }

    /// Find out whether or not a given consensus hash is "recent" enough to be used in this fork.
    /// This function only checks the first 19 bytes
    pub fn is_fresh_consensus_hash_check_19b(
        &mut self,
        consensus_hash_lifetime: u64,
        consensus_hash: &ConsensusHash,
    ) -> Result<bool, db_error> {
        self.check_fresh_consensus_hash(consensus_hash_lifetime, |fresh_hash| {
            fresh_hash.as_bytes()[0..19] == consensus_hash.as_bytes()[0..19]
        })
    }
}

impl<'a> SortitionHandleTx<'a> {
    pub fn set_stacks_block_accepted(
        &mut self,
        consensus_hash: &ConsensusHash,
        parent_stacks_block_hash: &BlockHeaderHash,
        stacks_block_hash: &BlockHeaderHash,
        stacks_block_height: u64,
    ) -> Result<(), db_error> {
        // NOTE: chain_tip here is the tip of the PoX fork on the canonical burn chain fork.
        // consensus_hash refers to the consensus hash of the tip of the canonical Stacks fork
        // we're updating.
        let chain_tip = SortitionDB::get_block_snapshot(self, &self.context.chain_tip)?.expect(
            "FAIL: Setting stacks block accepted in canonical chain tip which cannot be found",
        );
        self.set_stacks_block_accepted_at_tip(
            &chain_tip,
            consensus_hash,
            parent_stacks_block_hash,
            stacks_block_hash,
            stacks_block_height,
        )
    }

    /// Get the expected PoX recipients (reward set) for the next sortition, either by querying information
    ///  from the current reward cycle, or if `next_pox_info` is provided, by querying information
    ///  for the next reward cycle.
    ///
    /// Returns None if:
    ///   * The reward cycle had an anchor block, but it isn't known by this node.
    ///   * The reward cycle did not have anchor block
    ///   * The block is in the prepare phase of a reward cycle, in which case miners must burn
    ///   * The Stacking recipient set is empty (either because this reward cycle has already exhausted the set of addresses or because no one ever Stacked).
    fn pick_recipients(
        &mut self,
        burnchain: &Burnchain,
        block_height: u64,
        reward_set_vrf_seed: &SortitionHash,
        next_pox_info: Option<&RewardCycleInfo>,
    ) -> Result<Option<RewardSetInfo>, BurnchainError> {
        if let Some(next_pox_info) = next_pox_info {
            if let PoxAnchorBlockStatus::SelectedAndKnown(ref anchor_block, ref reward_set) =
                next_pox_info.anchor_status
            {
                if burnchain.is_in_prepare_phase(block_height) {
                    debug!(
                        "No recipients for block {}, since in prepare phase",
                        block_height
                    );
                    return Ok(None);
                }

                test_debug!(
                    "Pick recipients for anchor block {} -- {} reward recipient(s)",
                    anchor_block,
                    reward_set.len()
                );
                if reward_set.len() == 0 {
                    return Ok(None);
                }

                if OUTPUTS_PER_COMMIT != 2 {
                    unreachable!("BUG: PoX reward address selection only implemented for OUTPUTS_PER_COMMIT = 2");
                }

                let chosen_recipients = reward_set_vrf_seed.choose_two(
                    reward_set
                        .len()
                        .try_into()
                        .expect("BUG: u32 overflow in PoX outputs per commit"),
                );

                Ok(Some(RewardSetInfo {
                    anchor_block: anchor_block.clone(),
                    recipients: chosen_recipients
                        .into_iter()
                        .map(|ix| {
                            let recipient = reward_set[ix as usize].clone();
                            info!("PoX recipient chosen";
                                   "recipient" => recipient.clone().to_b58(),
                                   "block_height" => block_height);
                            (recipient, u16::try_from(ix).unwrap())
                        })
                        .collect(),
                }))
            } else {
                test_debug!("No anchor block known for this reward cycle");
                Ok(None)
            }
        } else {
            let last_anchor = self.get_last_anchor_block_hash()?;
            if let Some(anchor_block) = last_anchor {
                // known
                // get the reward set size
                let reward_set_size = self.get_reward_set_size()?;
                if reward_set_size == 0 {
                    test_debug!(
                        "No more reward recipients descending from anchor block {}",
                        anchor_block
                    );
                    Ok(None)
                } else {
                    let chosen_recipients = reward_set_vrf_seed.choose_two(reward_set_size as u32);
                    let mut recipients = vec![];
                    for ix in chosen_recipients.into_iter() {
                        let ix = u16::try_from(ix).unwrap();
                        let recipient = self.get_reward_set_entry(ix)?;
                        info!("PoX recipient chosen";
                               "recipient" => recipient.clone().to_b58(),
                               "block_height" => block_height);
                        recipients.push((recipient, ix));
                    }
                    Ok(Some(RewardSetInfo {
                        anchor_block,
                        recipients,
                    }))
                }
            } else {
                // no anchor block selected
                test_debug!("No anchor block selected for this reward cycle");
                Ok(None)
            }
        }
    }

    fn get_reward_set_entry(&mut self, entry_ix: u16) -> Result<StacksAddress, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let entry_str = self
            .get_indexed(&chain_tip, &db_keys::pox_reward_set_entry(entry_ix))?
            .expect(&format!(
                "CORRUPTION: expected reward set entry at index={}, but not found",
                entry_ix
            ));
        Ok(StacksAddress::from_string(&entry_str).expect(&format!(
            "CORRUPTION: bad address formatting in database: {}",
            &entry_str
        )))
    }

    fn get_reward_set_size(&mut self) -> Result<u16, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        self.get_indexed(&chain_tip, db_keys::pox_reward_set_size())
            .map(|x| {
                db_keys::reward_set_size_from_string(
                    &x.expect("CORRUPTION: no current reward set size written"),
                )
            })
    }

    /// is the given block a descendant of `potential_ancestor`?
    ///  * block_at_burn_height: the burn height of the sortition that chose the stacks block to check
    ///  * potential_ancestor: the stacks block hash of the potential ancestor
    pub fn descended_from(
        &mut self,
        block_at_burn_height: u64,
        potential_ancestor: &BlockHeaderHash,
    ) -> Result<bool, db_error> {
        let earliest_block_height = self.tx().query_row(
            "SELECT block_height FROM snapshots WHERE winning_stacks_block_hash = ? ORDER BY block_height ASC LIMIT 1",
            &[potential_ancestor],
            |row| Ok(u64::from_row(row).expect("Expected u64 in database")))?;

        let mut sn = self
            .get_block_snapshot_by_height(block_at_burn_height)?
            .ok_or_else(|| db_error::NotFoundError)?;
        while sn.block_height >= earliest_block_height {
            if !sn.sortition {
                return Ok(false);
            }
            if &sn.winning_stacks_block_hash == potential_ancestor {
                return Ok(true);
            }

            // step back to the parent
            let block_commit = get_block_commit_by_txid(&self.tx(), &sn.winning_block_txid)?
                .expect("CORRUPTION: winning block commit for snapshot not found");
            sn = self
                .get_block_snapshot_by_height(block_commit.parent_block_ptr as u64)?
                .ok_or_else(|| db_error::NotFoundError)?;
        }
        return Ok(false);
    }

    pub fn get_block_snapshot_by_height(
        &mut self,
        block_height: u64,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let chain_tip = self.context.chain_tip.clone();
        SortitionDB::get_ancestor_snapshot_tx(self, block_height, &chain_tip)
    }

    pub fn get_last_anchor_block_hash(&mut self) -> Result<Option<BlockHeaderHash>, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let anchor_block_hash = SortitionDB::parse_last_anchor_block_hash(
            self.get_indexed(&chain_tip, &db_keys::pox_last_anchor())?,
        );
        Ok(anchor_block_hash)
    }

    /// Mark an existing snapshot's stacks block as accepted at a particular burn chain tip within a PoX fork (identified by the consensus hash),
    /// and calculate and store its arrival index.
    /// If this Stacks block extends the canonical stacks chain tip, then also update the memoized canonical
    /// stacks chain tip metadata on the burn chain tip.
    // TODO: this method's inner call to get_indexed() occurs within a MARF transaction, which
    // means it will clone() the underlying TrieRAM.  Until this is rectified, care should be taken
    // to ensure that no keys are inserted until after this method is called.  This should already
    // be the case, since the only time keys are inserted into the sortition DB MARF is when the
    // next snapshot is processed (whereas this method is called when a Stacks epoch is processed).
    fn set_stacks_block_accepted_at_tip(
        &mut self,
        burn_tip: &BlockSnapshot,
        consensus_hash: &ConsensusHash,
        parent_stacks_block_hash: &BlockHeaderHash,
        stacks_block_hash: &BlockHeaderHash,
        stacks_block_height: u64,
    ) -> Result<(), db_error> {
        let arrival_index = SortitionDB::get_max_arrival_index(self)?;
        let args: &[&dyn ToSql] = &[
            &u64_to_sql(stacks_block_height)?,
            &u64_to_sql(arrival_index + 1)?,
            consensus_hash,
            stacks_block_hash,
        ];

        self.execute("UPDATE snapshots SET stacks_block_accepted = 1, stacks_block_height = ?1, arrival_index = ?2 WHERE consensus_hash = ?3 AND winning_stacks_block_hash = ?4", args)?;

        let parent_key = db_keys::stacks_block_index(parent_stacks_block_hash);

        // update memoized canonical stacks chain tip on the canonical burn chain tip if this block
        // extends it.
        if burn_tip.canonical_stacks_tip_hash == *parent_stacks_block_hash {
            // This block builds off of the memoized canonical stacks chain tip information we
            // already have.
            // Memoize this tip to the canonical burn chain snapshot.
            if stacks_block_height > 0 {
                assert_eq!(
                    burn_tip.canonical_stacks_tip_height + 1,
                    stacks_block_height
                );
            } else {
                assert_eq!(stacks_block_hash, &FIRST_STACKS_BLOCK_HASH);
            }
            debug!(
                "Accepted Stacks block {}/{} builds on the memoized canonical chain tip ({})",
                consensus_hash, stacks_block_hash, &burn_tip.burn_header_hash
            );
            let args: &[&dyn ToSql] = &[
                consensus_hash,
                stacks_block_hash,
                &u64_to_sql(stacks_block_height)?,
                &burn_tip.sortition_id,
            ];
            self.execute("UPDATE snapshots SET canonical_stacks_tip_consensus_hash = ?1, canonical_stacks_tip_hash = ?2, canonical_stacks_tip_height = ?3
                        WHERE sortition_id = ?4", args)?;

            SortitionDB::insert_accepted_stacks_block_pointer(
                self,
                &burn_tip.consensus_hash,
                consensus_hash,
                stacks_block_hash,
                stacks_block_height,
            )?;
        } else {
            // see if this block builds off of a Stacks block mined on this burnchain fork
            let height_opt = match SortitionDB::get_accepted_stacks_block_pointer(
                self,
                &burn_tip.consensus_hash,
                parent_stacks_block_hash,
            )? {
                // this block builds on a block accepted _after_ this burn chain tip was processed?
                Some(accepted_header) => Some(accepted_header.height),
                None => {
                    match self.get_indexed(&burn_tip.sortition_id, &parent_key)? {
                        // this block builds on a block accepted _before_ this burn chain tip was processed?
                        Some(height_str) => Some(height_str.parse::<u64>().expect(&format!(
                            "BUG: MARF stacks block key '{}' does not map to a u64",
                            parent_key
                        ))),
                        None => None,
                    }
                }
            };
            match height_opt {
                Some(height) => {
                    if stacks_block_height > burn_tip.canonical_stacks_tip_height {
                        assert!(stacks_block_height > height, "BUG: DB corruption -- block height {} <= {} means we accepted a block out-of-order", stacks_block_height, height);
                        // This block builds off of a parent that is _concurrent_ with the memoized canonical stacks chain pointer.
                        // i.e. this block will reorg the Stacks chain on the canonical burnchain fork.
                        // Memoize this new stacks chain tip to the canonical burn chain snapshot.
                        // Note that we don't have to check continuity of accepted blocks -- we already
                        // are guaranteed by the Stacks chain state code that Stacks blocks in a given
                        // Stacks fork will be marked as accepted in sequential order (i.e. at height h, h+1,
                        // h+2, etc., without any gaps).
                        debug!("Accepted Stacks block {}/{} builds on a previous canonical Stacks tip on this burnchain fork ({})", consensus_hash, stacks_block_hash, &burn_tip.burn_header_hash);
                        let args: &[&dyn ToSql] = &[
                            consensus_hash,
                            stacks_block_hash,
                            &u64_to_sql(stacks_block_height)?,
                            &burn_tip.sortition_id,
                        ];
                        self.execute("UPDATE snapshots SET canonical_stacks_tip_consensus_hash = ?1, canonical_stacks_tip_hash = ?2, canonical_stacks_tip_height = ?3
                                    WHERE sortition_id = ?4", args)
                            .map_err(db_error::SqliteError)?;
                    } else {
                        // This block was mined on this fork, but it's acceptance doesn't overtake
                        // the current stacks chain tip.  Remember it so that we can process its children,
                        // which might do so later.
                        debug!("Accepted Stacks block {}/{} builds on a non-canonical Stacks tip in this burnchain fork ({})", consensus_hash, stacks_block_hash, &burn_tip.burn_header_hash);
                    }
                    SortitionDB::insert_accepted_stacks_block_pointer(
                        self,
                        &burn_tip.consensus_hash,
                        consensus_hash,
                        stacks_block_hash,
                        stacks_block_height,
                    )?;
                }
                None => {
                    debug!("Accepted Stacks block {}/{} does NOT build on a Stacks tip in this burnchain fork ({}) -- no parent {} in this fork", consensus_hash, stacks_block_hash, &burn_tip.burn_header_hash, parent_stacks_block_hash);
                }
            }
        }
        Ok(())
    }
}

impl<'a> SortitionHandleConn<'a> {
    /// open a reader handle from a consensus hash
    pub fn open_reader_consensus(
        connection: &'a SortitionDBConn<'a>,
        chain_tip: &ConsensusHash,
    ) -> Result<SortitionHandleConn<'a>, db_error> {
        let sn = match SortitionDB::get_block_snapshot_consensus(&connection.conn(), chain_tip)? {
            Some(sn) => {
                if !sn.pox_valid {
                    warn!(
                        "No such chain tip consensus hash {}: not on a valid PoX fork",
                        chain_tip
                    );
                    return Err(db_error::InvalidPoxSortition);
                }
                sn
            }
            None => {
                test_debug!("No such chain tip consensus hash {}", chain_tip);
                return Err(db_error::NotFoundError);
            }
        };

        SortitionHandleConn::open_reader(connection, &sn.sortition_id)
    }

    #[cfg(test)]
    pub fn get_last_anchor_block_hash(&self) -> Result<Option<BlockHeaderHash>, db_error> {
        let anchor_block_hash = SortitionDB::parse_last_anchor_block_hash(
            self.get_indexed(&self.context.chain_tip, &db_keys::pox_last_anchor())?,
        );
        Ok(anchor_block_hash)
    }

    fn get_reward_set_size(&self) -> Result<u16, db_error> {
        self.get_tip_indexed(&db_keys::pox_reward_set_size())
            .map(|x| {
                db_keys::reward_set_size_from_string(
                    &x.expect("CORRUPTION: no current reward set size written"),
                )
            })
    }

    pub fn get_pox_id(&self) -> Result<PoxId, db_error> {
        let pox_id = self
            .get_tip_indexed(db_keys::pox_identifier())?
            .map(|s| s.parse().expect("BUG: Bad PoX identifier stored in DB"))
            .expect("BUG: No PoX identifier stored.");
        Ok(pox_id)
    }

    /// open a reader handle
    pub fn open_reader(
        connection: &'a SortitionDBConn<'a>,
        chain_tip: &SortitionId,
    ) -> Result<SortitionHandleConn<'a>, db_error> {
        Ok(SortitionHandleConn {
            context: SortitionHandleContext {
                chain_tip: chain_tip.clone(),
                first_block_height: connection.context.first_block_height,
            },
            index: &connection.index,
        })
    }

    fn get_tip_indexed(&self, key: &str) -> Result<Option<String>, db_error> {
        self.get_indexed(&self.context.chain_tip, key)
    }

    fn get_sortition_id_for_bhh(
        &self,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<SortitionId>, db_error> {
        let sortition_identifier_key = db_keys::sortition_id_for_bhh(burn_header_hash);
        let sortition_id = match self.get_tip_indexed(&sortition_identifier_key)? {
            None => return Ok(None),
            Some(x) => SortitionId::from_hex(&x).expect("FATAL: bad Sortition ID stored in DB"),
        };
        Ok(Some(sortition_id))
    }

    /// Uses the handle's current fork identifier to get a block snapshot by
    ///   burnchain block header
    /// If the burn header hash is _not_ in the current fork, then this will return Ok(None)
    pub fn get_block_snapshot(
        &self,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let sortition_id = match self.get_sortition_id_for_bhh(burn_header_hash)? {
            None => return Ok(None),
            Some(x) => x,
        };
        SortitionDB::get_block_snapshot(self.conn(), &sortition_id)
    }

    pub fn get_tip_snapshot(&self) -> Result<Option<BlockSnapshot>, db_error> {
        SortitionDB::get_block_snapshot(self.conn(), &self.context.chain_tip)
    }

    pub fn get_first_block_snapshot(&self) -> Result<BlockSnapshot, db_error> {
        SortitionDB::get_first_block_snapshot(self.conn())
    }

    /// Get consensus hash from a particular chain tip's history
    /// Returns None if the block height or block hash does not correspond to a
    /// known snapshot.
    pub fn get_consensus_at(&self, block_height: u64) -> Result<Option<ConsensusHash>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);

        match SortitionDB::get_ancestor_snapshot(self, block_height, &self.context.chain_tip)? {
            Some(sn) => Ok(Some(sn.consensus_hash)),
            None => Ok(None),
        }
    }

    pub fn get_block_snapshot_by_height(
        &self,
        block_height: u64,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);

        SortitionDB::get_ancestor_snapshot(self, block_height, &self.context.chain_tip)
    }

    /// Get all user burns that burned for the winning block in the chain_tip sortition
    /// Returns list of user burns in order by vtxindex.
    pub fn get_winning_user_burns_by_block(&self) -> Result<Vec<UserBurnSupportOp>, db_error> {
        let snapshot = match self.get_tip_snapshot()? {
            Some(sn) => sn,
            None => {
                // no such snapshot, so no such users
                return Ok(vec![]);
            }
        };

        if !snapshot.sortition {
            // no winner
            return Ok(vec![]);
        }
        let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 AND txid = ?2";
        let args: [&dyn ToSql; 2] = [&snapshot.sortition_id, &snapshot.winning_block_txid];
        let winning_commit: LeaderBlockCommitOp = query_row(self, qry, &args)?
            .expect("BUG: sortition exists, but winner cannot be found");

        let winning_block_hash160 =
            Hash160::from_sha256(snapshot.winning_stacks_block_hash.as_bytes());

        let qry = "SELECT * FROM user_burn_support
                   WHERE sortition_id = ?1 AND block_header_hash_160 = ?2 AND key_vtxindex = ?3 AND key_block_ptr = ?4
                   ORDER BY vtxindex ASC";
        let args: [&dyn ToSql; 4] = [
            &snapshot.sortition_id,
            &winning_block_hash160,
            &winning_commit.key_vtxindex,
            &winning_commit.key_block_ptr,
        ];

        let mut winning_user_burns: Vec<UserBurnSupportOp> = query_rows(self, qry, &args)?;

        // were there multiple miners with the same VRF key and block header hash? (i.e., are these user burns shared?)
        let qry = "SELECT COUNT(*) FROM block_commits
                   WHERE sortition_id = ?1 AND block_header_hash = ?2 AND key_vtxindex = ?3 AND key_block_ptr = ?4";
        let args: [&dyn ToSql; 4] = [
            &snapshot.sortition_id,
            &snapshot.winning_stacks_block_hash,
            &winning_commit.key_vtxindex,
            &winning_commit.key_block_ptr,
        ];
        let shared_miners = query_count(self, qry, &args)? as u64;

        assert!(
            shared_miners >= 1,
            "BUG: Should be at least 1 matching miner for the winning block commit"
        );

        for winning_user_burn in winning_user_burns.iter_mut() {
            winning_user_burn.burn_fee /= shared_miners;
        }

        Ok(winning_user_burns)
    }

    /// Get the block snapshot of the parent stacks block of the given stacks block
    pub fn get_block_snapshot_of_parent_stacks_block(
        &self,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<(LeaderBlockCommitOp, BlockSnapshot)>, db_error> {
        let block_commit = match SortitionDB::get_block_commit_for_stacks_block(
            self.conn(),
            consensus_hash,
            &block_hash,
        )? {
            Some(bc) => bc,
            None => {
                // unsoliciated
                debug!("No block commit for {}/{}", consensus_hash, block_hash);
                return Ok(None);
            }
        };

        // get the stacks chain tip this block commit builds off of
        let stacks_chain_tip =
            if block_commit.parent_block_ptr == 0 && block_commit.parent_vtxindex == 0 {
                // no parent -- this is the first-ever Stacks block in this fork
                test_debug!(
                    "Block {}/{} mines off of genesis",
                    consensus_hash,
                    block_hash
                );
                self.get_first_block_snapshot()?
            } else {
                let parent_commit = match self.get_block_commit_parent(
                    block_commit.parent_block_ptr.into(),
                    block_commit.parent_vtxindex.into(),
                )? {
                    Some(commit) => commit,
                    None => {
                        // unsolicited -- orphaned
                        warn!(
                        "Received unsolicited block, could not find parent: {}/{}, parent={}/{}",
                        consensus_hash, block_hash, block_commit.parent_block_ptr, consensus_hash
                    );
                        return Ok(None);
                    }
                };

                debug!(
                    "Block {}/{} mines off of parent {},{}",
                    consensus_hash, block_hash, parent_commit.block_height, parent_commit.vtxindex
                );
                self.get_block_snapshot(&parent_commit.burn_header_hash)?
                    .expect("FATAL: burn DB does not have snapshot for parent block commit")
            };

        Ok(Some((block_commit, stacks_chain_tip)))
    }

    /// Get the latest block snapshot on this fork where a sortition occured.
    /// Search snapshots up to (but excluding) the given block height.
    /// Will always return a snapshot -- even if it's the initial sentinel snapshot.
    pub fn get_last_snapshot_with_sortition(
        &self,
        burn_block_height: u64,
    ) -> Result<BlockSnapshot, db_error> {
        assert!(burn_block_height < BLOCK_HEIGHT_MAX);
        test_debug!(
            "Get snapshot at from sortition tip {}, expect height {}",
            &self.context.chain_tip,
            burn_block_height
        );
        let get_from = match get_ancestor_sort_id(self, burn_block_height, &self.context.chain_tip)?
        {
            Some(sortition_id) => sortition_id,
            None => {
                error!(
                    "No blockheight {} ancestor at sortition identifier {}",
                    burn_block_height, &self.context.chain_tip
                );
                return Err(db_error::NotFoundError);
            }
        };

        let ancestor_hash = match self.get_indexed(&get_from, &db_keys::last_sortition())? {
            Some(hex_str) => BurnchainHeaderHash::from_hex(&hex_str).expect(&format!(
                "FATAL: corrupt database: failed to parse {} into a hex string",
                &hex_str
            )),
            None => {
                // no prior sortitions, so get the first
                return self.get_first_block_snapshot();
            }
        };

        self.get_block_snapshot(&ancestor_hash).map(|snapshot_opt| {
            snapshot_opt.expect(&format!(
                "FATAL: corrupt index: no snapshot {}",
                ancestor_hash
            ))
        })
    }

    pub fn get_leader_key_at(
        &self,
        key_block_height: u64,
        key_vtxindex: u32,
    ) -> Result<Option<LeaderKeyRegisterOp>, db_error> {
        SortitionDB::get_leader_key_at(
            self,
            key_block_height,
            key_vtxindex,
            &self.context.chain_tip,
        )
    }

    pub fn get_block_commit_parent(
        &self,
        block_height: u64,
        vtxindex: u32,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        SortitionDB::get_block_commit_parent(self, block_height, vtxindex, &self.context.chain_tip)
    }

    /// Get a block commit by txid. In the event of a burnchain fork, this may not be unique.
    ///   this function simply returns one of those block commits: only use data that is
    ///   immutable across burnchain/pox forks, e.g., parent block ptr,  
    pub fn get_block_commit_by_txid(
        &self,
        txid: &Txid,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        get_block_commit_by_txid(self.conn(), txid)
    }

    /// Return a vec of sortition winner's burn header hash and stacks header hash, ordered by
    ///   increasing block height in the range (block_height_begin, block_height_end]
    fn get_sortition_winners_in_fork(
        &self,
        block_height_begin: u32,
        block_height_end: u32,
    ) -> Result<Vec<(Txid, u64)>, BurnchainError> {
        let mut result = vec![];
        for height in (block_height_begin + 1)..(block_height_end + 1) {
            debug!("Looking for winners at height = {}", height);
            let snapshot =
                SortitionDB::get_ancestor_snapshot(self, height as u64, &self.context.chain_tip)?
                    .ok_or_else(|| {
                    warn!("Missing parent"; "sortition_height" => %height);
                    BurnchainError::MissingParentBlock
                })?;
            if snapshot.sortition {
                result.push((snapshot.winning_block_txid, snapshot.block_height));
            }
        }
        Ok(result)
    }

    /// Return identifying information for a PoX anchor block for the reward cycle that
    ///   begins the block after `prepare_end_bhh`.
    /// If a PoX anchor block is chosen, this returns Some, if a PoX anchor block was not
    ///   selected, return `None`
    /// `prepare_end_bhh`: this is the burn block which is the last block in the prepare phase
    ///                 for the corresponding reward cycle
    pub fn get_chosen_pox_anchor(
        &self,
        prepare_end_bhh: &BurnchainHeaderHash,
        pox_consts: &PoxConstants,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash)>, CoordinatorError> {
        match self.get_chosen_pox_anchor_check_position(prepare_end_bhh, pox_consts, true) {
            Ok(Ok((c_hash, bh_hash, _))) => Ok(Some((c_hash, bh_hash))),
            Ok(Err(_)) => Ok(None),
            Err(e) => Err(e),
        }
    }

    pub fn get_chosen_pox_anchor_check_position(
        &self,
        prepare_end_bhh: &BurnchainHeaderHash,
        pox_consts: &PoxConstants,
        check_position: bool,
    ) -> Result<Result<(ConsensusHash, BlockHeaderHash, u32), u32>, CoordinatorError> {
        let prepare_end_sortid =
            self.get_sortition_id_for_bhh(prepare_end_bhh)?
                .ok_or_else(|| {
                    warn!("Missing parent"; "burn_header_hash" => %prepare_end_bhh);
                    BurnchainError::MissingParentBlock
                })?;
        let block_height = SortitionDB::get_block_height(self.deref(), &prepare_end_sortid)?
            .expect("CORRUPTION: SortitionID known, but no block height in SQL store");

        // if this block is the _end_ of a prepare phase,
        let effective_height = block_height - self.context.first_block_height as u32;
        let position_in_cycle = effective_height % pox_consts.reward_cycle_length;
        if position_in_cycle != 0 {
            debug!(
                "effective_height = {}, reward cycle length == {}",
                effective_height, pox_consts.reward_cycle_length
            );
            if check_position {
                return Err(CoordinatorError::NotPrepareEndBlock);
            }
        }

        if effective_height == 0 {
            debug!(
                "effective_height = {}, reward cycle length == {}",
                effective_height, pox_consts.reward_cycle_length
            );
            return Ok(Err(0));
        }

        let prepare_end = block_height;
        let prepare_begin = prepare_end.saturating_sub(pox_consts.prepare_length);

        let mut candidate_anchors = HashMap::new();
        let mut memoized_candidates: HashMap<_, (Txid, u64)> = HashMap::new();

        // iterate over every sortition winner in the prepare phase
        //   looking for their highest ancestor _before_ prepare_begin.
        let winners = self.get_sortition_winners_in_fork(prepare_begin, prepare_end)?;
        for (winner_commit_txid, winner_block_height) in winners.into_iter() {
            let mut cursor = (winner_commit_txid, winner_block_height);
            let mut found_ancestor = true;

            while cursor.1 > (prepare_begin as u64) {
                // check if we've already discovered the candidate for this block
                if let Some(ancestor) = memoized_candidates.get(&cursor.1) {
                    cursor = ancestor.clone();
                } else {
                    // get the block commit
                    let block_commit = self.get_block_commit_by_txid(&cursor.0)?.expect(
                        "CORRUPTED: Failed to fetch block commit for known sortition winner",
                    );
                    // is this a height=1 block?
                    if block_commit.is_parent_genesis() {
                        debug!("First parent before prepare phase for block winner is the genesis block, dropping block's PoX anchor vote";
                               "winner_txid" => %&cursor.0,
                               "burn_block_height" => cursor.1);
                        found_ancestor = false;
                        break;
                    }

                    // find the parent sortition
                    let sn = SortitionDB::get_ancestor_snapshot(
                        self,
                        block_commit.parent_block_ptr as u64,
                        &self.context.chain_tip,
                    )?
                    .expect(
                        "CORRUPTED: accepted block commit, but parent pointer not in sortition set",
                    );
                    assert!(sn.sortition, "CORRUPTED: accepted block commit, but parent pointer not a sortition winner");

                    cursor = (sn.winning_block_txid, sn.block_height);
                }
            }
            if !found_ancestor {
                continue;
            }
            // this is the burn block height of the sortition that chose the
            //   highest ancestor of winner_stacks_bh whose sortition occurred before prepare_begin
            //  the winner of that sortition is the PoX anchor block candidate that winner_stacks_bh is "voting for"
            let highest_ancestor = cursor.1;
            memoized_candidates.insert(winner_block_height, cursor);
            if let Some(x) = candidate_anchors.get_mut(&highest_ancestor) {
                *x += 1;
            } else {
                candidate_anchors.insert(highest_ancestor, 1u32);
            }
        }

        // did any candidate receive >= F*w?
        let mut result = None;
        let mut max_confirmed_by = 0;
        for (candidate, confirmed_by) in candidate_anchors.into_iter() {
            if confirmed_by > max_confirmed_by {
                max_confirmed_by = confirmed_by;
            }
            if confirmed_by >= pox_consts.anchor_threshold {
                // find the sortition at height
                let sn =
                    SortitionDB::get_ancestor_snapshot(self, candidate, &self.context.chain_tip)?
                        .expect("BUG: cannot find chosen PoX candidate's sortition");
                assert!(
                    result
                        .replace((
                            sn.consensus_hash,
                            sn.winning_stacks_block_hash,
                            confirmed_by
                        ))
                        .is_none(),
                    "BUG: multiple anchor blocks received more confirmations than anchor_threshold"
                );
            }
        }

        let reward_cycle_id = effective_height / pox_consts.reward_cycle_length;
        match result {
            None => {
                info!(
                    "Reward cycle #{} ({}): (F*w) not reached, expecting consensus over proof of burn",
                    reward_cycle_id, block_height
                );
                Ok(Err(max_confirmed_by))
            }
            Some(response) => {
                info!("Reward cycle #{} ({}): {:?} reached (F*w), expecting consensus over proof of transfer", reward_cycle_id, block_height, result);
                Ok(Ok(response))
            }
        }
    }
}

impl FromStr for PoxId {
    type Err = NetError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = vec![];
        for i in s.chars() {
            if i == '1' {
                result.push(true);
            } else if i == '0' {
                result.push(false);
            } else {
                return Err(NetError::DeserializeError(
                    "Unexpected character in PoX ID serialization".into(),
                ));
            }
        }
        Ok(PoxId::new(result))
    }
}

impl SortitionId {
    pub fn stubbed(from: &BurnchainHeaderHash) -> SortitionId {
        SortitionId::new(from, &PoxId::stubbed())
    }

    pub fn new(bhh: &BurnchainHeaderHash, pox: &PoxId) -> SortitionId {
        if pox == &PoxId::stubbed() {
            SortitionId(bhh.0.clone())
        } else {
            let mut hasher = Sha512Trunc256::new();
            hasher.input(bhh);
            write!(hasher, "{}", pox).expect("Failed to deserialize PoX ID into the hasher");
            let h = Sha512Trunc256Sum::from_hasher(hasher);
            SortitionId(h.0)
        }
    }
}

// Connection methods
impl SortitionDB {
    /// Begin a transaction.
    pub fn tx_begin<'a>(&'a mut self) -> Result<SortitionDBTx<'a>, db_error> {
        if !self.readwrite {
            return Err(db_error::ReadOnly);
        }

        let index_tx = SortitionDBTx::new(
            &mut self.marf,
            SortitionDBTxContext {
                first_block_height: self.first_block_height,
            },
        );
        Ok(index_tx)
    }

    /// Make an indexed connectino
    pub fn index_conn<'a>(&'a self) -> SortitionDBConn<'a> {
        SortitionDBConn::new(
            &self.marf,
            SortitionDBTxContext {
                first_block_height: self.first_block_height,
            },
        )
    }

    pub fn index_handle<'a>(&'a self, chain_tip: &SortitionId) -> SortitionHandleConn<'a> {
        SortitionHandleConn::new(
            &self.marf,
            SortitionHandleContext {
                first_block_height: self.first_block_height,
                chain_tip: chain_tip.clone(),
            },
        )
    }

    pub fn tx_handle_begin<'a>(
        &'a mut self,
        chain_tip: &SortitionId,
    ) -> Result<SortitionHandleTx<'a>, db_error> {
        if !self.readwrite {
            return Err(db_error::ReadOnly);
        }

        Ok(SortitionHandleTx::new(
            &mut self.marf,
            SortitionHandleContext {
                first_block_height: self.first_block_height,
                chain_tip: chain_tip.clone(),
            },
        ))
    }

    pub fn conn<'a>(&'a self) -> &'a Connection {
        self.marf.sqlite_conn()
    }

    fn open_index(index_path: &str) -> Result<MARF<SortitionId>, db_error> {
        test_debug!("Open index at {}", index_path);
        MARF::from_path(index_path).map_err(|_e| db_error::Corruption)
    }

    /// Open the database on disk.  It must already exist and be instantiated.
    /// It's best not to call this if you are able to call connect().  If you must call this, do so
    /// after you call connect() somewhere else, since connect() performs additional validations.
    pub fn open(path: &str, readwrite: bool) -> Result<SortitionDB, db_error> {
        let (db_path, index_path) = db_mkdirs(path)?;
        debug!(
            "Open sortdb '{}' as '{}', with index as '{}'",
            db_path,
            if readwrite { "readwrite" } else { "readonly" },
            index_path
        );

        let marf = SortitionDB::open_index(&index_path)?;
        let first_snapshot = SortitionDB::get_first_block_snapshot(marf.sqlite_conn())?;

        let db = SortitionDB {
            marf,
            readwrite,
            first_block_height: first_snapshot.block_height,
            first_burn_header_hash: first_snapshot.burn_header_hash.clone(),
        };
        Ok(db)
    }

    /// Open the burn database at the given path.  Open read-only or read/write.
    /// If opened for read/write and it doesn't exist, instantiate it.
    pub fn connect(
        path: &str,
        first_block_height: u64,
        first_burn_hash: &BurnchainHeaderHash,
        first_burn_header_timestamp: u64,
        readwrite: bool,
    ) -> Result<SortitionDB, db_error> {
        let create_flag = match fs::metadata(path) {
            Err(e) => {
                if e.kind() == ErrorKind::NotFound {
                    // need to create
                    if readwrite {
                        true
                    } else {
                        return Err(db_error::NoDBError);
                    }
                } else {
                    return Err(db_error::IOError(e));
                }
            }
            Ok(_md) => false,
        };

        let (db_path, index_path) = db_mkdirs(path)?;
        debug!(
            "Connect/Open {} sortdb '{}' as '{}', with index as '{}'",
            if create_flag { "(create)" } else { "" },
            db_path,
            if readwrite { "readwrite" } else { "readonly" },
            index_path
        );

        let marf = SortitionDB::open_index(&index_path)?;

        let mut db = SortitionDB {
            marf,
            readwrite,
            first_block_height,
            first_burn_header_hash: first_burn_hash.clone(),
        };

        if create_flag {
            // instantiate!
            db.instantiate(
                first_block_height,
                first_burn_hash,
                first_burn_header_timestamp,
            )?;
        } else {
            // validate -- must contain the given first block and first block hash
            let snapshot = SortitionDB::get_first_block_snapshot(db.conn())?;
            if !snapshot.is_initial()
                || snapshot.block_height != first_block_height
                || snapshot.burn_header_hash != *first_burn_hash
            {
                error!("Invalid genesis snapshot: sn.is_initial = {}, sn.block_height = {}, sn.burn_hash = {}, expect.block_height = {}, expect.burn_hash = {}",
                       snapshot.is_initial(), snapshot.block_height, &snapshot.burn_header_hash, first_block_height, first_burn_hash);
                return Err(db_error::Corruption);
            }
        }

        Ok(db)
    }

    /// Open a burn database at random tmp dir (used for testing)
    #[cfg(test)]
    pub fn connect_test(
        first_block_height: u64,
        first_burn_hash: &BurnchainHeaderHash,
    ) -> Result<SortitionDB, db_error> {
        let mut rng = rand::thread_rng();
        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        let db_path_dir = format!("/tmp/test-blockstack-sortdb-{}", to_hex(&buf));

        SortitionDB::connect(
            &db_path_dir,
            first_block_height,
            first_burn_hash,
            get_epoch_time_secs(),
            true,
        )
    }

    fn instantiate(
        &mut self,
        first_block_height: u64,
        first_burn_header_hash: &BurnchainHeaderHash,
        first_burn_header_timestamp: u64,
    ) -> Result<(), db_error> {
        debug!("Instantiate SortDB");

        sql_pragma(self.conn(), "PRAGMA journal_mode = WAL;")?;

        let mut db_tx = SortitionHandleTx::begin(self, &SortitionId::sentinel())?;

        // create first (sentinel) snapshot
        debug!("Make first snapshot");
        let mut first_snapshot = BlockSnapshot::initial(
            first_block_height,
            first_burn_header_hash,
            first_burn_header_timestamp,
        );

        assert!(first_snapshot.parent_burn_header_hash != first_snapshot.burn_header_hash);
        assert_eq!(
            first_snapshot.parent_burn_header_hash,
            BurnchainHeaderHash::sentinel()
        );

        for row_text in SORTITION_DB_INITIAL_SCHEMA {
            db_tx.execute_batch(row_text)?;
        }

        db_tx.execute(
            "INSERT INTO db_config (version) VALUES (?1)",
            &[&SORTITION_DB_VERSION],
        )?;

        db_tx.instantiate_index()?;

        let mut first_sn = first_snapshot.clone();
        first_sn.sortition_id = SortitionId::sentinel();
        let index_root =
            db_tx.index_add_fork_info(&mut first_sn, &first_snapshot, &vec![], None, None, None)?;
        first_snapshot.index_root = index_root;

        db_tx.insert_block_snapshot(&first_snapshot)?;
        db_tx.store_transition_ops(
            &first_snapshot.sortition_id,
            &BurnchainStateTransition::noop(),
        )?;

        db_tx.commit()?;
        Ok(())
    }

    /// Get a block commit by its content-addressed location in a specific sortition.
    pub fn get_block_commit(
        conn: &Connection,
        txid: &Txid,
        sortition_id: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        let qry = "SELECT * FROM block_commits WHERE txid = ?1 AND sortition_id = ?2";
        let args: [&dyn ToSql; 2] = [&txid, &sortition_id];
        query_row(conn, qry, &args)
    }

    /// Load up all snapshots, in ascending order by block height.  Great for testing!
    pub fn get_all_snapshots(&self) -> Result<Vec<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots ORDER BY block_height ASC";
        query_rows(self.conn(), qry, NO_PARAMS)
    }
}

impl<'a> SortitionDBConn<'a> {
    pub fn as_handle<'b>(&'b self, chain_tip: &SortitionId) -> SortitionHandleConn<'b> {
        SortitionHandleConn {
            index: self.index,
            context: SortitionHandleContext {
                first_block_height: self.context.first_block_height.clone(),
                chain_tip: chain_tip.clone(),
            },
        }
    }

    /// Given a burnchain consensus hash,
    /// go get the last N Stacks block headers that won sortition
    /// leading up to the given header hash.  The ith slot in the vector will be Some(...) if there
    /// was a sortition, and None if not.
    /// Returns up to num_headers prior block header hashes.
    /// The list of hashes will be in ascending order -- the lowest-height block is item 0.
    /// The last hash will be the hash for the given consensus hash.
    pub fn get_stacks_header_hashes(
        &self,
        num_headers: u64,
        tip_consensus_hash: &ConsensusHash,
        cache: &BlockHeaderCache,
    ) -> Result<Vec<(ConsensusHash, Option<BlockHeaderHash>)>, db_error> {
        let mut ret = vec![];
        let tip_snapshot = SortitionDB::get_block_snapshot_consensus(self, tip_consensus_hash)?
            .ok_or_else(|| db_error::NotFoundError)?;

        if !tip_snapshot.pox_valid {
            warn!("Consensus hash {:?} corresponds to a sortition that is not on the canonical PoX fork", tip_consensus_hash);
            return Err(db_error::InvalidPoxSortition);
        }

        assert!(
            tip_snapshot.block_height >= self.context.first_block_height,
            "DB corruption: have snapshot with a smaller block height than the first block height"
        );

        let db_handle = self.as_handle(&tip_snapshot.sortition_id);

        let headers_count =
            if tip_snapshot.block_height - self.context.first_block_height < num_headers {
                tip_snapshot.block_height - self.context.first_block_height
            } else {
                num_headers
            };

        let mut ancestor_consensus_hash = tip_snapshot.consensus_hash;

        for _i in 0..headers_count {
            if let Some((header_hash_opt, prev_consensus_hash)) =
                cache.get(&ancestor_consensus_hash)
            {
                // cache hit
                ret.push((ancestor_consensus_hash, header_hash_opt.clone()));
                ancestor_consensus_hash = prev_consensus_hash.clone();
                continue;
            }

            // cache miss
            let ancestor_snapshot = SortitionDB::get_block_snapshot_consensus(
                db_handle.conn(),
                &ancestor_consensus_hash,
            )?
            .expect(&format!(
                "Discontiguous index: missing block for consensus hash {}",
                ancestor_consensus_hash
            ));

            // this can happen if this call is interleaved with a PoX invalidation transaction
            if !ancestor_snapshot.pox_valid {
                warn!("Consensus hash {:?} corresponds to a sortition that is not on the canonical PoX fork", ancestor_consensus_hash);
                return Err(db_error::InvalidPoxSortition);
            }

            let header_hash_opt = if ancestor_snapshot.sortition {
                Some(ancestor_snapshot.winning_stacks_block_hash.clone())
            } else {
                None
            };

            debug!(
                "CACHE MISS {} (height {}): {:?}",
                &ancestor_consensus_hash, ancestor_snapshot.block_height, &header_hash_opt
            );

            ret.push((ancestor_snapshot.consensus_hash, header_hash_opt.clone()));

            let ancestor_snapshot_parent = SortitionDB::get_block_snapshot(
                db_handle.conn(),
                &ancestor_snapshot.parent_sortition_id,
            )?
            .expect(&format!(
                "Discontiguous index: missing parent block of parent burn header hash {}",
                &ancestor_snapshot.parent_burn_header_hash
            ));

            ancestor_consensus_hash = ancestor_snapshot_parent.consensus_hash;
        }

        ret.reverse();
        Ok(ret)
    }

    /// Get the height of a burnchain block
    pub fn inner_get_burn_block_height(
        &self,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<u64>, db_error> {
        let qry = "SELECT block_height FROM snapshots WHERE burn_header_hash = ?1 LIMIT 1";
        query_row(self.conn(), qry, &[burn_header_hash])
    }

    /// Get the burnchain hash given a height
    pub fn inner_get_burn_header_hash(
        &self,
        height: u32,
    ) -> Result<Option<BurnchainHeaderHash>, db_error> {
        let tip = SortitionDB::get_canonical_burn_chain_tip(self.conn())?;
        let ancestor_opt =
            SortitionDB::get_ancestor_snapshot(&self, height as u64, &tip.sortition_id)?
                .map(|snapshot| snapshot.burn_header_hash);
        Ok(ancestor_opt)
    }
}

// High-level functions used by ChainsCoordinator
impl SortitionDB {
    pub fn get_sortition_id(
        &self,
        burnchain_header_hash: &BurnchainHeaderHash,
        sortition_tip: &SortitionId,
    ) -> Result<Option<SortitionId>, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        handle
            .get_sortition_id_for_bhh(burnchain_header_hash)
            .map_err(BurnchainError::from)
    }

    pub fn is_sortition_processed(
        &self,
        burnchain_header_hash: &BurnchainHeaderHash,
    ) -> Result<Option<SortitionId>, BurnchainError> {
        let qry = "SELECT sortition_id FROM snapshots WHERE burn_header_hash = ? AND pox_valid = 1";
        query_row(self.conn(), qry, &[burnchain_header_hash]).map_err(BurnchainError::from)
    }

    fn get_block_height(
        conn: &Connection,
        sortition_id: &SortitionId,
    ) -> Result<Option<u32>, db_error> {
        let qry = "SELECT block_height FROM snapshots WHERE sortition_id = ? LIMIT 1";
        conn.query_row(qry, &[sortition_id], |row| row.get(0))
            .optional()
            .map_err(db_error::from)
    }

    /// Is the given block an expected PoX anchor in this sortition history?
    ///  if so, return the Stacks block hash
    pub fn is_stacks_block_pox_anchor(
        &mut self,
        block: &BlockHeaderHash,
        sortition_tip: &SortitionId,
    ) -> Result<Option<BlockHeaderHash>, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        let expects_block_as_anchor = handle
            .get_tip_indexed(&db_keys::pox_anchor_to_prepare_end(block))?
            .map(|_| block.clone());

        return Ok(expects_block_as_anchor);
    }

    fn parse_last_anchor_block_hash(s: Option<String>) -> Option<BlockHeaderHash> {
        s.map(|s| {
            if s == "" {
                None
            } else {
                Some(BlockHeaderHash::from_hex(&s).expect("BUG: Bad BlockHeaderHash stored in DB"))
            }
        })
        .flatten()
    }

    pub fn invalidate_descendants_of(
        &mut self,
        burn_block: &BurnchainHeaderHash,
    ) -> Result<(), BurnchainError> {
        let db_tx = self.tx_begin()?;
        let mut queue = vec![burn_block.clone()];

        while let Some(header) = queue.pop() {
            db_tx.tx().execute(
                "UPDATE snapshots SET pox_valid = 0 WHERE parent_burn_header_hash = ?",
                &[&header],
            )?;
            let mut stmt = db_tx.prepare(
                "SELECT DISTINCT burn_header_hash FROM snapshots WHERE parent_burn_header_hash = ?",
            )?;
            for next_header in stmt.query_map(&[&header], |row| row.get(0))? {
                queue.push(next_header?);
            }
        }

        db_tx.commit()?;
        Ok(())
    }

    /// Get the last sortition in the prepare phase that chose a particular Stacks block as the anchor,
    ///   or if the anchor is not expected, return None
    pub fn get_prepare_end_for(
        &mut self,
        sortition_tip: &SortitionId,
        anchor: &BlockHeaderHash,
    ) -> Result<Option<BlockSnapshot>, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        let prepare_end_sortid = match handle
            .get_tip_indexed(&db_keys::pox_anchor_to_prepare_end(anchor))?
        {
            Some(s) => SortitionId::from_hex(&s).expect("CORRUPTION: DB stored bad sortition ID"),
            None => return Ok(None),
        };
        let snapshot =
            SortitionDB::get_block_snapshot(self.conn(), &prepare_end_sortid)?.expect(&format!(
            "BUG: Sortition ID for prepare phase end is known, but no BlockSnapshot is stored: {}",
            &prepare_end_sortid
        ));
        Ok(Some(snapshot))
    }

    /// Get the PoX ID at the particular sortition_tip
    pub fn get_pox_id(&mut self, sortition_tip: &SortitionId) -> Result<PoxId, BurnchainError> {
        let handle = self.index_handle(sortition_tip);
        handle.get_pox_id().map_err(BurnchainError::from)
    }

    pub fn get_sortition_result(
        &self,
        id: &SortitionId,
    ) -> Result<Option<(BlockSnapshot, BurnchainStateTransitionOps)>, BurnchainError> {
        let snapshot = match SortitionDB::get_block_snapshot(self.conn(), id)? {
            Some(x) => x,
            None => return Ok(None),
        };

        let sql_transition_ops = "SELECT accepted_ops, consumed_keys FROM snapshot_transition_ops WHERE sortition_id = ?";
        let transition_ops = self
            .conn()
            .query_row(sql_transition_ops, &[id], |row| {
                let accepted_ops: String = row.get_unwrap(0);
                let consumed_leader_keys: String = row.get_unwrap(1);
                Ok(BurnchainStateTransitionOps {
                    accepted_ops: serde_json::from_str(&accepted_ops)
                        .expect("CORRUPTION: DB stored bad transition ops"),
                    consumed_leader_keys: serde_json::from_str(&consumed_leader_keys)
                        .expect("CORRUPTION: DB stored bad transition ops"),
                })
            })
            .optional()?
            .expect("CORRUPTION: DB stored BlockSnapshot, but not the transition ops");

        Ok(Some((snapshot, transition_ops)))
    }

    ///
    /// # Arguments
    /// * `burn_header` - the burnchain block header to process sortition for
    /// * `ops` - the parsed blockstack operations (will be validated in this function)
    /// * `burnchain` - a reference to the burnchain information struct
    /// * `from_tip` - tip of the "sortition chain" that is being built on
    /// * `next_pox_info` - iff this sortition is the first block in a reward cycle, this should be Some
    ///
    pub fn evaluate_sortition(
        &mut self,
        burn_header: &BurnchainBlockHeader,
        ops: Vec<BlockstackOperationType>,
        burnchain: &Burnchain,
        from_tip: &SortitionId,
        next_pox_info: Option<RewardCycleInfo>,
    ) -> Result<
        (
            BlockSnapshot,
            BurnchainStateTransition,
            Option<RewardSetInfo>,
        ),
        BurnchainError,
    > {
        let parent_sort_id = self
            .get_sortition_id(&burn_header.parent_block_hash, from_tip)?
            .ok_or_else(|| {
                warn!("Unknown block {:?}", burn_header.parent_block_hash);
                BurnchainError::MissingParentBlock
            })?;

        let mut sortition_db_handle = SortitionHandleTx::begin(self, &parent_sort_id)?;
        let parent_snapshot = sortition_db_handle
            .get_block_snapshot(&burn_header.parent_block_hash, &parent_sort_id)?
            .ok_or_else(|| {
                warn!("Unknown block {:?}", burn_header.parent_block_hash);
                BurnchainError::MissingParentBlock
            })?;

        let parent_pox = sortition_db_handle.get_pox_id()?;

        let reward_set_vrf_hash = parent_snapshot
            .sortition_hash
            .mix_burn_header(&parent_snapshot.burn_header_hash);

        let reward_set_info = if burn_header.block_height >= burnchain.pox_constants.sunset_end {
            None
        } else {
            sortition_db_handle.pick_recipients(
                burnchain,
                burn_header.block_height,
                &reward_set_vrf_hash,
                next_pox_info.as_ref(),
            )?
        };

        // Get any initial mining bonus which would be due to the winner of this block.
        let bonus_remaining =
            sortition_db_handle.get_initial_mining_bonus_remaining(&parent_sort_id)?;

        let initial_mining_bonus = if bonus_remaining > 0 {
            let mining_bonus_per_block = sortition_db_handle
                .get_initial_mining_bonus_per_block(&parent_sort_id)?
                .expect("BUG: initial mining bonus amount written, but not the per block amount.");
            cmp::min(bonus_remaining, mining_bonus_per_block)
        } else {
            0
        };

        let new_snapshot = sortition_db_handle.process_block_txs(
            &parent_snapshot,
            burn_header,
            burnchain,
            ops,
            next_pox_info,
            parent_pox,
            reward_set_info.as_ref(),
            initial_mining_bonus,
        )?;

        sortition_db_handle.store_transition_ops(&new_snapshot.0.sortition_id, &new_snapshot.1)?;

        // commit everything!
        sortition_db_handle.commit()?;
        Ok((new_snapshot.0, new_snapshot.1, reward_set_info))
    }

    #[cfg(test)]
    pub fn test_get_next_block_recipients(
        &mut self,
        burnchain: &Burnchain,
        next_pox_info: Option<&RewardCycleInfo>,
    ) -> Result<Option<RewardSetInfo>, BurnchainError> {
        let parent_snapshot = SortitionDB::get_canonical_burn_chain_tip(self.conn())?;
        self.get_next_block_recipients(burnchain, &parent_snapshot, next_pox_info)
    }

    pub fn get_next_block_recipients(
        &mut self,
        burnchain: &Burnchain,
        parent_snapshot: &BlockSnapshot,
        next_pox_info: Option<&RewardCycleInfo>,
    ) -> Result<Option<RewardSetInfo>, BurnchainError> {
        let reward_set_vrf_hash = parent_snapshot
            .sortition_hash
            .mix_burn_header(&parent_snapshot.burn_header_hash);

        let mut sortition_db_handle =
            SortitionHandleTx::begin(self, &parent_snapshot.sortition_id)?;
        if parent_snapshot.block_height + 1 >= burnchain.pox_constants.sunset_end {
            Ok(None)
        } else {
            sortition_db_handle.pick_recipients(
                burnchain,
                parent_snapshot.block_height + 1,
                &reward_set_vrf_hash,
                next_pox_info,
            )
        }
    }

    pub fn is_stacks_block_in_sortition_set(
        &self,
        sortition_id: &SortitionId,
        block_to_check: &BlockHeaderHash,
    ) -> Result<bool, BurnchainError> {
        let result = self
            .index_handle(sortition_id)
            .get_tip_indexed(&db_keys::stacks_block_present(block_to_check))?;
        Ok(result.is_some())
    }

    pub fn latest_stacks_blocks_processed(
        &self,
        sortition_id: &SortitionId,
    ) -> Result<u64, BurnchainError> {
        let db_handle = self.index_handle(sortition_id);
        SortitionDB::get_max_arrival_index(&db_handle).map_err(|e| BurnchainError::from(e))
    }

    /// Get a burn blockchain snapshot, given a burnchain configuration struct.
    /// Used mainly by the network code to determine what the chain tip currently looks like.
    pub fn get_burnchain_view(
        conn: &DBConn,
        burnchain: &Burnchain,
        chain_tip: &BlockSnapshot,
    ) -> Result<BurnchainView, db_error> {
        if chain_tip.block_height < burnchain.first_block_height {
            // should never happen, but don't panic since this is network-callable code
            error!(
                "Invalid block height from DB: {}: expected at least {}",
                chain_tip.block_height, burnchain.first_block_height
            );
            return Err(db_error::Corruption);
        }

        if chain_tip.block_height < burnchain.stable_confirmations as u64 {
            // should never happen, but don't panic since this is network-callable code
            error!(
                "Invalid block height from DB: {}: expected at least {}",
                chain_tip.block_height, burnchain.stable_confirmations
            );
            return Err(db_error::Corruption);
        }

        let stable_block_height = cmp::max(
            burnchain.first_block_height,
            chain_tip.block_height - (burnchain.stable_confirmations as u64),
        );

        // get all burn block hashes between the chain tip, and the stable height back
        // MAX_NEIGHBOR_BLOCK_DELAY
        let oldest_height = if stable_block_height < MAX_NEIGHBOR_BLOCK_DELAY {
            0
        } else {
            stable_block_height - MAX_NEIGHBOR_BLOCK_DELAY
        };

        let mut last_burn_block_hashes = HashMap::new();
        let tip_height = chain_tip.block_height;

        let mut cursor = chain_tip.clone();
        let mut cur_height = cursor.block_height;

        for _height in oldest_height..(tip_height + 1) {
            let (ancestor_hash, ancestor_height) =
                if cursor.block_height > burnchain.first_block_height {
                    match SortitionDB::get_block_snapshot(conn, &cursor.parent_sortition_id) {
                        Ok(Some(new_cursor)) => {
                            let ret = (cursor.burn_header_hash.clone(), cursor.block_height);

                            cursor = new_cursor;
                            assert_eq!(cursor.block_height + 1, cur_height);

                            cur_height = cursor.block_height;
                            ret
                        }
                        _ => {
                            cur_height = cur_height.saturating_sub(1);
                            (burnchain.first_block_hash.clone(), cur_height)
                        }
                    }
                } else {
                    cur_height = cur_height.saturating_sub(1);
                    (burnchain.first_block_hash.clone(), cur_height)
                };

            last_burn_block_hashes.insert(ancestor_height, ancestor_hash);
        }

        let burn_stable_block_hash = last_burn_block_hashes
            .get(&stable_block_height)
            .unwrap_or(&burnchain.first_block_hash)
            .clone();

        test_debug!(
            "Chain view: {},{}-{},{}",
            chain_tip.block_height,
            chain_tip.burn_header_hash,
            stable_block_height,
            &burn_stable_block_hash
        );
        Ok(BurnchainView {
            burn_block_height: chain_tip.block_height,
            burn_block_hash: chain_tip.burn_header_hash,
            burn_stable_block_height: stable_block_height,
            burn_stable_block_hash: burn_stable_block_hash,
            last_burn_block_hashes: last_burn_block_hashes,
        })
    }
}

// Querying methods
impl SortitionDB {
    /// Get the canonical burn chain tip -- the tip of the longest burn chain we know about.
    /// Break ties deterministically by ordering on burnchain block hash.
    pub fn get_canonical_burn_chain_tip(conn: &Connection) -> Result<BlockSnapshot, db_error> {
        let qry = "SELECT * FROM snapshots WHERE pox_valid = 1 ORDER BY block_height DESC, burn_header_hash ASC LIMIT 1";
        query_row(conn, qry, NO_PARAMS)
            .map(|opt| opt.expect("CORRUPTION: No canonical burnchain tip"))
    }

    /// Get the canonical burn chain tip -- the tip of the longest burn chain we know about.
    /// Break ties deterministically by ordering on burnchain block hash.
    pub fn get_canonical_chain_tip_bhh(conn: &Connection) -> Result<BurnchainHeaderHash, db_error> {
        let qry = "SELECT burn_header_hash FROM snapshots WHERE pox_valid = 1 ORDER BY block_height DESC, burn_header_hash ASC LIMIT 1";
        match conn.query_row(qry, NO_PARAMS, |row| row.get(0)).optional() {
            Ok(opt) => Ok(opt.expect("CORRUPTION: No canonical burnchain tip")),
            Err(e) => Err(db_error::from(e)),
        }
    }

    /// Get the canonical burn chain tip -- the tip of the longest burn chain we know about.
    /// Break ties deterministically by ordering on burnchain block hash.
    pub fn get_canonical_sortition_tip(conn: &Connection) -> Result<SortitionId, db_error> {
        let qry = "SELECT sortition_id FROM snapshots WHERE pox_valid = 1 ORDER BY block_height DESC, burn_header_hash ASC LIMIT 1";
        match conn.query_row(qry, NO_PARAMS, |row| row.get(0)).optional() {
            Ok(opt) => Ok(opt.expect("CORRUPTION: No canonical burnchain tip")),
            Err(e) => Err(db_error::from(e)),
        }
    }

    pub fn get_stack_stx_ops(
        conn: &Connection,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Vec<StackStxOp>, db_error> {
        query_rows(
            conn,
            "SELECT * FROM stack_stx WHERE burn_header_hash = ?",
            &[burn_header_hash],
        )
    }

    pub fn get_transfer_stx_ops(
        conn: &Connection,
        burn_header_hash: &BurnchainHeaderHash,
    ) -> Result<Vec<TransferStxOp>, db_error> {
        query_rows(
            conn,
            "SELECT * FROM transfer_stx WHERE burn_header_hash = ?",
            &[burn_header_hash],
        )
    }

    pub fn index_handle_at_tip<'a>(&'a self) -> SortitionHandleConn<'a> {
        let sortition_id = SortitionDB::get_canonical_sortition_tip(self.conn()).unwrap();
        self.index_handle(&sortition_id)
    }

    /// Open a tx handle at the burn chain tip
    pub fn tx_begin_at_tip<'a>(&'a mut self) -> SortitionHandleTx<'a> {
        let sortition_id = SortitionDB::get_canonical_sortition_tip(self.conn()).unwrap();
        self.tx_handle_begin(&sortition_id).unwrap()
    }

    /// Get the canonical Stacks chain tip -- this gets memoized on the canonical burn chain tip.
    pub fn get_canonical_stacks_chain_tip_hash(
        conn: &Connection,
    ) -> Result<(ConsensusHash, BlockHeaderHash), db_error> {
        let sn = SortitionDB::get_canonical_burn_chain_tip(conn)?;

        let stacks_block_hash = sn.canonical_stacks_tip_hash;
        let consensus_hash = sn.canonical_stacks_tip_consensus_hash;

        Ok((consensus_hash, stacks_block_hash))
    }

    /// Get an accepted stacks block header in a fork whose chain tip has not yet committed
    /// to it.
    fn get_accepted_stacks_block_pointer(
        conn: &Connection,
        tip_consensus_hash: &ConsensusHash,
        stacks_block_hash: &BlockHeaderHash,
    ) -> Result<Option<AcceptedStacksBlockHeader>, db_error> {
        let args: &[&dyn ToSql] = &[tip_consensus_hash, stacks_block_hash];
        query_row_panic(conn, "SELECT * FROM canonical_accepted_stacks_blocks WHERE tip_consensus_hash = ?1 AND stacks_block_hash = ?2", args,
                        || format!("BUG: the same Stacks block {} shows up twice or more in the same burn chain fork (whose tip is {})", stacks_block_hash, tip_consensus_hash))
    }

    /// Add an accepted Stacks block to the canonical accepted stacks header table, to indicate
    /// that it will be committed to by the next burn block added to the canonical chain tip.  Used
    /// to identify Stacks blocks that get accepted in the mean time, so we can ensure that the
    /// canonical burn chain tip always points to the canonical stacks chain tip.
    fn insert_accepted_stacks_block_pointer(
        tx: &Transaction,
        tip_consensus_hash: &ConsensusHash,
        consensus_hash: &ConsensusHash,
        stacks_block_hash: &BlockHeaderHash,
        stacks_block_height: u64,
    ) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[
            tip_consensus_hash,
            consensus_hash,
            stacks_block_hash,
            &u64_to_sql(stacks_block_height)?,
        ];
        tx.execute("INSERT OR REPLACE INTO canonical_accepted_stacks_blocks (tip_consensus_hash, consensus_hash, stacks_block_hash, block_height) VALUES (?1, ?2, ?3, ?4)", args)
            .map_err(db_error::SqliteError)?;
        Ok(())
    }

    /// Get the maximum arrival index for any known snapshot.
    fn get_max_arrival_index(conn: &Connection) -> Result<u64, db_error> {
        match conn
            .query_row(
                "SELECT IFNULL(MAX(arrival_index), 0) FROM snapshots",
                NO_PARAMS,
                |row| Ok(u64::from_row(row).expect("Expected u64 in database")),
            )
            .optional()?
        {
            Some(arrival_index) => Ok(arrival_index),
            None => Ok(0),
        }
    }

    /// Get a snapshot with an arrived block (i.e. a block that was marked as processed)
    fn get_snapshot_by_arrival_index(
        conn: &Connection,
        arrival_index: u64,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        query_row_panic(
            conn,
            "SELECT * FROM snapshots WHERE arrival_index = ?1 AND stacks_block_accepted > 0 AND pox_valid = 1",
            &[&u64_to_sql(arrival_index)?],
            || "BUG: multiple snapshots have the same non-zero arrival index".to_string(),
        )
    }

    pub fn get_sortition_id_by_consensus(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
    ) -> Result<Option<SortitionId>, db_error> {
        let qry = "SELECT sortition_id FROM snapshots WHERE consensus_hash = ?1 AND pox_valid = 1 LIMIT 1";
        let args = [&consensus_hash];
        query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block with consensus hash {}",
                consensus_hash
            )
        })
    }

    /// Get a snapshot for an existing burn chain block given its consensus hash.
    /// The snapshot may not be valid.
    pub fn get_block_snapshot_consensus(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots WHERE consensus_hash = ?1";
        let args = [&consensus_hash];
        query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block with consensus hash {}",
                consensus_hash
            )
        })
    }

    /// Get a snapshot for an processed sortition.
    /// The snapshot may not be valid
    pub fn get_block_snapshot(
        conn: &Connection,
        sortition_id: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        let qry = "SELECT * FROM snapshots WHERE sortition_id = ?1";
        let args = [&sortition_id];
        query_row_panic(conn, qry, &args, || {
            format!(
                "FATAL: multiple block snapshots for the same block {}",
                sortition_id
            )
        })
        .map(|x| {
            if x.is_none() {
                test_debug!("No snapshot with burn hash {}", sortition_id);
            }
            x
        })
    }

    /// Get the first snapshot
    pub fn get_first_block_snapshot(conn: &Connection) -> Result<BlockSnapshot, db_error> {
        let qry = "SELECT * FROM snapshots WHERE consensus_hash = ?1";
        let result = query_row_panic(conn, qry, &[&ConsensusHash::empty()], || {
            "FATAL: multiple first-block snapshots".into()
        })?;
        match result {
            None => {
                // should never happen
                panic!("FATAL: no first snapshot");
            }
            Some(snapshot) => Ok(snapshot),
        }
    }

    pub fn is_pox_active(
        &self,
        burnchain: &Burnchain,
        block: &BlockSnapshot,
    ) -> Result<bool, db_error> {
        let reward_start_height = burnchain.reward_cycle_to_block_height(
            burnchain
                .block_height_to_reward_cycle(block.block_height)
                .ok_or_else(|| db_error::NotFoundError)?,
        );
        let sort_id_of_start =
            get_ancestor_sort_id(&self.index_conn(), reward_start_height, &block.sortition_id)?
                .ok_or_else(|| db_error::NotFoundError)?;

        let handle = self.index_handle(&sort_id_of_start);
        Ok(handle.get_reward_set_size()? > 0)
    }

    /// Find out how any burn tokens were destroyed in a given block on a given fork.
    pub fn get_block_burn_amount(
        conn: &Connection,
        block_snapshot: &BlockSnapshot,
    ) -> Result<u64, db_error> {
        let user_burns = SortitionDB::get_user_burns_by_block(conn, &block_snapshot.sortition_id)?;
        let block_commits =
            SortitionDB::get_block_commits_by_block(conn, &block_snapshot.sortition_id)?;
        let mut burn_total: u64 = 0;

        for i in 0..user_burns.len() {
            burn_total = burn_total
                .checked_add(user_burns[i].burn_fee)
                .expect("Way too many tokens burned");
        }
        for i in 0..block_commits.len() {
            burn_total = burn_total
                .checked_add(block_commits[i].burn_fee)
                .expect("Way too many tokens burned");
        }
        Ok(burn_total)
    }

    /// Get all user burns registered in a block on is fork.
    /// Returns list of user burns in order by vtxindex.
    pub fn get_user_burns_by_block(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Vec<UserBurnSupportOp>, db_error> {
        let qry = "SELECT * FROM user_burn_support WHERE sortition_id = ?1 ORDER BY vtxindex ASC";
        let args: &[&dyn ToSql] = &[sortition];

        query_rows(conn, qry, args)
    }

    /// Get all block commitments registered in a block on the burn chain's history in this fork.
    /// Returns the list of block commits in order by vtxindex.
    pub fn get_block_commits_by_block(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Vec<LeaderBlockCommitOp>, db_error> {
        let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 ORDER BY vtxindex ASC";
        let args: &[&dyn ToSql] = &[sortition];

        query_rows(conn, qry, args)
    }

    /// Get all the missed block commits that were intended to be included in the given
    ///  block but were not
    pub fn get_missed_commits_by_intended(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Vec<MissedBlockCommit>, db_error> {
        let qry = "SELECT * FROM missed_commits WHERE intended_sortition_id = ?1";
        let args: &[&dyn ToSql] = &[sortition];

        query_rows(conn, qry, args)
    }

    /// Get all leader keys registered in a block on the burn chain's history in this fork.
    /// Returns the list of leader keys in order by vtxindex.
    pub fn get_leader_keys_by_block(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Vec<LeaderKeyRegisterOp>, db_error> {
        let qry = "SELECT * FROM leader_keys WHERE sortition_id = ?1 ORDER BY vtxindex ASC";
        let args: &[&dyn ToSql] = &[sortition];

        query_rows(conn, qry, args)
    }

    pub fn get_block_winning_vtxindex(
        conn: &Connection,
        sortition: &SortitionId,
    ) -> Result<Option<u16>, db_error> {
        let qry = "SELECT vtxindex FROM block_commits WHERE sortition_id = ?1 
                    AND txid = (
                      SELECT winning_block_txid FROM snapshots WHERE sortition_id = ?2 LIMIT 1) LIMIT 1";
        let args: &[&dyn ToSql] = &[sortition, sortition];
        conn.query_row(qry, args, |row| row.get(0))
            .optional()
            .map_err(db_error::from)
    }

    /// Given the fork index hash of a chain tip, and a block height that is an ancestor of the last
    /// block in this fork, find the snapshot of the block at that height.
    pub fn get_ancestor_snapshot<C: SortitionContext>(
        ic: &IndexDBConn<'_, C, SortitionId>,
        ancestor_block_height: u64,
        tip_block_hash: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(ancestor_block_height < BLOCK_HEIGHT_MAX);

        let ancestor = match get_ancestor_sort_id(ic, ancestor_block_height, tip_block_hash)? {
            Some(id) => id,
            None => {
                debug!(
                    "No ancestor block {} from {} in index",
                    ancestor_block_height, tip_block_hash
                );
                return Ok(None);
            }
        };

        SortitionDB::get_block_snapshot(ic, &ancestor)
    }

    /// Given the fork index hash of a chain tip, and a block height that is an ancestor of the last
    /// block in this fork, find the snapshot of the block at that height.
    pub fn get_ancestor_snapshot_tx<C: SortitionContext>(
        ic: &mut IndexDBTx<'_, C, SortitionId>,
        ancestor_block_height: u64,
        tip_block_hash: &SortitionId,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        assert!(ancestor_block_height < BLOCK_HEIGHT_MAX);

        let ancestor = match get_ancestor_sort_id_tx(ic, ancestor_block_height, tip_block_hash)? {
            Some(id) => id,
            None => {
                debug!(
                    "No ancestor block {} from {} in index",
                    ancestor_block_height, tip_block_hash
                );
                return Ok(None);
            }
        };

        SortitionDB::get_block_snapshot(ic.tx(), &ancestor)
    }

    /// Get a parent block commit at a specific location in the burn chain on a particular fork.
    /// Returns None if there is no block commit at this location.
    pub fn get_block_commit_parent<C: SortitionContext>(
        ic: &IndexDBConn<'_, C, SortitionId>,
        block_height: u64,
        vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);
        let ancestor_id = match get_ancestor_sort_id(ic, block_height, tip)? {
            Some(id) => id,
            None => {
                return Ok(None);
            }
        };

        SortitionDB::get_block_commit_of_sortition(ic, &ancestor_id, block_height, vtxindex)
    }

    fn get_block_commit_of_sortition(
        conn: &Connection,
        sortition: &SortitionId,
        block_height: u64,
        vtxindex: u32,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        assert!(block_height < BLOCK_HEIGHT_MAX);

        let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 AND block_height = ?2 AND vtxindex = ?3 LIMIT 2";
        let args: &[&dyn ToSql] = &[sortition, &u64_to_sql(block_height)?, &vtxindex];
        query_row_panic(conn, qry, args, || {
            format!(
                "Multiple parent blocks at {},{} in {}",
                block_height, vtxindex, sortition
            )
        })
    }

    /// Get a leader key at a specific location in the burn chain's fork history, given the
    /// matching block commit's fork index root (block_height and vtxindex are the leader's
    /// calculated location in this fork).
    /// Returns None if there is no leader key at this location.
    pub fn get_leader_key_at<C: SortitionContext>(
        ic: &IndexDBConn<'_, C, SortitionId>,
        key_block_height: u64,
        key_vtxindex: u32,
        tip: &SortitionId,
    ) -> Result<Option<LeaderKeyRegisterOp>, db_error> {
        assert!(key_block_height < BLOCK_HEIGHT_MAX);
        let ancestor_snapshot = match SortitionDB::get_ancestor_snapshot(ic, key_block_height, tip)?
        {
            Some(sn) => sn,
            None => {
                return Ok(None);
            }
        };

        let qry = "SELECT * FROM leader_keys WHERE sortition_id = ?1 AND block_height = ?2 AND vtxindex = ?3 LIMIT 2";
        let args: &[&dyn ToSql] = &[
            &ancestor_snapshot.sortition_id,
            &u64_to_sql(key_block_height)?,
            &key_vtxindex,
        ];
        query_row_panic(ic, qry, args, || {
            format!(
                "Multiple keys at {},{} in {}",
                key_block_height, key_vtxindex, tip
            )
        })
    }

    /// Get a block commit by its committed block
    pub fn get_block_commit_for_stacks_block(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        let (sortition_id, winning_txid) = match SortitionDB::get_block_snapshot_consensus(
            conn,
            consensus_hash,
        )? {
            Some(sn) => {
                if !sn.pox_valid {
                    warn!("Consensus hash {:?} corresponds to a sortition that is not on the canonical PoX fork", consensus_hash);
                    return Err(db_error::InvalidPoxSortition);
                }
                (sn.sortition_id, sn.winning_block_txid)
            }
            None => {
                return Ok(None);
            }
        };

        let qry = "SELECT * FROM block_commits WHERE sortition_id = ?1 AND block_header_hash = ?2 AND txid = ?3";
        let args: [&dyn ToSql; 3] = [&sortition_id, &block_hash, &winning_txid];
        query_row_panic(conn, qry, &args, || {
            format!("FATAL: multiple block commits for {}", &block_hash)
        })
    }

    /// Get a block snapshot for a winning block hash in a given burn chain fork.
    pub fn get_block_snapshot_for_winning_stacks_block(
        ic: &SortitionDBConn,
        tip: &SortitionId,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<BlockSnapshot>, db_error> {
        match ic.get_indexed(tip, &db_keys::stacks_block_present(block_hash))? {
            Some(sortition_id_hex) => {
                let sortition_id = SortitionId::from_hex(&sortition_id_hex)
                    .expect("FATAL: DB stored non-parseable sortition id");
                SortitionDB::get_block_snapshot(ic, &sortition_id)
            }
            None => Ok(None),
        }
    }

    /// Merge the result of get_stacks_header_hashes() into a BlockHeaderCache
    pub fn merge_block_header_cache(
        cache: &mut BlockHeaderCache,
        header_data: &Vec<(ConsensusHash, Option<BlockHeaderHash>)>,
    ) -> () {
        if header_data.len() > 0 {
            let mut i = header_data.len() - 1;
            while i > 0 {
                let cur_consensus_hash = &header_data[i].0;
                let cur_block_opt = &header_data[i].1;

                if let Some((ref cached_block_opt, _)) = cache.get(cur_consensus_hash) {
                    assert_eq!(cached_block_opt, cur_block_opt);
                } else {
                    let prev_consensus_hash = header_data[i - 1].0.clone();
                    cache.insert(
                        (*cur_consensus_hash).clone(),
                        ((*cur_block_opt).clone(), prev_consensus_hash.clone()),
                    );
                }

                i -= 1;
            }
        }
        debug!("Block header cache has {} items", cache.len());
    }

    /// Get a blockstack burnchain operation by txid
    #[cfg(test)]
    pub fn get_burnchain_transaction(
        conn: &Connection,
        txid: &Txid,
    ) -> Result<Option<BlockstackOperationType>, db_error> {
        // leader key?
        let leader_key_sql = "SELECT * FROM leader_keys WHERE txid = ?1 LIMIT 1";
        let args = [&txid];

        let leader_key_res = query_row_panic(conn, &leader_key_sql, &args, || {
            "Multiple leader keys with same txid".to_string()
        })?;
        if let Some(leader_key) = leader_key_res {
            return Ok(Some(BlockstackOperationType::LeaderKeyRegister(leader_key)));
        }

        // block commit?
        let block_commit_sql = "SELECT * FROM block_commits WHERE txid = ?1 LIMIT 1";

        let block_commit_res = query_row_panic(conn, &block_commit_sql, &args, || {
            "Multiple block commits with same txid".to_string()
        })?;
        if let Some(block_commit) = block_commit_res {
            return Ok(Some(BlockstackOperationType::LeaderBlockCommit(
                block_commit,
            )));
        }

        // user burn?
        let user_burn_sql = "SELECT * FROM user_burn_support WHERE txid = ?1 LIMIT 1".to_string();

        let user_burn_res = query_row_panic(conn, &user_burn_sql, &args, || {
            "Multiple user burns with same txid".to_string()
        })?;
        if let Some(user_burn) = user_burn_res {
            return Ok(Some(BlockstackOperationType::UserBurnSupport(user_burn)));
        }

        Ok(None)
    }
}

impl<'a> SortitionHandleTx<'a> {
    /// Append a snapshot to a chain tip, and update various chain tip statistics.
    /// Returns the new state root of this fork.
    /// `initialize_bonus` - if Some(..), then this snapshot is the first mined snapshot,
    ///    and this method should initialize the `initial_mining_bonus` fields in the sortition db.
    pub fn append_chain_tip_snapshot(
        &mut self,
        parent_snapshot: &BlockSnapshot,
        snapshot: &BlockSnapshot,
        block_ops: &Vec<BlockstackOperationType>,
        missed_commits: &Vec<MissedBlockCommit>,
        next_pox_info: Option<RewardCycleInfo>,
        reward_info: Option<&RewardSetInfo>,
        initialize_bonus: Option<InitialMiningBonus>,
    ) -> Result<TrieHash, db_error> {
        assert_eq!(
            snapshot.parent_burn_header_hash,
            parent_snapshot.burn_header_hash
        );
        assert_eq!(snapshot.parent_sortition_id, parent_snapshot.sortition_id);
        assert_eq!(parent_snapshot.block_height + 1, snapshot.block_height);
        if snapshot.sortition {
            assert_eq!(parent_snapshot.num_sortitions + 1, snapshot.num_sortitions);
        } else {
            assert_eq!(parent_snapshot.num_sortitions, snapshot.num_sortitions);
        }

        let mut parent_sn = parent_snapshot.clone();
        let root_hash = self.index_add_fork_info(
            &mut parent_sn,
            snapshot,
            block_ops,
            next_pox_info,
            reward_info,
            initialize_bonus,
        )?;

        let mut sn = snapshot.clone();
        sn.index_root = root_hash.clone();

        // preserve memoized stacks chain tip from this burn chain fork
        sn.canonical_stacks_tip_height = parent_sn.canonical_stacks_tip_height;
        sn.canonical_stacks_tip_hash = parent_sn.canonical_stacks_tip_hash;
        sn.canonical_stacks_tip_consensus_hash = parent_sn.canonical_stacks_tip_consensus_hash;

        self.insert_block_snapshot(&sn)?;

        for block_op in block_ops {
            self.store_burnchain_transaction(block_op, &sn.sortition_id)?;
        }

        for missed_commit in missed_commits {
            self.insert_missed_block_commit(missed_commit)?;
        }

        Ok(root_hash)
    }

    pub fn get_initial_mining_bonus_remaining(
        &mut self,
        chain_tip: &SortitionId,
    ) -> Result<u128, db_error> {
        self.get_indexed(&chain_tip, db_keys::initial_mining_bonus_remaining())?
            .map(|s| Ok(s.parse().expect("BUG: bad mining bonus stored in DB")))
            .unwrap_or(Ok(0))
    }

    pub fn get_initial_mining_bonus_per_block(
        &mut self,
        chain_tip: &SortitionId,
    ) -> Result<Option<u128>, db_error> {
        Ok(self
            .get_indexed(&chain_tip, db_keys::initial_mining_bonus_per_block())?
            .map(|s| s.parse().expect("BUG: bad mining bonus stored in DB")))
    }

    #[cfg(test)]
    fn store_burn_distribution(
        &mut self,
        new_sortition: &SortitionId,
        transition: &BurnchainStateTransition,
    ) {
        let create = "CREATE TABLE IF NOT EXISTS snapshot_burn_distributions (sortition_id TEXT PRIMARY KEY, data TEXT NOT NULL);";
        self.execute(create, NO_PARAMS).unwrap();
        let sql = "INSERT INTO snapshot_burn_distributions (sortition_id, data) VALUES (?, ?)";
        let args: &[&dyn ToSql] = &[
            new_sortition,
            &serde_json::to_string(&transition.burn_dist).unwrap(),
        ];
        self.execute(sql, args).unwrap();
    }

    #[cfg(not(test))]
    fn store_burn_distribution(
        &mut self,
        _new_sortition: &SortitionId,
        _transition: &BurnchainStateTransition,
    ) {
    }

    fn store_transition_ops(
        &mut self,
        new_sortition: &SortitionId,
        transition: &BurnchainStateTransition,
    ) -> Result<(), db_error> {
        let sql = "INSERT INTO snapshot_transition_ops (sortition_id, accepted_ops, consumed_keys) VALUES (?, ?, ?)";
        let args: &[&dyn ToSql] = &[
            new_sortition,
            &serde_json::to_string(&transition.accepted_ops).unwrap(),
            &serde_json::to_string(&transition.consumed_leader_keys).unwrap(),
        ];
        self.execute(sql, args)?;
        self.store_burn_distribution(new_sortition, transition);
        Ok(())
    }

    fn get_pox_id(&mut self) -> Result<PoxId, db_error> {
        let chain_tip = self.context.chain_tip.clone();
        let pox_id = self
            .get_indexed(&chain_tip, db_keys::pox_identifier())?
            .map(|s| s.parse().expect("BUG: Bad PoX identifier stored in DB"))
            .expect("BUG: No PoX identifier stored.");
        Ok(pox_id)
    }

    /// Store a blockstack burnchain operation
    fn store_burnchain_transaction(
        &mut self,
        blockstack_op: &BlockstackOperationType,
        sort_id: &SortitionId,
    ) -> Result<(), db_error> {
        match blockstack_op {
            BlockstackOperationType::LeaderKeyRegister(ref op) => {
                info!(
                    "ACCEPTED({}) leader key register {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_leader_key(op, sort_id)
            }
            BlockstackOperationType::LeaderBlockCommit(ref op) => {
                info!(
                    "ACCEPTED({}) leader block commit {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex;
                    "apparent_sender" => %op.apparent_sender.to_bitcoin_address(BitcoinNetworkType::Mainnet)
                );
                self.insert_block_commit(op, sort_id)
            }
            BlockstackOperationType::UserBurnSupport(ref op) => {
                info!(
                    "ACCEPTED({}) user burn support {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_user_burn(op, sort_id)
            }
            BlockstackOperationType::StackStx(ref op) => {
                info!(
                    "ACCEPTED({}) stack stx opt {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_stack_stx(op)
            }
            BlockstackOperationType::TransferStx(ref op) => {
                info!(
                    "ACCEPTED({}) transfer stx opt {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                self.insert_transfer_stx(op)
            }
            BlockstackOperationType::PreStx(ref op) => {
                info!(
                    "ACCEPTED({}) pre stack stx op {} at {},{}",
                    op.block_height, &op.txid, op.block_height, op.vtxindex
                );
                // no need to store this op in the sortition db.
                Ok(())
            }
        }
    }

    /// Insert a leader key registration.
    /// No validity checking will be done, beyond what is encoded in the leader_keys table
    /// constraints.  That is, type mismatches and serialization issues will be caught, but nothing else.
    /// The corresponding snapshot must already be inserted
    fn insert_leader_key(
        &mut self,
        leader_key: &LeaderKeyRegisterOp,
        sort_id: &SortitionId,
    ) -> Result<(), db_error> {
        assert!(leader_key.block_height < BLOCK_HEIGHT_MAX);

        let args: &[&dyn ToSql] = &[
            &leader_key.txid,
            &leader_key.vtxindex,
            &u64_to_sql(leader_key.block_height)?,
            &leader_key.burn_header_hash,
            &leader_key.consensus_hash,
            &leader_key.public_key.to_hex(),
            &to_hex(&leader_key.memo),
            &leader_key.address.to_string(),
            sort_id,
        ];

        self.execute("INSERT INTO leader_keys (txid, vtxindex, block_height, burn_header_hash, consensus_hash, public_key, memo, address, sortition_id) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)", args)?;

        Ok(())
    }

    /// Insert a stack-stx op
    fn insert_stack_stx(&mut self, op: &StackStxOp) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[
            &op.txid,
            &op.vtxindex,
            &u64_to_sql(op.block_height)?,
            &op.burn_header_hash,
            &op.sender.to_string(),
            &op.reward_addr.to_string(),
            &op.stacked_ustx.to_string(),
            &op.num_cycles,
        ];

        self.execute("REPLACE INTO stack_stx (txid, vtxindex, block_height, burn_header_hash, sender_addr, reward_addr, stacked_ustx, num_cycles) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)", args)?;

        Ok(())
    }

    /// Insert a transfer-stx op
    fn insert_transfer_stx(&mut self, op: &TransferStxOp) -> Result<(), db_error> {
        let args: &[&dyn ToSql] = &[
            &op.txid,
            &op.vtxindex,
            &u64_to_sql(op.block_height)?,
            &op.burn_header_hash,
            &op.sender.to_string(),
            &op.recipient.to_string(),
            &op.transfered_ustx.to_string(),
            &to_hex(&op.memo),
        ];

        self.execute("REPLACE INTO transfer_stx (txid, vtxindex, block_height, burn_header_hash, sender_addr, recipient_addr, transfered_ustx, memo) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)", args)?;

        Ok(())
    }

    /// Insert a leader block commitment.
    /// No validity checking will be done, beyond what is encoded in the block_commits table
    /// constraints.  That is, type mismatches and serialization issues will be caught, but nothing else.
    /// The corresponding snapshot must already be inserted
    fn insert_block_commit(
        &mut self,
        block_commit: &LeaderBlockCommitOp,
        sort_id: &SortitionId,
    ) -> Result<(), db_error> {
        assert!(block_commit.block_height < BLOCK_HEIGHT_MAX);

        // serialize tx input to JSON
        let tx_input_str = serde_json::to_string(&block_commit.input)
            .map_err(|e| db_error::SerializationError(e))?;

        // serialize apparent sender to JSON
        let apparent_sender_str = serde_json::to_string(&block_commit.apparent_sender)
            .map_err(|e| db_error::SerializationError(e))?;

        let args: &[&dyn ToSql] = &[
            &block_commit.txid,
            &block_commit.vtxindex,
            &u64_to_sql(block_commit.block_height)?,
            &block_commit.burn_header_hash,
            &block_commit.block_header_hash,
            &block_commit.new_seed,
            &block_commit.parent_block_ptr,
            &block_commit.parent_vtxindex,
            &block_commit.key_block_ptr,
            &block_commit.key_vtxindex,
            &to_hex(&block_commit.memo[..]),
            &block_commit.burn_fee.to_string(),
            &tx_input_str,
            sort_id,
            &serde_json::to_value(&block_commit.commit_outs).unwrap(),
            &block_commit.sunset_burn.to_string(),
            &apparent_sender_str,
            &block_commit.burn_parent_modulus,
        ];

        self.execute("INSERT INTO block_commits (txid, vtxindex, block_height, burn_header_hash, block_header_hash, new_seed, parent_block_ptr, parent_vtxindex, key_block_ptr, key_vtxindex, memo, burn_fee, input, sortition_id, commit_outs, sunset_burn, apparent_sender, burn_parent_modulus) \
                      VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18)", args)?;

        Ok(())
    }

    /// Insert a user support burn.
    /// No validity checking will be done, beyond what is encoded in the user_burn_support table
    /// constraints.  That is, type mismatches and serialization errors will be caught, but nothing
    /// else.
    /// The corresponding snapshot must already be inserted
    fn insert_user_burn(
        &mut self,
        user_burn: &UserBurnSupportOp,
        sort_id: &SortitionId,
    ) -> Result<(), db_error> {
        assert!(user_burn.block_height < BLOCK_HEIGHT_MAX);

        // represent burn fee as TEXT
        let burn_fee_str = format!("{}", user_burn.burn_fee);

        let args: &[&dyn ToSql] = &[
            &user_burn.txid,
            &user_burn.vtxindex,
            &u64_to_sql(user_burn.block_height)?,
            &user_burn.burn_header_hash,
            &user_burn.address.to_string(),
            &user_burn.consensus_hash,
            &user_burn.public_key.to_hex(),
            &user_burn.key_block_ptr,
            &user_burn.key_vtxindex,
            &user_burn.block_header_hash_160,
            &burn_fee_str,
            sort_id,
        ];

        self.execute("INSERT INTO user_burn_support (txid, vtxindex, block_height, burn_header_hash, address, consensus_hash, public_key, key_block_ptr, key_vtxindex, block_header_hash_160, burn_fee, sortition_id) \
                      VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)", args)?;

        Ok(())
    }

    /// Insert a missed block commit
    fn insert_missed_block_commit(&mut self, op: &MissedBlockCommit) -> Result<(), db_error> {
        // serialize tx input to JSON
        let tx_input_str =
            serde_json::to_string(&op.input).map_err(|e| db_error::SerializationError(e))?;

        let args: &[&dyn ToSql] = &[&op.txid, &op.intended_sortition, &tx_input_str];

        self.execute(
            "INSERT OR REPLACE INTO missed_commits (txid, intended_sortition_id, input) \
                      VALUES (?1, ?2, ?3)",
            args,
        )?;
        info!(
            "ACCEPTED missed block commit";
            "txid" => %op.txid,
            "intended_sortition" => %op.intended_sortition,
        );

        Ok(())
    }

    /// Insert a snapshots row from a block's-worth of operations.
    /// Do not call directly -- use append_chain_tip_snapshot to preserve the fork table structure.
    fn insert_block_snapshot(&self, snapshot: &BlockSnapshot) -> Result<(), db_error> {
        assert!(snapshot.block_height < BLOCK_HEIGHT_MAX);
        assert!(snapshot.num_sortitions < BLOCK_HEIGHT_MAX);

        test_debug!(
            "Insert block snapshot state {} for block {} ({},{}) {}",
            snapshot.index_root,
            snapshot.block_height,
            snapshot.burn_header_hash,
            snapshot.parent_burn_header_hash,
            snapshot.num_sortitions
        );

        let args: &[&dyn ToSql] = &[
            &u64_to_sql(snapshot.block_height)?,
            &snapshot.burn_header_hash,
            &u64_to_sql(snapshot.burn_header_timestamp)?,
            &snapshot.parent_burn_header_hash,
            &snapshot.consensus_hash,
            &snapshot.ops_hash,
            &snapshot.total_burn.to_string(),
            &snapshot.sortition,
            &snapshot.sortition_hash,
            &snapshot.winning_block_txid,
            &snapshot.winning_stacks_block_hash,
            &snapshot.index_root,
            &u64_to_sql(snapshot.num_sortitions)?,
            &snapshot.stacks_block_accepted,
            &u64_to_sql(snapshot.stacks_block_height)?,
            &u64_to_sql(snapshot.arrival_index)?,
            &u64_to_sql(snapshot.canonical_stacks_tip_height)?,
            &snapshot.canonical_stacks_tip_hash,
            &snapshot.canonical_stacks_tip_consensus_hash,
            &snapshot.sortition_id,
            &snapshot.parent_sortition_id,
            &snapshot.pox_valid,
            &snapshot.accumulated_coinbase_ustx.to_string(),
        ];

        self.execute("INSERT INTO snapshots \
                      (block_height, burn_header_hash, burn_header_timestamp, parent_burn_header_hash, consensus_hash, ops_hash, total_burn, sortition, sortition_hash, winning_block_txid, winning_stacks_block_hash, index_root, num_sortitions, \
                      stacks_block_accepted, stacks_block_height, arrival_index, canonical_stacks_tip_height, canonical_stacks_tip_hash, canonical_stacks_tip_consensus_hash, sortition_id, parent_sortition_id, pox_valid, accumulated_coinbase_ustx) \
                      VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19, ?20, ?21, ?22, ?23)", args)
            .map_err(db_error::SqliteError)?;

        Ok(())
    }

    /// Record fork information to the index and calculate the new fork index root hash.
    /// * sortdb::vrf::${VRF_PUBLIC_KEY} --> 0 or 1 (1 if available, 0 if consumed), for each VRF public key we process
    /// * sortdb::last_sortition --> $BURN_BLOCK_HASH, for each block that had a sortition
    /// * sortdb::sortition_block_hash::${STACKS_BLOCK_HASH} --> $BURN_BLOCK_HASH for each winning block sortition
    /// * sortdb::stacks::block::${STACKS_BLOCK_HASH} --> ${STACKS_BLOCK_HEIGHT} for each block that has been accepted so far
    /// * sortdb::stacks::block::max_arrival_index --> ${ARRIVAL_INDEX} to set the maximum arrival index processed in this fork
    /// * sortdb::pox_reward_set::${n} --> recipient Bitcoin address, to track the reward set as the permutation progresses
    ///
    /// `recipient_info` is used to pass information to this function about which reward set addresses were consumed
    ///   during this sortition. this object will be None in the following cases:
    ///    * The reward cycle had an anchor block, but it isn't known by this node.
    ///    * The reward cycle did not have anchor block
    ///    * The Stacking recipient set is empty (either because this reward cycle has already exhausted the set of addresses or because no one ever Stacked).
    ///
    /// NOTE: the resulting index root must be globally unique.  This is guaranteed because each
    /// burn block hash is unique, no matter what fork it's on (and this index uses burn block
    /// hashes as its index's block hash data).
    fn index_add_fork_info(
        &mut self,
        parent_snapshot: &mut BlockSnapshot,
        snapshot: &BlockSnapshot,
        block_ops: &Vec<BlockstackOperationType>,
        next_pox_info: Option<RewardCycleInfo>,
        recipient_info: Option<&RewardSetInfo>,
        initialize_bonus: Option<InitialMiningBonus>,
    ) -> Result<TrieHash, db_error> {
        if !snapshot.is_initial() {
            assert_eq!(
                snapshot.parent_burn_header_hash,
                parent_snapshot.burn_header_hash
            );
            assert_eq!(&parent_snapshot.sortition_id, &self.context.chain_tip);
        }

        // data we want to store
        let mut keys = vec![];
        let mut values = vec![];

        // record each new VRF key, and each consumed VRF key
        for block_op in block_ops {
            if let BlockstackOperationType::LeaderKeyRegister(ref data) = block_op {
                keys.push(db_keys::vrf_key_status(&data.public_key));
                values.push("1".to_string()); // the value is no longer used, but the key needs to exist to figure whether a key was registered
            }
        }

        // map burnchain header hashes to sortition ids
        keys.push(db_keys::sortition_id_for_bhh(&snapshot.burn_header_hash));
        values.push(snapshot.sortition_id.to_hex());

        // if this commit has a sortition, record its burn block hash and stacks block hash
        if snapshot.sortition {
            keys.push(db_keys::last_sortition().to_string());
            values.push(snapshot.burn_header_hash.to_hex());

            keys.push(db_keys::stacks_block_present(
                &snapshot.winning_stacks_block_hash,
            ));
            values.push(snapshot.sortition_id.to_hex());
        }

        if let Some(initialize_bonus) = initialize_bonus {
            // first sortition with a winner, set the initial mining bonus fields
            keys.push(db_keys::initial_mining_bonus_per_block().into());
            values.push(initialize_bonus.per_block.to_string());

            let total_reward_remaining = initialize_bonus
                .total_reward
                .saturating_sub(initialize_bonus.per_block);
            keys.push(db_keys::initial_mining_bonus_remaining().into());
            values.push(total_reward_remaining.to_string());
        } else if parent_snapshot.total_burn > 0 {
            // mining has started, check if there's still any remaining bonus that this
            //  block consumed, and then decrement
            let prior_bonus_remaining =
                self.get_initial_mining_bonus_remaining(&parent_snapshot.sortition_id)?;
            if prior_bonus_remaining > 0 {
                let mining_bonus_per_block = self
                    .get_initial_mining_bonus_per_block(&parent_snapshot.sortition_id)?
                    .expect(
                        "BUG: initial mining bonus amount written, but not the per block amount.",
                    );
                let bonus_remaining = prior_bonus_remaining.saturating_sub(mining_bonus_per_block);
                keys.push(db_keys::initial_mining_bonus_remaining().into());
                values.push(bonus_remaining.to_string());
            }
        }

        // if this is the start of a reward cycle, store the new PoX keys
        if !snapshot.is_initial() {
            if let Some(reward_info) = next_pox_info {
                let mut pox_id = self.get_pox_id()?;
                // update the PoX bit vector with whether or not
                //  this reward cycle is aware of its anchor (if one wasn't selected,
                //   mark this as "known")
                if reward_info.is_reward_info_known() {
                    pox_id.extend_with_present_block();
                } else {
                    pox_id.extend_with_not_present_block();
                }
                // if we have selected an anchor block, write that info
                if let Some(ref anchor_block) = reward_info.selected_anchor_block() {
                    keys.push(db_keys::pox_anchor_to_prepare_end(anchor_block));
                    values.push(parent_snapshot.sortition_id.to_hex());

                    keys.push(db_keys::pox_last_anchor().to_string());
                    values.push(anchor_block.to_hex());
                } else {
                    keys.push(db_keys::pox_last_anchor().to_string());
                    values.push("".to_string());
                }
                // if we've selected an anchor _and_ know of the anchor,
                //  write the reward set information
                if let Some(mut reward_set) = reward_info.known_selected_anchor_block_owned() {
                    if reward_set.len() > 0 {
                        // if we have a reward set, then we must also have produced a recipient
                        //   info for this block
                        let mut recipients_to_remove: Vec<_> = recipient_info
                            .unwrap()
                            .recipients
                            .iter()
                            .map(|(addr, ix)| (addr.clone(), *ix))
                            .collect();
                        recipients_to_remove.sort_unstable_by(|(_, a), (_, b)| b.cmp(a));
                        // remove from the reward set any consumed addresses in this first reward block
                        for (addr, ix) in recipients_to_remove.iter() {
                            assert_eq!(&reward_set.remove(*ix as usize), addr,
                                       "BUG: Attempted to remove used address from reward set, but failed to do so safely");
                        }
                    }

                    keys.push(db_keys::pox_reward_set_size().to_string());
                    values.push(db_keys::reward_set_size_to_string(reward_set.len()));
                    for (ix, address) in reward_set.iter().enumerate() {
                        keys.push(db_keys::pox_reward_set_entry(ix as u16));
                        values.push(address.to_string());
                    }
                } else {
                    keys.push(db_keys::pox_reward_set_size().to_string());
                    values.push(db_keys::reward_set_size_to_string(0));
                }

                // in all cases, write the new PoX bit vector
                keys.push(db_keys::pox_identifier().to_string());
                values.push(pox_id.to_string());
            } else {
                // if this snapshot consumed some reward set entries AND
                //  this isn't the start of a new reward cycle,
                //   update the reward set
                if let Some(reward_info) = recipient_info {
                    let mut current_len = self.get_reward_set_size()?;
                    let mut recipient_indexes: Vec<_> =
                        reward_info.recipients.iter().map(|(_, x)| *x).collect();
                    let mut remapped_entries = HashMap::new();
                    // sort in decrementing order
                    recipient_indexes.sort_unstable_by(|a, b| b.cmp(a));
                    for index in recipient_indexes.into_iter() {
                        // sanity check
                        if index >= current_len {
                            unreachable!(
                                "Supplied index should never be greater than recipient set size"
                            );
                        } else if index + 1 == current_len {
                            // selected index is the last element: no need to swap, just decrement len
                            current_len -= 1;
                        } else {
                            let replacement = current_len - 1; // if current_len were 0, we would already have panicked.
                            let replace_with = if let Some((_prior_ix, replace_with)) =
                                remapped_entries.remove_entry(&replacement)
                            {
                                // the entry to swap in was itself swapped, so let's use the new value instead
                                replace_with
                            } else {
                                self.get_reward_set_entry(replacement)?
                            };

                            // swap and decrement to remove from set
                            remapped_entries.insert(index, replace_with);
                            current_len -= 1;
                        }
                    }
                    // store the changes in the new trie
                    keys.push(db_keys::pox_reward_set_size().to_string());
                    values.push(db_keys::reward_set_size_to_string(current_len as usize));
                    for (recipient_index, replace_with) in remapped_entries.into_iter() {
                        keys.push(db_keys::pox_reward_set_entry(recipient_index));
                        values.push(replace_with.to_string())
                    }
                }
            }
        } else {
            assert_eq!(next_pox_info, None);
            keys.push(db_keys::pox_identifier().to_string());
            values.push(PoxId::initial().to_string());
            keys.push(db_keys::pox_reward_set_size().to_string());
            values.push(db_keys::reward_set_size_to_string(0));
            keys.push(db_keys::pox_last_anchor().to_string());
            values.push("".to_string());
        }

        // commit to all newly-arrived blocks
        let (mut block_arrival_keys, mut block_arrival_values) =
            self.process_new_block_arrivals(parent_snapshot)?;
        keys.append(&mut block_arrival_keys);
        values.append(&mut block_arrival_values);

        // store each indexed field
        //  -- marf tx _must_ have already began
        self.put_indexed_begin(&parent_snapshot.sortition_id, &snapshot.sortition_id)?;

        let root_hash = self.put_indexed_all(&keys, &values)?;
        self.context.chain_tip = snapshot.sortition_id.clone();
        Ok(root_hash)
    }

    /// Find all stacks blocks that were processed since parent_tip had been processed, and generate MARF
    /// key/value pairs for the subset that arrived on ancestor blocks of the parent.  Update the
    /// given parent chain tip to have the correct memoized canonical chain tip present in the fork
    /// it represents.
    fn process_new_block_arrivals(
        &mut self,
        parent_tip: &mut BlockSnapshot,
    ) -> Result<(Vec<String>, Vec<String>), db_error> {
        let mut keys = vec![];
        let mut values = vec![];

        let mut new_block_arrivals = vec![];

        let old_max_arrival_index = self
            .get_indexed(
                &parent_tip.sortition_id,
                &db_keys::stacks_block_max_arrival_index(),
            )?
            .unwrap_or("0".into())
            .parse::<u64>()
            .expect("BUG: max arrival index is not a u64");

        let max_arrival_index = SortitionDB::get_max_arrival_index(self.tx())?;

        // find all Stacks block hashes who arrived since this parent_tip was built.
        for ari in old_max_arrival_index..(max_arrival_index + 1) {
            test_debug!("Get block with arrival index {}", ari);
            let arrival_sn = match SortitionDB::get_snapshot_by_arrival_index(self.tx(), ari)? {
                Some(sn) => sn,
                None => {
                    continue;
                }
            };

            // must be an ancestor of this tip, or must be this tip
            if let Some(sn) =
                self.get_block_snapshot(&arrival_sn.burn_header_hash, &parent_tip.sortition_id)?
            {
                assert_eq!(sn, arrival_sn);

                debug!(
                    "New Stacks anchored block arrived since {}: block {} ({}) ari={} tip={}",
                    parent_tip.burn_header_hash,
                    sn.stacks_block_height,
                    sn.winning_stacks_block_hash,
                    ari,
                    &parent_tip.burn_header_hash
                );
                new_block_arrivals.push((
                    sn.consensus_hash,
                    sn.winning_stacks_block_hash,
                    sn.stacks_block_height,
                ));
            } else {
                // this block did not arrive on an ancestor block
                continue;
            }
        }

        let mut best_tip_block_bhh = parent_tip.canonical_stacks_tip_hash.clone();
        let mut best_tip_consensus_hash = parent_tip.canonical_stacks_tip_consensus_hash.clone();
        let mut best_tip_height = parent_tip.canonical_stacks_tip_height;

        // NOTE: new_block_arrivals is ordered by arrival index, which means it is partially
        // ordered by block height!
        for (consensus_hash, block_bhh, height) in new_block_arrivals.into_iter() {
            keys.push(db_keys::stacks_block_index(&block_bhh));
            values.push(db_keys::stacks_block_index_value(height));

            if height > best_tip_height {
                debug!(
                    "At tip {}: {}/{} (height {}) is superceded by {}/{} (height {})",
                    &parent_tip.burn_header_hash,
                    &best_tip_consensus_hash,
                    &best_tip_block_bhh,
                    best_tip_height,
                    consensus_hash,
                    block_bhh,
                    height
                );

                best_tip_block_bhh = block_bhh;
                best_tip_consensus_hash = consensus_hash;
                best_tip_height = height;
            }
        }

        // update parent tip
        parent_tip.canonical_stacks_tip_consensus_hash = best_tip_consensus_hash;
        parent_tip.canonical_stacks_tip_hash = best_tip_block_bhh;
        parent_tip.canonical_stacks_tip_height = best_tip_height;

        debug!(
            "Max arrival for child of {} (burn {}) is {}",
            &parent_tip.consensus_hash, &parent_tip.burn_header_hash, &max_arrival_index
        );
        keys.push(db_keys::stacks_block_max_arrival_index());
        values.push(db_keys::stacks_block_max_arrival_index_value(
            max_arrival_index,
        ));

        Ok((keys, values))
    }
}

impl ChainstateDB for SortitionDB {
    fn backup(_backup_path: &String) -> Result<(), db_error> {
        return Err(db_error::NotImplemented);
    }
}

#[cfg(test)]
pub mod tests {
    use std::sync::mpsc::sync_channel;
    use std::thread;

    use address::AddressHashMode;
    use burnchains::bitcoin::address::BitcoinAddress;
    use burnchains::bitcoin::keys::BitcoinPublicKey;
    use burnchains::bitcoin::BitcoinNetworkType;
    use burnchains::*;
    use chainstate::burn::operations::{
        leader_block_commit::BURN_BLOCK_MINED_AT_MODULUS, BlockstackOperationType,
        LeaderBlockCommitOp, LeaderKeyRegisterOp, UserBurnSupportOp,
    };
    use chainstate::burn::ConsensusHash;
    use chainstate::stacks::StacksPublicKey;
    use core::*;
    use util::db::Error as db_error;
    use util::get_epoch_time_secs;
    use util::hash::{hex_bytes, Hash160};
    use util::vrf::*;

    use crate::types::chainstate::StacksAddress;
    use crate::types::chainstate::{BlockHeaderHash, VRFSeed};

    use super::*;

    #[test]
    fn test_instantiate() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let _db = SortitionDB::connect_test(123, &first_burn_hash).unwrap();
    }

    #[test]
    fn test_tx_begin_end() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(123, &first_burn_hash).unwrap();
        let tx = db.tx_begin().unwrap();
        tx.commit().unwrap();
    }

    pub fn test_append_snapshot(
        db: &mut SortitionDB,
        next_hash: BurnchainHeaderHash,
        block_ops: &Vec<BlockstackOperationType>,
    ) -> BlockSnapshot {
        let mut sn = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        let mut tx = SortitionHandleTx::begin(db, &sn.sortition_id).unwrap();

        let sn_parent = sn.clone();
        sn.parent_burn_header_hash = sn.burn_header_hash.clone();
        sn.parent_sortition_id = sn.sortition_id.clone();
        sn.burn_header_hash = next_hash;
        sn.block_height += 1;
        sn.num_sortitions += 1;
        sn.sortition_id = SortitionId::stubbed(&sn.burn_header_hash);
        sn.consensus_hash = ConsensusHash(Hash160::from_data(&sn.consensus_hash.0).0);

        let index_root = tx
            .append_chain_tip_snapshot(&sn_parent, &sn, block_ops, &vec![], None, None, None)
            .unwrap();
        sn.index_root = index_root;

        tx.commit().unwrap();

        sn
    }

    #[test]
    fn test_insert_leader_key() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
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
            vtxindex: vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &vec![BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        {
            let ic = db.index_conn();
            let leader_key_opt = SortitionDB::get_leader_key_at(
                &ic,
                block_height + 1,
                vtxindex,
                &snapshot.sortition_id,
            )
            .unwrap();
            assert!(leader_key_opt.is_some());
            assert_eq!(leader_key_opt.unwrap(), leader_key);
        }

        let new_snapshot = test_append_snapshot(&mut db, BurnchainHeaderHash([0x02; 32]), &vec![]);

        {
            let ic = db.index_conn();
            let leader_key_opt = SortitionDB::get_leader_key_at(
                &ic,
                block_height + 1,
                vtxindex,
                &new_snapshot.sortition_id,
            )
            .unwrap();
            assert!(leader_key_opt.is_some());
            assert_eq!(leader_key_opt.unwrap(), leader_key);

            let leader_key_none = SortitionDB::get_leader_key_at(
                &ic,
                block_height + 1,
                vtxindex + 1,
                &new_snapshot.sortition_id,
            )
            .unwrap();
            assert!(leader_key_none.is_none());
        }
    }

    #[test]
    fn test_insert_block_commit() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
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
            vtxindex: vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let block_commit = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222222")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: 0x43424140,
            parent_vtxindex: 0x5150,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],

            commit_outs: vec![],
            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner {
                public_keys: vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
                num_sigs: 1,
                hash_mode: AddressHashMode::SerializeP2PKH,
            },

            txid: Txid::from_bytes_be(
                &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: vtxindex,
            block_height: block_height + 2,
            burn_parent_modulus: ((block_height + 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &vec![BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        // test get_consumed_leader_keys()
        {
            let mut ic = SortitionHandleTx::begin(&mut db, &snapshot.sortition_id).unwrap();
            let keys = ic
                .get_consumed_leader_keys(&snapshot, &vec![block_commit.clone()])
                .unwrap();
            assert_eq!(keys, vec![leader_key.clone()]);
        }

        let snapshot_consumed = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &vec![BlockstackOperationType::LeaderBlockCommit(
                block_commit.clone(),
            )],
        );

        {
            let res_block_commits =
                SortitionDB::get_block_commits_by_block(db.conn(), &snapshot_consumed.sortition_id)
                    .unwrap();
            assert_eq!(res_block_commits.len(), 1);
            assert_eq!(res_block_commits[0], block_commit);
        }

        // advance and get parent
        let empty_snapshot =
            test_append_snapshot(&mut db, BurnchainHeaderHash([0x05; 32]), &vec![]);

        // test get_block_commit_parent()
        {
            let ic = db.index_conn();
            let parent = SortitionDB::get_block_commit_parent(
                &ic,
                block_height + 2,
                block_commit.vtxindex,
                &empty_snapshot.sortition_id,
            )
            .unwrap();
            assert!(parent.is_some());
            assert_eq!(parent.unwrap(), block_commit);

            let parent = SortitionDB::get_block_commit_parent(
                &ic,
                block_height + 3,
                block_commit.vtxindex,
                &empty_snapshot.sortition_id,
            )
            .unwrap();
            assert!(parent.is_none());

            let parent = SortitionDB::get_block_commit_parent(
                &ic,
                block_height + 2,
                block_commit.vtxindex + 1,
                &empty_snapshot.sortition_id,
            )
            .unwrap();
            assert!(parent.is_none());
        }

        // test get_block_commit()
        {
            let handle = db.index_handle(&empty_snapshot.sortition_id);
            let commit = handle.get_block_commit_by_txid(&block_commit.txid).unwrap();
            assert!(commit.is_some());
            assert_eq!(commit.unwrap(), block_commit);

            let bad_txid = Txid::from_bytes_be(
                &hex_bytes("4c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap();
            let commit = handle.get_block_commit_by_txid(&bad_txid).unwrap();
            assert!(commit.is_none());
        }

        // test get_consumed_leader_keys() (should be doable at any subsequent index root)
        {
            let mut ic = SortitionHandleTx::begin(&mut db, &snapshot.sortition_id).unwrap();
            let keys = ic
                .get_consumed_leader_keys(&empty_snapshot, &vec![block_commit.clone()])
                .unwrap();
            assert_eq!(keys, vec![leader_key.clone()]);
        }

        // make a fork between the leader key and block commit, and verify that the key is
        // unconsumed
        let fork_snapshot = {
            let mut sn = SortitionDB::get_block_snapshot(db.conn(), &snapshot.sortition_id)
                .unwrap()
                .unwrap();
            let next_hash = BurnchainHeaderHash([0x13; 32]);
            let mut tx = SortitionHandleTx::begin(&mut db, &sn.sortition_id).unwrap();

            let sn_parent = sn.clone();
            sn.parent_burn_header_hash = sn.burn_header_hash.clone();
            sn.sortition_id = SortitionId(next_hash.0.clone());
            sn.parent_sortition_id = sn_parent.sortition_id.clone();
            sn.burn_header_hash = next_hash;
            sn.block_height += 1;
            sn.num_sortitions += 1;
            sn.consensus_hash = ConsensusHash([0x23; 20]);

            let index_root = tx
                .append_chain_tip_snapshot(&sn_parent, &sn, &vec![], &vec![], None, None, None)
                .unwrap();
            sn.index_root = index_root;

            tx.commit().unwrap();

            sn
        };

        // test get_consumed_leader_keys() and is_leader_key_consumed() against this new fork
        {
            let mut ic = SortitionHandleTx::begin(&mut db, &snapshot.sortition_id).unwrap();
            let keys = ic
                .get_consumed_leader_keys(&fork_snapshot, &vec![block_commit.clone()])
                .unwrap();
            assert_eq!(keys, vec![leader_key.clone()]);
        }
    }

    #[test]
    fn test_insert_user_burn() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
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
            vtxindex: vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let user_burn = UserBurnSupportOp {
            address: StacksAddress::new(1, Hash160([1u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333").unwrap(),
            )
            .unwrap(),
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            burn_fee: 12345,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: vtxindex,
            block_height: block_height + 2,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &vec![BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        let user_burn_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &vec![BlockstackOperationType::UserBurnSupport(user_burn.clone())],
        );

        {
            let res_user_burns =
                SortitionDB::get_user_burns_by_block(db.conn(), &user_burn_snapshot.sortition_id)
                    .unwrap();
            assert_eq!(res_user_burns.len(), 1);
            assert_eq!(res_user_burns[0], user_burn);

            let no_user_burns =
                SortitionDB::get_user_burns_by_block(db.conn(), &snapshot.sortition_id).unwrap();
            assert_eq!(no_user_burns.len(), 0);
        }
    }

    #[test]
    fn has_VRF_public_key() {
        let public_key = VRFPublicKey::from_bytes(
            &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a").unwrap(),
        )
        .unwrap();
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: public_key.clone(),
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
            vtxindex: vtxindex,
            block_height: block_height + 2,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let no_key_snapshot =
            test_append_snapshot(&mut db, BurnchainHeaderHash([0x01; 32]), &vec![]);

        let has_key_before = {
            let mut ic = SortitionHandleTx::begin(&mut db, &no_key_snapshot.sortition_id).unwrap();
            ic.has_VRF_public_key(&public_key).unwrap()
        };

        assert!(!has_key_before);

        let key_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &vec![BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        let has_key_after = {
            let mut ic = SortitionHandleTx::begin(&mut db, &key_snapshot.sortition_id).unwrap();
            ic.has_VRF_public_key(&public_key).unwrap()
        };

        assert!(has_key_after);
    }

    #[test]
    fn is_fresh_consensus_hash() {
        let consensus_hash_lifetime = 24;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();
        {
            let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            for i in 0..255 {
                let sortition_id = SortitionId([
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, i as u8,
                ]);
                let parent_sortition_id = if i == 0 {
                    last_snapshot.sortition_id.clone()
                } else {
                    SortitionId([
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
                        i - 1 as u8,
                    ])
                };

                let mut tx = SortitionHandleTx::begin(&mut db, &parent_sortition_id).unwrap();
                let snapshot_row = BlockSnapshot {
                    accumulated_coinbase_ustx: 0,
                    pox_valid: true,
                    block_height: i as u64 + 1,
                    burn_header_timestamp: get_epoch_time_secs(),
                    burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i as u8,
                    ])
                    .unwrap(),
                    sortition_id,
                    parent_sortition_id,
                    parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        (if i == 0 { 0x10 } else { 0 }) as u8,
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
                        (if i == 0 { 0xff } else { i - 1 }) as u8,
                    ])
                    .unwrap(),
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
                    total_burn: i as u64,
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
                    num_sortitions: i as u64 + 1,
                    stacks_block_accepted: false,
                    stacks_block_height: 0,
                    arrival_index: 0,
                    canonical_stacks_tip_height: 0,
                    canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                    canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                };
                let index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot_row,
                        &vec![],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                last_snapshot = snapshot_row;
                last_snapshot.index_root = index_root;
                tx.commit().unwrap();
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let ch_fresh = ConsensusHash::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255,
        ])
        .unwrap();
        let ch_oldest_fresh = ConsensusHash::from_bytes(&[
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
            (255 - consensus_hash_lifetime) as u8,
        ])
        .unwrap();
        let ch_newest_stale = ConsensusHash::from_bytes(&[
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
            (255 - consensus_hash_lifetime - 1) as u8,
        ])
        .unwrap();
        let ch_missing = ConsensusHash::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 255,
        ])
        .unwrap();

        let mut ic = SortitionHandleTx::begin(&mut db, &tip.sortition_id).unwrap();
        let fresh_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_fresh)
            .unwrap();

        assert!(fresh_check);

        let oldest_fresh_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_oldest_fresh)
            .unwrap();

        assert!(oldest_fresh_check);

        let newest_stale_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_newest_stale)
            .unwrap();

        assert!(!newest_stale_check);

        let missing_check = ic
            .is_fresh_consensus_hash(consensus_hash_lifetime, &ch_missing)
            .unwrap();

        assert!(!missing_check);
    }

    #[test]
    fn get_consensus_at() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();
        {
            let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            for i in 0..256u64 {
                let sortition_id = SortitionId([
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, i as u8,
                ]);
                let parent_sortition_id = if i == 0 {
                    last_snapshot.sortition_id.clone()
                } else {
                    SortitionId([
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
                        (i - 1) as u8,
                    ])
                };

                let mut tx = SortitionHandleTx::begin(&mut db, &parent_sortition_id).unwrap();
                let snapshot_row = BlockSnapshot {
                    accumulated_coinbase_ustx: 0,
                    pox_valid: true,
                    block_height: i as u64 + 1,
                    burn_header_timestamp: get_epoch_time_secs(),
                    burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i as u8,
                    ])
                    .unwrap(),
                    sortition_id,
                    parent_sortition_id,
                    parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                        (if i == 0 { 0x10 } else { 0 }) as u8,
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
                        (if i == 0 { 0xff } else { i - 1 }) as u8,
                    ])
                    .unwrap(),
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
                        ((i + 1) / 256) as u8,
                        (i + 1) as u8,
                    ])
                    .unwrap(),
                    ops_hash: OpsHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i as u8,
                    ])
                    .unwrap(),
                    total_burn: i as u64,
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
                    num_sortitions: i as u64 + 1,
                    stacks_block_accepted: false,
                    stacks_block_height: 0,
                    arrival_index: 0,
                    canonical_stacks_tip_height: 0,
                    canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                    canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                };
                let index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot_row,
                        &vec![],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                last_snapshot = snapshot_row;
                last_snapshot.index_root = index_root;
                // should succeed within the tx
                let ch = tx.get_consensus_at(i as u64 + 1).unwrap().unwrap();
                assert_eq!(ch, last_snapshot.consensus_hash);

                tx.commit().unwrap();
            }
        }

        let tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        for i in 0..256 {
            // should succeed within the conn
            let ic = db.index_handle(&tip.sortition_id);
            let expected_ch = ConsensusHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8,
            ])
            .unwrap();
            let ch = ic.get_consensus_at(i).unwrap().unwrap();
            assert_eq!(ch, expected_ch);
        }
    }

    #[test]
    fn get_block_burn_amount() {
        let block_height = 123;
        let vtxindex = 456;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
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
            vtxindex: vtxindex,
            block_height: block_height + 1,
            burn_header_hash: BurnchainHeaderHash([0x01; 32]),
        };

        let block_commit = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222222")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: 0x43424140,
            parent_vtxindex: 0x4342,
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            memo: vec![0x80],
            commit_outs: vec![],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner {
                public_keys: vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
                num_sigs: 1,
                hash_mode: AddressHashMode::SerializeP2PKH,
            },

            txid: Txid::from_bytes_be(
                &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: vtxindex,
            block_height: block_height + 2,
            burn_parent_modulus: ((block_height + 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
        };

        let user_burn = UserBurnSupportOp {
            address: StacksAddress::new(2, Hash160([2u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333").unwrap(),
            )
            .unwrap(),
            key_block_ptr: (block_height + 1) as u32,
            key_vtxindex: vtxindex as u16,
            burn_fee: 12345,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: vtxindex + 1,
            block_height: block_height + 2,
            burn_header_hash: BurnchainHeaderHash([0x03; 32]),
        };

        let mut db = SortitionDB::connect_test(block_height, &first_burn_hash).unwrap();

        let key_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x01; 32]),
            &vec![BlockstackOperationType::LeaderKeyRegister(
                leader_key.clone(),
            )],
        );

        let commit_snapshot = test_append_snapshot(
            &mut db,
            BurnchainHeaderHash([0x03; 32]),
            &vec![
                BlockstackOperationType::LeaderBlockCommit(block_commit.clone()),
                BlockstackOperationType::UserBurnSupport(user_burn.clone()),
            ],
        );

        {
            let burn_amt = SortitionDB::get_block_burn_amount(db.conn(), &commit_snapshot).unwrap();
            assert_eq!(burn_amt, block_commit.burn_fee + user_burn.burn_fee);

            let no_burn_amt = SortitionDB::get_block_burn_amount(db.conn(), &key_snapshot).unwrap();
            assert_eq!(no_burn_amt, 0);
        }
    }

    #[test]
    fn get_last_snapshot_with_sortition() {
        let block_height = 123;
        let total_burn_sortition = 100;
        let total_burn_no_sortition = 200;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let mut first_snapshot = BlockSnapshot {
            accumulated_coinbase_ustx: 0,
            pox_valid: true,
            block_height: block_height - 2,
            burn_header_timestamp: get_epoch_time_secs(),
            burn_header_hash: first_burn_hash.clone(),
            sortition_id: SortitionId(first_burn_hash.0.clone()),
            parent_sortition_id: SortitionId(first_burn_hash.0.clone()),
            parent_burn_header_hash: BurnchainHeaderHash([0xff; 32]),
            consensus_hash: ConsensusHash::from_hex("0000000000000000000000000000000000000000")
                .unwrap(),
            ops_hash: OpsHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
            total_burn: 0,
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
            index_root: TrieHash([0u8; 32]),
            num_sortitions: 0,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
        };

        let mut snapshot_with_sortition = BlockSnapshot {
            accumulated_coinbase_ustx: 0,
            pox_valid: true,
            block_height: block_height,
            burn_header_timestamp: get_epoch_time_secs(),
            burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 2,
            ])
            .unwrap(),
            sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 2,
            ]),
            parent_sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ]),
            parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ])
            .unwrap(),
            consensus_hash: ConsensusHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
            ])
            .unwrap(),
            ops_hash: OpsHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ])
            .unwrap(),
            total_burn: total_burn_sortition,
            sortition: true,
            sortition_hash: SortitionHash::initial(),
            winning_block_txid: Txid::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000001",
            )
            .unwrap(),
            winning_stacks_block_hash: BlockHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000001",
            )
            .unwrap(),
            index_root: TrieHash([1u8; 32]),
            num_sortitions: 1,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
        };

        let snapshot_without_sortition = BlockSnapshot {
            accumulated_coinbase_ustx: 0,
            pox_valid: true,
            block_height: block_height - 1,
            burn_header_timestamp: get_epoch_time_secs(),
            burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ])
            .unwrap(),
            sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 1,
            ]),
            parent_sortition_id: SortitionId([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ]),
            parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ])
            .unwrap(),
            consensus_hash: ConsensusHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2,
            ])
            .unwrap(),
            ops_hash: OpsHash::from_bytes(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 2,
            ])
            .unwrap(),
            total_burn: total_burn_no_sortition,
            sortition: false,
            sortition_hash: SortitionHash::initial(),
            winning_block_txid: Txid::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000002",
            )
            .unwrap(),
            winning_stacks_block_hash: BlockHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000002",
            )
            .unwrap(),
            index_root: TrieHash([2u8; 32]),
            num_sortitions: 0,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
            canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
        };

        let mut db = SortitionDB::connect_test(block_height - 2, &first_burn_hash).unwrap();

        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let initial_snapshot = {
            let ic = db.index_handle(&chain_tip.sortition_id);
            ic.get_last_snapshot_with_sortition(block_height - 2)
                .unwrap()
        };

        first_snapshot.index_root = initial_snapshot.index_root.clone();
        first_snapshot.burn_header_timestamp = initial_snapshot.burn_header_timestamp;
        assert_eq!(initial_snapshot, first_snapshot);

        {
            let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
            let mut tx = SortitionHandleTx::begin(&mut db, &chain_tip.sortition_id).unwrap();

            tx.append_chain_tip_snapshot(
                &chain_tip,
                &snapshot_without_sortition,
                &vec![],
                &vec![],
                None,
                None,
                None,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let mut next_snapshot = {
            let ic = db.index_handle(&chain_tip.sortition_id);
            ic.get_last_snapshot_with_sortition(block_height - 1)
                .unwrap()
        };

        next_snapshot.index_root = initial_snapshot.index_root.clone();
        next_snapshot.burn_header_timestamp = initial_snapshot.burn_header_timestamp;
        assert_eq!(initial_snapshot, next_snapshot);

        {
            let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
            let mut tx = SortitionHandleTx::begin(&mut db, &chain_tip.sortition_id).unwrap();

            tx.append_chain_tip_snapshot(
                &chain_tip,
                &snapshot_with_sortition,
                &vec![],
                &vec![],
                None,
                None,
                None,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();

        let next_snapshot_2 = {
            let ic = db.index_handle(&chain_tip.sortition_id);
            ic.get_last_snapshot_with_sortition(block_height).unwrap()
        };

        snapshot_with_sortition.index_root = next_snapshot_2.index_root.clone();
        snapshot_with_sortition.burn_header_timestamp = next_snapshot_2.burn_header_timestamp;
        assert_eq!(snapshot_with_sortition, next_snapshot_2);
    }

    /// Verify that the snapshots in a fork are well-formed -- i.e. the block heights are
    /// sequential and the parent block hash of the ith block is equal to the block hash of the
    /// (i-1)th block.
    fn verify_fork_integrity(db: &mut SortitionDB, tip: &SortitionId) {
        let mut child = SortitionDB::get_block_snapshot(db.conn(), tip)
            .unwrap()
            .unwrap();

        let initial = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        test_debug!(
            "Verify from {},hash={},parent={} back to {},hash={},parent={}",
            child.block_height,
            child.burn_header_hash,
            child.parent_burn_header_hash,
            initial.block_height,
            initial.burn_header_hash,
            initial.parent_burn_header_hash
        );

        while child.block_height > initial.block_height {
            let parent = {
                let ic = db.index_conn();
                SortitionDB::get_ancestor_snapshot(&ic, child.block_height - 1, &child.sortition_id)
                    .unwrap()
                    .unwrap()
            };

            test_debug!(
                "Verify {} == {} - 1 and hash={},parent_hash={} == parent={}",
                parent.block_height,
                child.block_height,
                child.burn_header_hash,
                parent.burn_header_hash,
                child.parent_burn_header_hash
            );

            assert_eq!(parent.block_height, child.block_height - 1);
            assert_eq!(parent.burn_header_hash, child.parent_burn_header_hash);

            child = parent.clone();
        }

        assert_eq!(child, initial);
    }

    #[test]
    fn test_chain_reorg() {
        // Create a set of forks that looks like this:
        // 0-1-2-3-4-5-6-7-8-9 (fork 0)
        //  \
        //   1-2-3-4-5-6-7-8-9 (fork 1)
        //    \
        //     2-3-4-5-6-7-8-9 (fork 2)
        //      \
        //       3-4-5-6-7-8-9 (fork 3)
        //
        //    ...etc...
        //
        // Then, append a block to fork 9, and confirm that it switches places with fork 0.
        // Append 2 blocks to fork 8, and confirm that it switches places with fork 0.
        // Append 3 blocks to fork 7, and confirm that it switches places with fork 0.
        // ... etc.
        //
        let first_burn_hash = BurnchainHeaderHash([0x00; 32]);
        let first_block_height = 100;

        let mut db = SortitionDB::connect_test(first_block_height, &first_burn_hash).unwrap();

        // make an initial fork
        let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        for i in 0..10 {
            let mut next_snapshot = last_snapshot.clone();

            next_snapshot.block_height += 1;
            next_snapshot.num_sortitions += 1;
            next_snapshot.parent_burn_header_hash = next_snapshot.burn_header_hash.clone();
            next_snapshot.burn_header_hash = BurnchainHeaderHash([
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
                i + 1,
            ]);
            next_snapshot.sortition_id = SortitionId([
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
                i + 1,
            ]);
            next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
            next_snapshot.consensus_hash = ConsensusHash([
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
                i + 1,
            ]);

            let mut tx = SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
            tx.append_chain_tip_snapshot(
                &last_snapshot,
                &next_snapshot,
                &vec![],
                &vec![],
                None,
                None,
                None,
            )
            .unwrap();
            tx.commit().unwrap();

            last_snapshot = next_snapshot.clone();
        }

        test_debug!("----- make forks -----");

        // make other forks
        for i in 0..9 {
            let parent_block_hash = if i == 0 {
                [0u8; 32]
            } else {
                let mut tmp = [
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
                ];
                tmp[i - 1] = 1;
                tmp
            };

            let parent_block = SortitionId(parent_block_hash);
            test_debug!(
                "----- build fork off of parent {} (i = {}) -----",
                &parent_block,
                i
            );

            let mut last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &parent_block)
                .unwrap()
                .unwrap();

            let initial_block_height = last_snapshot.block_height;
            let initial_num_sortitions = last_snapshot.num_sortitions;

            let mut next_snapshot = last_snapshot.clone();

            for j in (i + 1)..10 {
                let mut block_hash = [
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
                    (j + 1) as u8,
                ];
                block_hash[i] = (j - i) as u8;

                next_snapshot.block_height = initial_block_height + (j - i) as u64;
                next_snapshot.num_sortitions = initial_num_sortitions + (j - i) as u64;
                next_snapshot.parent_burn_header_hash = next_snapshot.burn_header_hash.clone();
                next_snapshot.sortition_id = SortitionId(block_hash.clone());
                next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
                next_snapshot.burn_header_hash = BurnchainHeaderHash(block_hash);
                next_snapshot.consensus_hash = ConsensusHash([
                    1,
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
                    j as u8,
                    (i + 1) as u8,
                ]);

                let mut tx =
                    SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
                let next_index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &next_snapshot,
                        &vec![],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                tx.commit().unwrap();

                next_snapshot.index_root = next_index_root;
                last_snapshot = next_snapshot.clone();
            }

            test_debug!(
                "----- made fork {} (i = {}) -----",
                &next_snapshot.burn_header_hash,
                i
            );
        }

        test_debug!("----- grow forks -----");

        let mut all_chain_tips = vec![];

        // grow each fork so it overtakes the currently-canonical fork
        for i in 0..9 {
            let mut last_block_hash = [
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 10,
            ];
            last_block_hash[i] = (9 - i) as u8;
            let last_block = SortitionId(last_block_hash);

            test_debug!("----- grow fork {} (i = {}) -----", &last_block, i);

            let mut last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &last_block)
                .unwrap()
                .unwrap();

            let initial_block_height = last_snapshot.block_height;
            let mut next_snapshot = last_snapshot.clone();

            // grow the fork up to the length of the previous fork
            for j in 0..((i + 1) as u64) {
                next_snapshot = last_snapshot.clone();

                let mut next_block_hash_vec = last_snapshot.burn_header_hash.as_bytes().to_vec();
                next_block_hash_vec[0] += 1;
                let mut next_block_hash = [0u8; 32];
                next_block_hash.copy_from_slice(&next_block_hash_vec[..]);

                next_snapshot.block_height = last_snapshot.block_height + 1;
                next_snapshot.num_sortitions = last_snapshot.num_sortitions + 1;
                next_snapshot.parent_burn_header_hash = last_snapshot.burn_header_hash.clone();
                next_snapshot.sortition_id = SortitionId(next_block_hash.clone());
                next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
                next_snapshot.burn_header_hash = BurnchainHeaderHash(next_block_hash);
                next_snapshot.consensus_hash = ConsensusHash([
                    2,
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
                    j as u8,
                    (i + 1) as u8,
                ]);

                let next_index_root = {
                    let mut tx =
                        SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
                    let next_index_root = tx
                        .append_chain_tip_snapshot(
                            &last_snapshot,
                            &next_snapshot,
                            &vec![],
                            &vec![],
                            None,
                            None,
                            None,
                        )
                        .unwrap();
                    tx.commit().unwrap();
                    next_index_root
                };

                last_snapshot =
                    SortitionDB::get_block_snapshot(db.conn(), &next_snapshot.sortition_id)
                        .unwrap()
                        .unwrap();
            }

            // make the fork exceed the canonical chain tip
            next_snapshot = last_snapshot.clone();

            let mut next_block_hash_vec = last_snapshot.burn_header_hash.as_bytes().to_vec();
            next_block_hash_vec[0] = 0xff;
            let mut next_block_hash = [0u8; 32];
            next_block_hash.copy_from_slice(&next_block_hash_vec[..]);

            next_snapshot.block_height += 1;
            next_snapshot.num_sortitions += 1;
            next_snapshot.parent_burn_header_hash = next_snapshot.burn_header_hash.clone();
            next_snapshot.sortition_id = SortitionId(next_block_hash.clone());
            next_snapshot.parent_sortition_id = last_snapshot.sortition_id.clone();
            next_snapshot.burn_header_hash = BurnchainHeaderHash(next_block_hash);
            next_snapshot.consensus_hash =
                ConsensusHash(Hash160::from_data(&next_snapshot.consensus_hash.0).0);

            let next_index_root = {
                let mut tx =
                    SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();
                let next_index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &next_snapshot,
                        &vec![],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                tx.commit().unwrap();
                next_index_root
            };

            next_snapshot.index_root = next_index_root;

            let mut expected_tip = next_snapshot.clone();
            expected_tip.index_root = next_index_root;

            let canonical_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
            assert_eq!(canonical_tip, expected_tip);

            verify_fork_integrity(&mut db, &canonical_tip.sortition_id);
            all_chain_tips.push(canonical_tip.sortition_id.clone());
        }

        for tip_header_hash in all_chain_tips.iter() {
            verify_fork_integrity(&mut db, tip_header_hash);
        }
    }

    #[test]
    fn test_get_stacks_header_hashes() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();
        {
            let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            let mut total_burn = 0;
            let mut total_sortitions = 0;
            for i in 0..256 {
                let snapshot_row = if i % 3 == 0 {
                    BlockSnapshot {
                        accumulated_coinbase_ustx: 0,
                        pox_valid: true,
                        block_height: i + 1,
                        burn_header_timestamp: get_epoch_time_secs(),
                        burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        sortition_id: SortitionId([
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ]),
                        parent_sortition_id: last_snapshot.sortition_id.clone(),
                        parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            (if i == 0 { 0x10 } else { 0 }) as u8,
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
                            (if i == 0 { 0xff } else { i - 1 }) as u8,
                        ])
                        .unwrap(),
                        consensus_hash: ConsensusHash::from_bytes(&[
                            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        ops_hash: OpsHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        total_burn: total_burn,
                        sortition: false,
                        sortition_hash: SortitionHash([(i as u8); 32]),
                        winning_block_txid: Txid([(i as u8); 32]),
                        winning_stacks_block_hash: BlockHeaderHash([0u8; 32]),
                        index_root: TrieHash::from_empty_data(),
                        num_sortitions: total_sortitions,
                        stacks_block_accepted: false,
                        stacks_block_height: 0,
                        arrival_index: 0,
                        canonical_stacks_tip_height: 0,
                        canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                        canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                    }
                } else {
                    total_burn += 1;
                    total_sortitions += 1;
                    BlockSnapshot {
                        accumulated_coinbase_ustx: 0,
                        pox_valid: true,
                        block_height: i + 1,
                        burn_header_timestamp: get_epoch_time_secs(),
                        burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        sortition_id: SortitionId([
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ]),
                        parent_sortition_id: last_snapshot.sortition_id.clone(),
                        parent_burn_header_hash: BurnchainHeaderHash::from_bytes(&[
                            (if i == 0 { 0x10 } else { 0 }) as u8,
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
                            (if i == 0 { 0xff } else { i - 1 }) as u8,
                        ])
                        .unwrap(),
                        consensus_hash: ConsensusHash::from_bytes(&[
                            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        ops_hash: OpsHash::from_bytes(&[
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, i as u8,
                        ])
                        .unwrap(),
                        total_burn: total_burn,
                        sortition: true,
                        sortition_hash: SortitionHash([(i as u8); 32]),
                        winning_block_txid: Txid([(i as u8); 32]),
                        winning_stacks_block_hash: BlockHeaderHash([(i as u8); 32]),
                        index_root: TrieHash::from_empty_data(),
                        num_sortitions: total_sortitions,
                        stacks_block_accepted: false,
                        stacks_block_height: 0,
                        arrival_index: 0,
                        canonical_stacks_tip_height: 0,
                        canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                        canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                    }
                };

                // NOTE: we don't care about VRF keys or block commits here

                let mut tx =
                    SortitionHandleTx::begin(&mut db, &last_snapshot.sortition_id).unwrap();

                let index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot_row,
                        &vec![],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                last_snapshot = snapshot_row;
                last_snapshot.index_root = index_root;

                // should succeed within the tx
                let ch = tx
                    .get_consensus_at(i + 1)
                    .unwrap()
                    .unwrap_or(ConsensusHash::empty());
                assert_eq!(ch, last_snapshot.consensus_hash);

                tx.commit().unwrap();
            }
        }

        let canonical_tip = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        let mut cache = BlockHeaderCache::new();

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(256, &canonical_tip.consensus_hash, &cache)
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            assert_eq!(hashes.len(), 256);
            for i in 0..256 {
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                if i > 0 {
                    assert!(cache.contains_key(consensus_hash));
                    assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
                }
            }
        }

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(
                    256,
                    &canonical_tip.consensus_hash,
                    &mut BlockHeaderCache::new(),
                )
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            let cached_hashes = ic
                .get_stacks_header_hashes(256, &canonical_tip.consensus_hash, &cache)
                .unwrap();

            assert_eq!(hashes.len(), 256);
            assert_eq!(cached_hashes.len(), 256);
            for i in 0..256 {
                assert_eq!(cached_hashes[i], hashes[i]);
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                if i > 0 {
                    assert!(cache.contains_key(consensus_hash));
                    assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
                }
            }
        }

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(
                    192,
                    &canonical_tip.consensus_hash,
                    &mut BlockHeaderCache::new(),
                )
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            let cached_hashes = ic
                .get_stacks_header_hashes(192, &canonical_tip.consensus_hash, &cache)
                .unwrap();

            assert_eq!(hashes.len(), 192);
            assert_eq!(cached_hashes.len(), 192);
            for i in 64..256 {
                assert_eq!(cached_hashes[i - 64], hashes[i - 64]);
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i - 64];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                assert!(cache.contains_key(consensus_hash));
                assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
            }
        }

        {
            let ic = db.index_conn();
            let hashes = ic
                .get_stacks_header_hashes(
                    257,
                    &canonical_tip.consensus_hash,
                    &mut BlockHeaderCache::new(),
                )
                .unwrap();
            SortitionDB::merge_block_header_cache(&mut cache, &hashes);

            let cached_hashes = ic
                .get_stacks_header_hashes(257, &canonical_tip.consensus_hash, &cache)
                .unwrap();

            assert_eq!(hashes.len(), 256);
            assert_eq!(cached_hashes.len(), 256);
            for i in 0..256 {
                assert_eq!(cached_hashes[i], hashes[i]);
                let (ref consensus_hash, ref block_hash_opt) = &hashes[i];
                if i % 3 == 0 {
                    assert!(block_hash_opt.is_none());
                } else {
                    assert!(block_hash_opt.is_some());
                    let block_hash = block_hash_opt.unwrap();
                    assert_eq!(block_hash, BlockHeaderHash([(i as u8); 32]));
                }
                assert_eq!(
                    *consensus_hash,
                    ConsensusHash::from_bytes(&[
                        1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, i as u8
                    ])
                    .unwrap()
                );

                if i > 0 {
                    assert!(cache.contains_key(consensus_hash));
                    assert_eq!(cache.get(consensus_hash).unwrap().0, *block_hash_opt);
                }
            }
        }

        {
            let ic = db.index_conn();
            let err = ic
                .get_stacks_header_hashes(256, &ConsensusHash([0x03; 20]), &BlockHeaderCache::new())
                .unwrap_err();
            match err {
                db_error::NotFoundError => {}
                _ => {
                    eprintln!("Got wrong error: {:?}", &err);
                    assert!(false);
                    unreachable!();
                }
            }

            let err = ic
                .get_stacks_header_hashes(256, &ConsensusHash([0x03; 20]), &cache)
                .unwrap_err();
            match err {
                db_error::NotFoundError => {}
                _ => {
                    eprintln!("Got wrong error: {:?}", &err);
                    assert!(false);
                    unreachable!();
                }
            }
        }
    }

    fn make_fork_run(
        db: &mut SortitionDB,
        start_snapshot: &BlockSnapshot,
        length: u64,
        bit_pattern: u8,
    ) -> () {
        let mut last_snapshot = start_snapshot.clone();
        for i in last_snapshot.block_height..(last_snapshot.block_height + length) {
            let snapshot = BlockSnapshot {
                accumulated_coinbase_ustx: 0,
                pox_valid: true,
                block_height: last_snapshot.block_height + 1,
                burn_header_timestamp: get_epoch_time_secs(),
                burn_header_hash: BurnchainHeaderHash([(i as u8) | bit_pattern; 32]),
                sortition_id: SortitionId([(i as u8) | bit_pattern; 32]),
                parent_sortition_id: last_snapshot.sortition_id.clone(),
                parent_burn_header_hash: last_snapshot.burn_header_hash.clone(),
                consensus_hash: ConsensusHash([((i + 1) as u8) | bit_pattern; 20]),
                ops_hash: OpsHash([(i as u8) | bit_pattern; 32]),
                total_burn: 0,
                sortition: true,
                sortition_hash: SortitionHash([(i as u8) | bit_pattern; 32]),
                winning_block_txid: Txid([(i as u8) | bit_pattern; 32]),
                winning_stacks_block_hash: BlockHeaderHash([(i as u8) | bit_pattern; 32]),
                index_root: TrieHash([0u8; 32]),
                num_sortitions: last_snapshot.num_sortitions + 1,
                stacks_block_accepted: false,
                stacks_block_height: 0,
                arrival_index: 0,
                canonical_stacks_tip_height: 0,
                canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
            };
            {
                let mut tx = SortitionHandleTx::begin(db, &last_snapshot.sortition_id).unwrap();
                let _index_root = tx
                    .append_chain_tip_snapshot(
                        &last_snapshot,
                        &snapshot,
                        &vec![],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();
                tx.commit().unwrap();
            }
            last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &snapshot.sortition_id)
                .unwrap()
                .unwrap();
        }
    }

    #[test]
    fn test_set_stacks_block_accepted() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "10000000000000000000000000000000000000000000000000000000000000ff",
        )
        .unwrap();
        let mut db = SortitionDB::connect_test(0, &first_burn_hash).unwrap();

        let mut last_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        // seed a single fork
        make_fork_run(&mut db, &last_snapshot, 5, 0);

        // set some blocks as processed
        for i in 0..5 {
            let consensus_hash = ConsensusHash([(i + 1) as u8; 20]);
            let parent_stacks_block_hash = if i == 0 {
                FIRST_STACKS_BLOCK_HASH.clone()
            } else {
                BlockHeaderHash([(i - 1) as u8; 32])
            };

            let stacks_block_hash = BlockHeaderHash([i as u8; 32]);
            let height = i;

            {
                let mut tx = db.tx_begin_at_tip();
                tx.set_stacks_block_accepted(
                    &consensus_hash,
                    &parent_stacks_block_hash,
                    &stacks_block_hash,
                    height,
                )
                .unwrap();
                tx.commit().unwrap();
            }

            // chain tip is memoized to the current burn chain tip
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(block_consensus_hash, consensus_hash);
            assert_eq!(block_bhh, stacks_block_hash);
        }

        // materialize all block arrivals in the MARF
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x04; 32]))
            .unwrap()
            .unwrap();
        make_fork_run(&mut db, &last_snapshot, 1, 0);

        // verify that all Stacks block in this fork can be looked up from this chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        {
            let ic = db.index_conn();
            for i in 0..5 {
                let parent_stacks_block_hash = BlockHeaderHash([i as u8; 32]);
                let parent_key = db_keys::stacks_block_index(&parent_stacks_block_hash);

                test_debug!(
                    "Look up '{}' off of {}",
                    &parent_key,
                    &last_snapshot.burn_header_hash
                );
                let value_opt = ic
                    .get_indexed(&last_snapshot.sortition_id, &parent_key)
                    .unwrap();
                assert!(value_opt.is_some());
                assert_eq!(value_opt.unwrap(), format!("{}", i));
            }
        }

        // make a burn fork off of the 5th block
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        make_fork_run(&mut db, &last_snapshot, 5, 0x80);

        // chain tip is _still_ memoized to the last materialized chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x8a; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );

        // accept blocks 5 and 7 in one fork, and 6, 8, 9 in another.
        // Stacks fork 1,2,3,4,5,7 will be the longest fork.
        // Stacks fork 1,2,3,4 will overtake it when blocks 6,8,9 are processed.
        let mut parent_stacks_block_hash = BlockHeaderHash([0x04; 32]);
        for (i, height) in [5, 7].iter().zip([5, 6].iter()) {
            let consensus_hash = ConsensusHash([((i + 1) | 0x80) as u8; 20]);
            let stacks_block_hash = BlockHeaderHash([(i | 0x80) as u8; 32]);

            {
                let mut tx = db.tx_begin_at_tip();
                tx.set_stacks_block_accepted(
                    &consensus_hash,
                    &parent_stacks_block_hash,
                    &stacks_block_hash,
                    *height,
                )
                .unwrap();
                tx.commit().unwrap();
            }

            // chain tip is memoized to the current burn chain tip, since it's the longest stacks fork
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(block_consensus_hash, consensus_hash);
            assert_eq!(block_bhh, stacks_block_hash);

            parent_stacks_block_hash = stacks_block_hash;
        }

        // chain tip is _still_ memoized to the last materialized chain tip (i.e. stacks block 7)
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x8a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x88; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x87; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 6);

        // when the blocks for burn blocks 6 and 8 arrive, the canonical fork is still at stacks
        // block 7.  The two stacks forks will be:
        // * 1,2,3,4,5,7
        // * 1,2,3,4,6,8
        parent_stacks_block_hash = BlockHeaderHash([4u8; 32]);
        for (i, height) in [6, 8].iter().zip([5, 6].iter()) {
            let consensus_hash = ConsensusHash([((i + 1) | 0x80) as u8; 20]);
            let stacks_block_hash = BlockHeaderHash([(i | 0x80) as u8; 32]);

            {
                let mut tx = db.tx_begin_at_tip();
                tx.set_stacks_block_accepted(
                    &consensus_hash,
                    &parent_stacks_block_hash,
                    &stacks_block_hash,
                    *height,
                )
                .unwrap();
                tx.commit().unwrap();
            }

            // chain tip is memoized to the current burn chain tip, since it's the longest stacks fork
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(
                block_consensus_hash,
                last_snapshot.canonical_stacks_tip_consensus_hash
            );
            assert_eq!(block_bhh, last_snapshot.canonical_stacks_tip_hash);

            parent_stacks_block_hash = stacks_block_hash;
        }

        // when the block for burn block 9 arrives, the canonical stacks fork will be
        // 1,2,3,4,6,8,9.  It overtakes 1,2,3,4,5,7
        for (i, height) in [9].iter().zip([7].iter()) {
            let consensus_hash = ConsensusHash([((i + 1) | 0x80) as u8; 20]);
            let stacks_block_hash = BlockHeaderHash([(i | 0x80) as u8; 32]);

            {
                let mut tx = db.tx_begin_at_tip();
                tx.set_stacks_block_accepted(
                    &consensus_hash,
                    &parent_stacks_block_hash,
                    &stacks_block_hash,
                    *height,
                )
                .unwrap();
                tx.commit().unwrap();
            }

            // we've overtaken the longest fork with a different longest fork on this burn chain fork
            let (block_consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(db.conn()).unwrap();
            assert_eq!(block_consensus_hash, consensus_hash);
            assert_eq!(block_bhh, stacks_block_hash);
        }

        // canonical stacks chain tip is now stacks block 9
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x8a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x8a; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x89; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 7);

        // fork the burn chain at 0x4, producing a longer burnchain fork.  There are now two
        // burnchain forks, where the first one has two stacks forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x04; 32]))
            .unwrap()
            .unwrap();
        make_fork_run(&mut db, &last_snapshot, 7, 0x40);

        // canonical stacks chain tip is now stacks block 4, since the burn chain fork ending on
        // 0x4b has overtaken the burn chain fork ending on 0x8a
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);

        // set the stacks block at 0x4b as accepted as the 5th block
        {
            let mut tx = db.tx_begin_at_tip();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x4c; 20]),
                &BlockHeaderHash([0x04; 32]),
                &BlockHeaderHash([0x4b; 32]),
                5,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x4c; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x4b; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 5);

        // fork the burn chain at 0x48, producing a shorter burnchain fork.  There are now three
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x48; 32]))
            .unwrap()
            .unwrap();
        make_fork_run(&mut db, &last_snapshot, 2, 0x20);

        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x2a; 32]))
            .unwrap()
            .unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x05; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x04; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 4);

        // doesn't affect canonical chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x4c; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x4b; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 5);

        // set the stacks block at 0x29 and 0x2a as accepted as the 5th and 6th blocks
        {
            let mut tx = db.tx_handle_begin(&SortitionId([0x2a; 32])).unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x2a; 20]),
                &BlockHeaderHash([0x04; 32]),
                &BlockHeaderHash([0x29; 32]),
                5,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x2b; 20]),
                &BlockHeaderHash([0x29; 32]),
                &BlockHeaderHash([0x2a; 32]),
                6,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        // new state of the world:
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,                            5,    6
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a

        // canonical stacks chain off of non-canonical burn chain fork 0x2a should have been updated
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x2a; 32]))
            .unwrap()
            .unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x2b; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x2a; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 6);

        // insertion on the non-canonical tip doesn't affect canonical chain tip
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x4c; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x4b; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 5);

        // insert stacks blocks #6, #7, #8, #9 off of the burn chain tip starting at 0x4b (i.e. the
        // canonical burn chain tip), on blocks 0x45, 0x46, and 0x47
        {
            let mut tx = db.tx_begin_at_tip();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x46; 20]),
                &BlockHeaderHash([0x04; 32]),
                &BlockHeaderHash([0x45; 32]),
                5,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x47; 20]),
                &BlockHeaderHash([0x45; 32]),
                &BlockHeaderHash([0x46; 32]),
                6,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x48; 20]),
                &BlockHeaderHash([0x46; 32]),
                &BlockHeaderHash([0x47; 32]),
                7,
            )
            .unwrap();
            tx.set_stacks_block_accepted(
                &ConsensusHash([0x49; 20]),
                &BlockHeaderHash([0x47; 32]),
                &BlockHeaderHash([0x48; 32]),
                8,
            )
            .unwrap();
            tx.commit().unwrap();
        }

        // new state of the world:
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,    6,    7,    8,   9
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,                            5,    6
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a

        // new stacks tip is the 9th block added on burn chain tipped by 0x4b
        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x4b; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x49; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x48; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 8);

        // LIMITATION: the burn chain tipped at 0x2a will _not_ be updated, since it is not the
        // canonical burn chain tip.
        last_snapshot = SortitionDB::get_block_snapshot(db.conn(), &SortitionId([0x2a; 32]))
            .unwrap()
            .unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2a; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x2b; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x2a; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 6);

        // BUT, when the burn chain tipped by 0x2a overtakes the one tipped by 0x4b, then all blocks
        // will show up.
        make_fork_run(&mut db, &last_snapshot, 2, 0x20);

        // new state of the world:
        // burnchain forks:
        // stx:      1,    2,    3,    4,          6,          8,    9
        // stx:      1,    2,    3,    4,    5,          7,
        // burn:  0x01, 0x02, 0x03, 0x04, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a
        //
        // stx:      1,    2,    3,    4,    6,    7,    8,    9
        // stx:      1,    2,    3,    4,                                        5
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b
        //
        // stx:      1,    2,    3,    4,    7,    8,    9,   10
        // stx:      1,    2,    3,    4,                            5,    6
        // burn:  0x01, 0x02, 0x03, 0x04, 0x45, 0x46, 0x47, 0x48, 0x29, 0x2a, 0x2b, 0x2c

        last_snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
        assert_eq!(
            last_snapshot.burn_header_hash,
            BurnchainHeaderHash([0x2c; 32])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_consensus_hash,
            ConsensusHash([0x49; 20])
        );
        assert_eq!(
            last_snapshot.canonical_stacks_tip_hash,
            BlockHeaderHash([0x48; 32])
        );
        assert_eq!(last_snapshot.canonical_stacks_tip_height, 8);
    }
}
