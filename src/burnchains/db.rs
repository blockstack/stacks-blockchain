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

use std::fmt;

use std::collections::{HashMap, HashSet};
use std::{cmp, fs, io, path::Path};

use rusqlite::{
    types::ToSql, Connection, OpenFlags, OptionalExtension, Row, Transaction, NO_PARAMS,
};
use serde_json;

use burnchains::affirmation::*;
use burnchains::Txid;
use burnchains::{
    Burnchain, BurnchainBlock, BurnchainBlockHeader, BurnchainSigner, Error as BurnchainError,
    PoxConstants,
};
use chainstate::burn::operations::{
    leader_block_commit::BURN_BLOCK_MINED_AT_MODULUS, BlockstackOperationType, LeaderBlockCommitOp,
};
use chainstate::burn::BlockSnapshot;
use chainstate::stacks::index::MarfTrieId;
use util::db::{
    opt_u64_to_sql, query_row, query_row_panic, query_rows, sql_pragma, tx_begin_immediate,
    tx_busy_handler, u64_to_sql, DBConn, Error as DBError, FromColumn, FromRow,
};

use crate::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash};
use crate::types::proof::ClarityMarfTrieId;

pub struct BurnchainDB {
    conn: Connection,
}

pub struct BurnchainDBTransaction<'a> {
    sql_tx: Transaction<'a>,
}

pub struct BurnchainBlockData {
    pub header: BurnchainBlockHeader,
    pub ops: Vec<BlockstackOperationType>,
}

/// A trait for reading burnchain block headers
pub trait BurnchainHeaderReader {
    fn read_burnchain_headers(
        &self,
        start_height: u64,
        end_height: u64,
    ) -> Result<Vec<BurnchainBlockHeader>, DBError>;
    fn get_burnchain_headers_height(&self) -> Result<u64, DBError>;

    fn read_burnchain_header(&self, height: u64) -> Result<Option<BurnchainBlockHeader>, DBError> {
        let mut hdrs = self.read_burnchain_headers(height, height.saturating_add(1))?;
        Ok(hdrs.pop())
    }
}

#[derive(Debug, Clone)]
pub struct BlockCommitMetadata {
    pub burn_block_hash: BurnchainHeaderHash,
    pub txid: Txid,
    pub block_height: u64,
    pub vtxindex: u32,
    pub affirmation_id: u64,
    /// if Some(..), then this block-commit is the anchor block for a reward cycle, and the
    /// reward cycle is represented as the inner u64.
    pub anchor_block: Option<u64>,
    /// If Some(..), then this is the anchor block that this block-commit descends from
    pub anchor_block_descendant: Option<u64>,
}

impl FromColumn<AffirmationMap> for AffirmationMap {
    fn from_column<'a>(row: &'a Row, col_name: &str) -> Result<AffirmationMap, DBError> {
        let txt: String = row.get_unwrap(col_name);
        let am = AffirmationMap::decode(&txt).ok_or(DBError::ParseError)?;
        Ok(am)
    }
}

impl FromRow<AffirmationMap> for AffirmationMap {
    fn from_row<'a>(row: &'a Row) -> Result<AffirmationMap, DBError> {
        AffirmationMap::from_column(row, "affirmation_map")
    }
}

impl FromRow<BlockCommitMetadata> for BlockCommitMetadata {
    fn from_row<'a>(row: &'a Row) -> Result<BlockCommitMetadata, DBError> {
        let burn_block_hash = BurnchainHeaderHash::from_column(row, "burn_block_hash")?;
        let txid = Txid::from_column(row, "txid")?;
        let block_height = u64::from_column(row, "block_height")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");
        let affirmation_id = u64::from_column(row, "affirmation_id")?;
        let anchor_block_i64: Option<i64> = row.get_unwrap("anchor_block");
        let anchor_block = match anchor_block_i64 {
            Some(ab) => {
                if ab < 0 {
                    return Err(DBError::ParseError);
                }
                Some(ab as u64)
            }
            None => None,
        };

        let anchor_block_descendant_i64: Option<i64> = row.get_unwrap("anchor_block_descendant");
        let anchor_block_descendant = match anchor_block_descendant_i64 {
            Some(abd) => {
                if abd < 0 {
                    return Err(DBError::ParseError);
                }
                Some(abd as u64)
            }
            None => None,
        };

        Ok(BlockCommitMetadata {
            burn_block_hash,
            txid,
            block_height,
            vtxindex,
            affirmation_id,
            anchor_block: anchor_block,
            anchor_block_descendant,
        })
    }
}

/// Apply safety checks on extracted blockstack transactions
/// - put them in order by vtxindex
/// - make sure there are no vtxindex duplicates
fn apply_blockstack_txs_safety_checks(
    block_height: u64,
    blockstack_txs: &mut Vec<BlockstackOperationType>,
) -> () {
    // safety -- make sure these are in order
    blockstack_txs.sort_by(|ref a, ref b| a.vtxindex().partial_cmp(&b.vtxindex()).unwrap());

    // safety -- no duplicate vtxindex (shouldn't happen but crash if so)
    if blockstack_txs.len() > 1 {
        for i in 0..blockstack_txs.len() - 1 {
            if blockstack_txs[i].vtxindex() == blockstack_txs[i + 1].vtxindex() {
                panic!(
                    "FATAL: BUG: duplicate vtxindex {} in block {}",
                    blockstack_txs[i].vtxindex(),
                    blockstack_txs[i].block_height()
                );
            }
        }
    }

    // safety -- block heights all match
    for tx in blockstack_txs.iter() {
        if tx.block_height() != block_height {
            panic!(
                "FATAL: BUG: block height mismatch: {} != {}",
                tx.block_height(),
                block_height
            );
        }
    }
}

impl FromRow<BurnchainBlockHeader> for BurnchainBlockHeader {
    fn from_row(row: &Row) -> Result<BurnchainBlockHeader, DBError> {
        let block_height = u64::from_column(row, "block_height")?;
        let block_hash = BurnchainHeaderHash::from_column(row, "block_hash")?;
        let timestamp = u64::from_column(row, "timestamp")?;
        let num_txs = u64::from_column(row, "num_txs")?;
        let parent_block_hash = BurnchainHeaderHash::from_column(row, "parent_block_hash")?;

        Ok(BurnchainBlockHeader {
            block_height,
            block_hash,
            timestamp,
            num_txs,
            parent_block_hash,
        })
    }
}

impl FromRow<BlockstackOperationType> for BlockstackOperationType {
    fn from_row(row: &Row) -> Result<BlockstackOperationType, DBError> {
        let serialized: String = row.get_unwrap("op");
        let deserialized = serde_json::from_str(&serialized)
            .expect("CORRUPTION: db store un-deserializable block op");

        Ok(deserialized)
    }
}

pub const BURNCHAIN_DB_VERSION: &'static str = "2";

const BURNCHAIN_DB_SCHEMA: &'static str = r#"
CREATE TABLE burnchain_db_block_headers (
    block_height INTEGER NOT NULL,
    block_hash TEXT UNIQUE NOT NULL,
    parent_block_hash TEXT NOT NULL,
    num_txs INTEGER NOT NULL,
    timestamp INTEGER NOT NULL,

    PRIMARY KEY(block_hash)
);

CREATE TABLE burnchain_db_block_ops (
    block_hash TEXT NOT NULL,
    op TEXT NOT NULL,
    txid TEXT NOT NULL,

    FOREIGN KEY(block_hash) REFERENCES burnchain_db_block_headers(block_hash)
);

CREATE TABLE affirmation_maps (
    affirmation_id INTEGER PRIMARY KEY AUTOINCREMENT,
    weight INTEGER NOT NULL,
    affirmation_map TEXT NOT NULL
);
CREATE INDEX affirmation_maps_index ON affirmation_maps(affirmation_map);

-- ensure anchor block uniqueness
CREATE TABLE anchor_blocks (
    reward_cycle INTEGER PRIMARY KEY
);

CREATE TABLE block_commit_metadata (
    burn_block_hash TEXT NOT NULL,
    txid TEXT NOT NULL,
    block_height INTEGER NOT NULL,
    vtxindex INTEGER NOT NULL,
    
    affirmation_id INTEGER NOT NULL,
    anchor_block INTEGER,
    anchor_block_descendant INTEGER,

    PRIMARY KEY(burn_block_hash,txid),
    FOREIGN KEY(affirmation_id) REFERENCES affirmation_maps(affirmation_id),
    FOREIGN KEY(anchor_block) REFERENCES anchor_blocks(reward_cycle)
);

-- override the canonical affirmation map at the operator's discression
CREATE TABLE overrides (
    reward_cycle INTEGER PRIMARY KEY NOT NULL,
    affirmation_map TEXT NOT NULL
);

CREATE TABLE db_config(version TEXT NOT NULL);

INSERT INTO affirmation_maps(affirmation_id,weight,affirmation_map) VALUES (0,0,""); -- empty affirmation map
"#;

impl<'a> BurnchainDBTransaction<'a> {
    fn store_burnchain_db_entry(
        &self,
        header: &BurnchainBlockHeader,
    ) -> Result<i64, BurnchainError> {
        let sql = "INSERT INTO burnchain_db_block_headers
                   (block_height, block_hash, parent_block_hash, num_txs, timestamp)
                   VALUES (?, ?, ?, ?, ?)";
        let args: &[&dyn ToSql] = &[
            &u64_to_sql(header.block_height)?,
            &header.block_hash,
            &header.parent_block_hash,
            &u64_to_sql(header.num_txs)?,
            &u64_to_sql(header.timestamp)?,
        ];
        match self.sql_tx.execute(sql, args) {
            Ok(_) => Ok(self.sql_tx.last_insert_rowid()),
            Err(e) => Err(e.into()),
        }
    }

    fn insert_block_commit_affirmation_map(
        &self,
        affirmation_map: &AffirmationMap,
    ) -> Result<u64, DBError> {
        let weight = affirmation_map.weight();
        let sql = "INSERT INTO affirmation_maps (affirmation_map,weight) VALUES (?1,?2)";
        let args: &[&dyn ToSql] = &[&affirmation_map.encode(), &u64_to_sql(weight)?];
        match self.sql_tx.execute(sql, args) {
            Ok(_) => {
                let am_id = BurnchainDB::get_affirmation_map_id(&self.sql_tx, &affirmation_map)?
                    .expect("BUG: no affirmation ID for affirmation map we just inserted");
                Ok(am_id)
            }
            Err(e) => Err(DBError::SqliteError(e)),
        }
    }

    fn update_block_commit_affirmation(
        &self,
        block_commit: &LeaderBlockCommitOp,
        anchor_block_descendant: Option<u64>,
        affirmation_id: u64,
    ) -> Result<(), DBError> {
        let sql = "UPDATE block_commit_metadata SET affirmation_id = ?1, anchor_block_descendant = ?2 WHERE burn_block_hash = ?3 AND txid = ?4";
        let args: &[&dyn ToSql] = &[
            &u64_to_sql(affirmation_id)?,
            &opt_u64_to_sql(anchor_block_descendant)?,
            &block_commit.burn_header_hash,
            &block_commit.txid,
        ];
        match self.sql_tx.execute(sql, args) {
            Ok(_) => {
                test_debug!("Set affirmation map ID of {} - {},{},{} (parent {},{}) to {} (anchor block descendant? {:?})",
                            &block_commit.burn_header_hash, &block_commit.txid, block_commit.block_height, block_commit.vtxindex, block_commit.parent_block_ptr, block_commit.parent_vtxindex, affirmation_id, &anchor_block_descendant);
                Ok(())
            }
            Err(e) => Err(DBError::SqliteError(e)),
        }
    }

    pub fn set_anchor_block(
        &self,
        block_commit: &LeaderBlockCommitOp,
        target_reward_cycle: u64,
    ) -> Result<(), DBError> {
        let sql = "INSERT OR REPLACE INTO anchor_blocks (reward_cycle) VALUES (?1)";
        let args: &[&dyn ToSql] = &[&u64_to_sql(target_reward_cycle)?];
        self.sql_tx
            .execute(sql, args)
            .map_err(|e| DBError::SqliteError(e))?;

        let sql = "UPDATE block_commit_metadata SET anchor_block = ?1 WHERE burn_block_hash = ?2 AND txid = ?3";
        let args: &[&dyn ToSql] = &[
            &u64_to_sql(target_reward_cycle)?,
            &block_commit.burn_header_hash,
            &block_commit.txid,
        ];
        match self.sql_tx.execute(sql, args) {
            Ok(_) => {
                info!(
                    "Set anchor block for reward cycle {} to {},{},{},{}",
                    target_reward_cycle,
                    &block_commit.burn_header_hash,
                    &block_commit.txid,
                    &block_commit.block_height,
                    &block_commit.vtxindex
                );
                Ok(())
            }
            Err(e) => Err(DBError::SqliteError(e)),
        }
    }

    pub fn clear_anchor_block(&self, reward_cycle: u64) -> Result<(), DBError> {
        let sql = "UPDATE block_commit_metadata SET anchor_block = NULL WHERE anchor_block = ?1";
        let args: &[&dyn ToSql] = &[&u64_to_sql(reward_cycle)?];
        self.sql_tx
            .execute(sql, args)
            .map(|_| ())
            .map_err(|e| DBError::SqliteError(e))
    }

    /// Clear the descendancy data and affirmations for all block-commits in a reward cycle
    /// (both the reward and prepare phases), as well as anchor block data.
    pub fn clear_reward_cycle_descendancies(
        &self,
        reward_cycle: u64,
        burnchain: &Burnchain,
    ) -> Result<(), DBError> {
        let first_block_height = burnchain.reward_cycle_to_block_height(reward_cycle);
        let last_block_height = burnchain.reward_cycle_to_block_height(reward_cycle + 1);

        test_debug!(
            "Clear descendancy data for reward cycle {} (blocks {}-{})",
            reward_cycle,
            first_block_height,
            last_block_height
        );

        let sql = "UPDATE block_commit_metadata SET affirmation_id = 0, anchor_block = NULL, anchor_block_descendant = NULL WHERE block_height >= ?1 AND block_height < ?2";
        let args: &[&dyn ToSql] = &[
            &u64_to_sql(first_block_height)?,
            &u64_to_sql(last_block_height)?,
        ];
        self.sql_tx
            .execute(sql, args)
            .map(|_| ())
            .map_err(|e| DBError::SqliteError(e))
    }

    /// Calculate a burnchain block's block-commits' descendancy information
    pub fn update_block_descendancy<B: BurnchainHeaderReader>(
        &self,
        indexer: &B,
        hdr: &BurnchainBlockHeader,
        burnchain: &Burnchain,
    ) -> Result<(), BurnchainError> {
        // find all block-commits for this block
        let commits: Vec<LeaderBlockCommitOp> = {
            let block_ops_qry = "SELECT * FROM burnchain_db_block_ops WHERE block_hash = ?";
            let block_ops = query_rows(&self.sql_tx, block_ops_qry, &[&hdr.block_hash])?;
            block_ops
                .into_iter()
                .filter_map(|op| {
                    if let BlockstackOperationType::LeaderBlockCommit(opdata) = op {
                        Some(opdata)
                    } else {
                        None
                    }
                })
                .collect()
        };
        if commits.len() == 0 {
            test_debug!("No block-commits for block {}", hdr.block_height);
            return Ok(());
        }

        // for each commit[i], find its parent commit
        let mut parent_commits = vec![];
        for commit in commits.iter() {
            let parent_commit_opt = if commit.parent_block_ptr != 0 || commit.parent_vtxindex != 0 {
                // parent is not genesis
                BurnchainDB::get_commit_at(
                    &self.sql_tx,
                    indexer,
                    commit.parent_block_ptr,
                    commit.parent_vtxindex,
                )?
            } else {
                // parnet is genesis
                test_debug!(
                    "Parent block-commit of {},{},{} is the genesis commit",
                    &commit.txid,
                    commit.block_height,
                    commit.vtxindex
                );
                None
            };

            parent_commits.push(parent_commit_opt);
        }
        assert_eq!(parent_commits.len(), commits.len());

        // for each parent block-commit and block-commit, calculate the block-commit's new
        // affirmation map
        for (parent_commit_opt, commit) in parent_commits.iter().zip(commits.iter()) {
            if let Some(parent_commit) = parent_commit_opt.as_ref() {
                if get_parent_child_reward_cycles(parent_commit, commit, burnchain).is_some() {
                    // we have enough info to calculate this commit's affirmation
                    self.make_reward_phase_affirmation_map(burnchain, commit, parent_commit)?;
                } else {
                    // parent is invalid
                    test_debug!(
                        "No block-commit parent reward cycle found for {},{},{}",
                        &commit.txid,
                        commit.block_height,
                        commit.vtxindex
                    );
                    self.update_block_commit_affirmation(commit, None, 0)?;
                }
            } else {
                if commit.parent_block_ptr == 0 && commit.parent_vtxindex == 0 {
                    test_debug!(
                        "Block-commit parent of {},{},{} is genesis",
                        &commit.txid,
                        commit.block_height,
                        commit.vtxindex
                    );
                } else {
                    // this is an invalid commit -- no parent found
                    test_debug!(
                        "No block-commit parent found for {},{},{}",
                        &commit.txid,
                        commit.block_height,
                        commit.vtxindex
                    );
                }
                self.update_block_commit_affirmation(commit, None, 0)?;
            }
        }

        Ok(())
    }

    /// Create a prepare-phase affirmation map.  This is only done at the very end of a reward
    /// cycle, once the anchor block is chosen and a new reward cycle is about to begin.  This
    /// method updates the prepare-phase block-commit's affirmation map to reflect what its miner
    /// believes to be the state of all anchor blocks, _including_ this new reward cycle's anchor
    /// block.
    pub fn make_prepare_phase_affirmation_map<B: BurnchainHeaderReader>(
        &self,
        indexer: &B,
        burnchain: &Burnchain,
        reward_cycle: u64,
        block_commit: &LeaderBlockCommitOp,
        anchor_block: Option<&LeaderBlockCommitOp>,
        descends_from_anchor_block: bool,
    ) -> Result<u64, BurnchainError> {
        test_debug!(
            "Make affirmation map for {},{},{} (parent {},{}) in reward cycle {}",
            &block_commit.txid,
            block_commit.block_height,
            block_commit.vtxindex,
            block_commit.parent_block_ptr,
            block_commit.parent_vtxindex,
            reward_cycle
        );

        let parent = match BurnchainDB::get_commit_at(
            &self.sql_tx,
            indexer,
            block_commit.parent_block_ptr,
            block_commit.parent_vtxindex,
        )? {
            Some(p) => p,
            None => {
                if block_commit.parent_block_ptr == 0 && block_commit.vtxindex == 0 {
                    debug!(
                        "Prepare-phase commit {},{},{} builds off of genesis",
                        &block_commit.block_header_hash,
                        block_commit.block_height,
                        block_commit.vtxindex
                    );
                } else {
                    debug!(
                        "Prepare-phase commit {},{},{} has no parent, so must be invalid",
                        &block_commit.block_header_hash,
                        block_commit.block_height,
                        block_commit.vtxindex
                    );
                }
                return Ok(0);
            }
        };

        let parent_metadata =
            BurnchainDB::get_commit_metadata(&self.sql_tx, &parent.burn_header_hash, &parent.txid)?
                .expect("BUG: no metadata found for parent block-commit");

        let (am, affirmed_reward_cycle) = if let Some(anchor_block) = anchor_block {
            let anchor_am_id =
                BurnchainDB::get_block_commit_affirmation_id(&self.sql_tx, &anchor_block)?
                    .expect("BUG: anchor block has no affirmation map");

            let mut am = BurnchainDB::get_affirmation_map(&self.sql_tx, anchor_am_id)?
                .ok_or(BurnchainError::DBError(DBError::NotFoundError))?;

            if descends_from_anchor_block {
                test_debug!("Prepare-phase commit {},{},{} descends from anchor block {},{},{} for reward cycle {}",
                            &block_commit.block_header_hash, block_commit.block_height, block_commit.vtxindex, &anchor_block.block_header_hash, anchor_block.block_height, anchor_block.vtxindex, reward_cycle);

                am.push(AffirmationMapEntry::PoxAnchorBlockPresent);
                (am, Some(reward_cycle))
            } else {
                test_debug!("Prepare-phase commit {},{},{} does NOT descend from anchor block {},{},{} for reward cycle {}",
                            &block_commit.block_header_hash, block_commit.block_height, block_commit.vtxindex, &anchor_block.block_header_hash, anchor_block.block_height, anchor_block.vtxindex, reward_cycle);

                am.push(AffirmationMapEntry::PoxAnchorBlockAbsent);
                (am, parent_metadata.anchor_block_descendant)
            }
        } else {
            let (parent_reward_cycle, _) =
                get_parent_child_reward_cycles(&parent, block_commit, burnchain)
                    .ok_or(BurnchainError::DBError(DBError::NotFoundError))?;

            // load up the affirmation map for the last anchor block the parent affirmed
            let (mut am, parent_rc_opt) = match parent_metadata.anchor_block_descendant {
                Some(parent_ab_rc) => {
                    // parent affirmed some past anchor block
                    let (_, ab_metadata) = BurnchainDB::get_anchor_block_commit(&self.sql_tx, parent_ab_rc)?
                            .expect(&format!("BUG: parent descends from a reward cycle with an anchor block ({}), but no anchor block found", parent_ab_rc));

                    let mut am =
                        BurnchainDB::get_affirmation_map(&self.sql_tx, ab_metadata.affirmation_id)?
                            .expect("BUG: no affirmation map for parent commit's anchor block");

                    test_debug!("Prepare-phase commit {},{},{} does nothing for reward cycle {}, but it builds on its parent which affirms anchor block for reward cycle {} ({}) (affirms? {})",
                                    &block_commit.block_header_hash, block_commit.block_height, block_commit.vtxindex, reward_cycle, parent_ab_rc, &am, (am.len() as u64) < parent_ab_rc);

                    if (am.len() as u64) < parent_ab_rc {
                        // child is affirming the parent
                        am.push(AffirmationMapEntry::PoxAnchorBlockPresent);
                    }

                    (am, Some(parent_ab_rc))
                }
                None => {
                    let mut parent_am = BurnchainDB::get_affirmation_map(
                        &self.sql_tx,
                        parent_metadata.affirmation_id,
                    )?
                    .expect("BUG: no affirmation map for parent commit");

                    // parent affirms no anchor blocks
                    test_debug!("Prepare-phase commit {},{},{} does nothing for reward cycle {}, and it builds on a parent {},{} {} which affirms no anchor block (affirms? {})",
                                    &block_commit.block_header_hash, block_commit.block_height, block_commit.vtxindex, reward_cycle, block_commit.parent_block_ptr, block_commit.parent_vtxindex, &parent_am, (parent_am.len() as u64) < parent_reward_cycle);

                    if (parent_am.len() as u64) < parent_reward_cycle {
                        // child is affirming the parent
                        parent_am.push(AffirmationMapEntry::Nothing);
                    }

                    (parent_am, None)
                }
            };

            let num_affirmed = am.len() as u64;
            for rc in (num_affirmed + 1)..(reward_cycle + 1) {
                if BurnchainDB::has_anchor_block(&self.sql_tx, rc)? {
                    test_debug!(
                        "Commit {},{},{} skips reward cycle {} with anchor block",
                        &block_commit.block_header_hash,
                        block_commit.block_height,
                        block_commit.vtxindex,
                        rc
                    );
                    am.push(AffirmationMapEntry::PoxAnchorBlockAbsent);
                } else {
                    // affirmation weight increases even if there's no decision made, because
                    // the lack of a decision is still an affirmation of all prior decisions
                    test_debug!(
                        "Commit {},{},{} skips reward cycle {} without anchor block",
                        &block_commit.block_header_hash,
                        block_commit.block_height,
                        block_commit.vtxindex,
                        rc
                    );
                    am.push(AffirmationMapEntry::Nothing);
                }
            }

            debug!(
                "Prepare-phase commit {},{} affirms parent {},{} with {} descended from {:?}",
                block_commit.block_height,
                block_commit.vtxindex,
                parent.block_height,
                parent.vtxindex,
                &am,
                &parent_metadata.anchor_block_descendant
            );

            (am, parent_rc_opt)
        };

        if let Some(am_id) = BurnchainDB::get_affirmation_map_id(&self.sql_tx, &am)? {
            // child doesn't represent any new affirmations by the network, since its
            // affirmation map already exists.
            if cfg!(test) {
                let _am_weight = BurnchainDB::get_affirmation_weight(&self.sql_tx, am_id)?
                    .expect(&format!("BUG: no affirmation map {}", &am_id));

                test_debug!("Affirmation map of prepare-phase block-commit {},{},{} (parent {},{}) is old: {:?} weight {} affirmed {:?}",
                            &block_commit.txid, block_commit.block_height, block_commit.vtxindex, block_commit.parent_block_ptr, block_commit.parent_vtxindex, &am, _am_weight, &affirmed_reward_cycle);
            }

            self.update_block_commit_affirmation(block_commit, affirmed_reward_cycle, am_id)?;
            Ok(am_id)
        } else {
            test_debug!("Affirmation map of prepare-phase block-commit {},{},{} (parent {},{}) is new: {:?} weight {} affirmed {:?}",
                        &block_commit.txid, block_commit.block_height, block_commit.vtxindex, block_commit.parent_block_ptr, block_commit.parent_vtxindex, &am, am.weight(), &affirmed_reward_cycle);

            let am_id = self.insert_block_commit_affirmation_map(&am)?;
            self.update_block_commit_affirmation(block_commit, affirmed_reward_cycle, am_id)?;
            Ok(am_id)
        }
    }

    /// Make an affirmation map for a block commit in a reward phase (or an in-progress prepare
    /// phase).  This is done once per Bitcoin block, as block-commits are stored.  Affirmation
    /// maps for prepare-phase commits will be recomputed once the reward cycle finishes.
    fn make_reward_phase_affirmation_map(
        &self,
        burnchain: &Burnchain,
        block_commit: &LeaderBlockCommitOp,
        parent: &LeaderBlockCommitOp,
    ) -> Result<u64, BurnchainError> {
        assert_eq!(block_commit.parent_block_ptr as u64, parent.block_height);
        assert_eq!(block_commit.parent_vtxindex as u32, parent.vtxindex);

        let parent_metadata =
            BurnchainDB::get_commit_metadata(&self.sql_tx, &parent.burn_header_hash, &parent.txid)?
                .expect("BUG: no metadata found for existing block commit");

        test_debug!(
            "Reward-phase commit {},{},{} has parent {},{}, anchor block {:?}",
            &block_commit.block_header_hash,
            block_commit.block_height,
            block_commit.vtxindex,
            parent.block_height,
            parent.vtxindex,
            &parent_metadata.anchor_block_descendant
        );

        let child_reward_cycle = burnchain
            .block_height_to_reward_cycle(block_commit.block_height)
            .expect("BUG: block commit exists before first block height");

        let (am, affirmed_anchor_block_reward_cycle) =
            if let Some(parent_ab_rc) = parent_metadata.anchor_block_descendant {
                let am_id = parent_metadata.affirmation_id;
                let mut am = BurnchainDB::get_affirmation_map(&self.sql_tx, am_id)?
                    .expect("BUG: no affirmation map for parent commit");

                test_debug!("Affirmation map of parent is {}", &am);

                let start_rc = am.len() as u64;
                for rc in (start_rc + 1)..(child_reward_cycle + 1) {
                    if BurnchainDB::has_anchor_block(&self.sql_tx, rc)? {
                        test_debug!(
                            "Commit {},{},{} skips reward cycle {} with anchor block",
                            &block_commit.block_header_hash,
                            block_commit.block_height,
                            block_commit.vtxindex,
                            rc
                        );
                        am.push(AffirmationMapEntry::PoxAnchorBlockAbsent);
                    } else {
                        test_debug!(
                            "Commit {},{},{} skips reward cycle {} without anchor block",
                            &block_commit.block_header_hash,
                            block_commit.block_height,
                            block_commit.vtxindex,
                            rc
                        );
                        am.push(AffirmationMapEntry::Nothing);
                    }
                }

                (am, Some(parent_ab_rc))
            } else {
                let mut am = AffirmationMap::empty();
                for rc in 1..(child_reward_cycle + 1) {
                    if BurnchainDB::has_anchor_block(&self.sql_tx, rc)? {
                        test_debug!(
                            "Commit {},{},{} skips reward cycle {} with anchor block",
                            &block_commit.block_header_hash,
                            block_commit.block_height,
                            block_commit.vtxindex,
                            rc
                        );
                        am.push(AffirmationMapEntry::PoxAnchorBlockAbsent);
                    } else {
                        test_debug!(
                            "Commit {},{},{} skips reward cycle {} without anchor block",
                            &block_commit.block_header_hash,
                            block_commit.block_height,
                            block_commit.vtxindex,
                            rc
                        );
                        am.push(AffirmationMapEntry::Nothing);
                    }
                }
                (am, None)
            };

        if let Some(am_id) = BurnchainDB::get_affirmation_map_id(&self.sql_tx, &am)? {
            // child doesn't represent any new affirmations by the network, since its
            // affirmation map already exists.
            if cfg!(test) {
                let _am_weight = BurnchainDB::get_affirmation_weight(&self.sql_tx, am_id)?
                    .expect(&format!("BUG: no affirmation map {}", &am_id));

                test_debug!("Affirmation map of reward-phase block-commit {},{},{} (parent {},{}) is old: {:?} weight {}",
                            &block_commit.txid, block_commit.block_height, block_commit.vtxindex, block_commit.parent_block_ptr, block_commit.parent_vtxindex, &am, _am_weight);
            }

            self.update_block_commit_affirmation(
                block_commit,
                affirmed_anchor_block_reward_cycle,
                am_id,
            )?;
            Ok(am_id)
        } else {
            test_debug!("Affirmation map of reward-phase block-commit {},{},{} (parent {},{}) is new: {:?} weight {}",
                        &block_commit.txid, block_commit.block_height, block_commit.vtxindex, block_commit.parent_block_ptr, block_commit.parent_vtxindex, &am, am.weight());

            let am_id = self.insert_block_commit_affirmation_map(&am)?;

            self.update_block_commit_affirmation(
                block_commit,
                affirmed_anchor_block_reward_cycle,
                am_id,
            )?;

            Ok(am_id)
        }
    }

    fn insert_block_commit_metadata(&self, bcm: BlockCommitMetadata) -> Result<(), BurnchainError> {
        let commit_metadata_sql = "INSERT OR REPLACE INTO block_commit_metadata
                                   (burn_block_hash, txid, block_height, vtxindex, anchor_block, anchor_block_descendant, affirmation_id)
                                   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)";
        let mut stmt = self.sql_tx.prepare(commit_metadata_sql)?;
        let args: &[&dyn ToSql] = &[
            &bcm.burn_block_hash,
            &bcm.txid,
            &u64_to_sql(bcm.block_height)?,
            &bcm.vtxindex,
            &opt_u64_to_sql(bcm.anchor_block)?,
            &opt_u64_to_sql(bcm.anchor_block_descendant)?,
            &u64_to_sql(bcm.affirmation_id)?,
        ];
        stmt.execute(args)?;
        Ok(())
    }

    fn store_blockstack_ops<B: BurnchainHeaderReader>(
        &self,
        burnchain: &Burnchain,
        indexer: &B,
        block_header: &BurnchainBlockHeader,
        block_ops: &[BlockstackOperationType],
    ) -> Result<(), BurnchainError> {
        let sql = "INSERT INTO burnchain_db_block_ops
                   (block_hash, txid, op) VALUES (?, ?, ?)";
        let mut stmt = self.sql_tx.prepare(sql)?;
        for op in block_ops.iter() {
            let serialized_op =
                serde_json::to_string(op).expect("Failed to serialize parsed BlockstackOp");
            let args: &[&dyn ToSql] = &[&block_header.block_hash, op.txid_ref(), &serialized_op];
            stmt.execute(args)?;
        }

        for op in block_ops.iter() {
            if let BlockstackOperationType::LeaderBlockCommit(ref opdata) = op {
                let bcm = BlockCommitMetadata {
                    burn_block_hash: block_header.block_hash.clone(),
                    txid: opdata.txid.clone(),
                    block_height: opdata.block_height,
                    vtxindex: opdata.vtxindex,
                    // NOTE: these fields are filled in by the subsequent call.
                    affirmation_id: 0,
                    anchor_block: None,
                    anchor_block_descendant: None,
                };
                self.insert_block_commit_metadata(bcm)?;
            }
        }

        self.update_block_descendancy(indexer, block_header, burnchain)?;
        Ok(())
    }

    pub fn commit(self) -> Result<(), BurnchainError> {
        self.sql_tx.commit().map_err(BurnchainError::from)
    }

    pub fn conn(&self) -> &DBConn {
        &self.sql_tx
    }

    pub fn get_canonical_chain_tip(&self) -> Result<BurnchainBlockHeader, BurnchainError> {
        BurnchainDB::inner_get_canonical_chain_tip(&self.sql_tx)
    }

    /// You'd only do this in network emergencies, where node operators are expected to declare an
    /// anchor block missing (or present).  Ideally there'd be a smart contract somewhere for this.
    pub fn set_override_affirmation_map(
        &self,
        reward_cycle: u64,
        affirmation_map: AffirmationMap,
    ) -> Result<(), DBError> {
        assert_eq!((affirmation_map.len() as u64) + 1, reward_cycle);
        let qry = "INSERT INTO overrides (reward_cycle, affirmation_map) VALUES (?1, ?2)";
        let args: &[&dyn ToSql] = &[&u64_to_sql(reward_cycle)?, &affirmation_map.encode()];

        let mut stmt = self.sql_tx.prepare(qry)?;
        stmt.execute(args)?;
        Ok(())
    }

    pub fn clear_override_affirmation_map(&self, reward_cycle: u64) -> Result<(), DBError> {
        let qry = "DELETE FROM overrides WHERE reward_cycle = ?1";
        let args: &[&dyn ToSql] = &[&u64_to_sql(reward_cycle)?];

        let mut stmt = self.sql_tx.prepare(qry)?;
        stmt.execute(args)?;
        Ok(())
    }
}

impl BurnchainDB {
    pub fn connect(
        path: &str,
        burnchain: &Burnchain,
        readwrite: bool,
    ) -> Result<BurnchainDB, BurnchainError> {
        let mut create_flag = false;
        let open_flags = match fs::metadata(path) {
            Err(e) => {
                if e.kind() == io::ErrorKind::NotFound {
                    // need to create
                    if readwrite {
                        create_flag = true;
                        let ppath = Path::new(path);
                        let pparent_path = ppath
                            .parent()
                            .expect(&format!("BUG: no parent of '{}'", path));
                        fs::create_dir_all(&pparent_path)
                            .map_err(|e| BurnchainError::from(DBError::IOError(e)))?;

                        OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
                    } else {
                        return Err(BurnchainError::from(DBError::NoDBError));
                    }
                } else {
                    return Err(BurnchainError::from(DBError::IOError(e)));
                }
            }
            Ok(_md) => {
                // can just open
                if readwrite {
                    OpenFlags::SQLITE_OPEN_READ_WRITE
                } else {
                    OpenFlags::SQLITE_OPEN_READ_ONLY
                }
            }
        };

        let conn = Connection::open_with_flags(path, open_flags)
            .expect(&format!("FAILED to open: {}", path));

        conn.busy_handler(Some(tx_busy_handler))?;

        let mut db = BurnchainDB { conn };

        if create_flag {
            let db_tx = db.tx_begin()?;
            sql_pragma(&db_tx.sql_tx, "PRAGMA journal_mode = WAL;")?;
            db_tx.sql_tx.execute_batch(BURNCHAIN_DB_SCHEMA)?;
            db_tx.sql_tx.execute(
                "INSERT INTO db_config (version) VALUES (?1)",
                &[&BURNCHAIN_DB_VERSION],
            )?;

            let first_block_header = BurnchainBlockHeader {
                block_height: burnchain.first_block_height,
                block_hash: burnchain.first_block_hash.clone(),
                timestamp: burnchain.first_block_timestamp.into(),
                num_txs: 0,
                parent_block_hash: BurnchainHeaderHash::sentinel(),
            };

            db_tx.store_burnchain_db_entry(&first_block_header)?;

            let first_snapshot = BlockSnapshot::initial(
                burnchain.first_block_height,
                &burnchain.first_block_hash,
                burnchain.first_block_timestamp as u64,
            );
            let first_snapshot_commit_metadata = BlockCommitMetadata {
                burn_block_hash: first_snapshot.burn_header_hash.clone(),
                txid: first_snapshot.winning_block_txid.clone(),
                block_height: first_snapshot.block_height,
                vtxindex: 0,
                affirmation_id: 0,
                anchor_block: None,
                anchor_block_descendant: None,
            };
            db_tx.insert_block_commit_metadata(first_snapshot_commit_metadata)?;
            db_tx.commit()?;
        }

        Ok(db)
    }

    pub fn open(path: &str, readwrite: bool) -> Result<BurnchainDB, BurnchainError> {
        let open_flags = if readwrite {
            OpenFlags::SQLITE_OPEN_READ_WRITE
        } else {
            OpenFlags::SQLITE_OPEN_READ_ONLY
        };
        let conn = Connection::open_with_flags(path, open_flags)?;
        conn.busy_handler(Some(tx_busy_handler))?;

        Ok(BurnchainDB { conn })
    }

    pub fn conn(&self) -> &DBConn {
        &self.conn
    }

    pub fn tx_begin<'a>(&'a mut self) -> Result<BurnchainDBTransaction<'a>, BurnchainError> {
        let sql_tx = tx_begin_immediate(&mut self.conn)?;
        Ok(BurnchainDBTransaction { sql_tx: sql_tx })
    }

    fn inner_get_canonical_chain_tip(
        conn: &DBConn,
    ) -> Result<BurnchainBlockHeader, BurnchainError> {
        let qry = "SELECT * FROM burnchain_db_block_headers ORDER BY block_height DESC, block_hash ASC LIMIT 1";
        let opt = query_row(conn, qry, NO_PARAMS)?;
        Ok(opt.expect("CORRUPTION: No canonical burnchain tip"))
    }

    pub fn get_canonical_chain_tip(&self) -> Result<BurnchainBlockHeader, BurnchainError> {
        BurnchainDB::inner_get_canonical_chain_tip(&self.conn)
    }

    #[cfg(test)]
    pub fn get_first_header(&self) -> Result<BurnchainBlockHeader, BurnchainError> {
        let qry = "SELECT * FROM burnchain_db_block_headers ORDER BY block_height ASC, block_hash DESC LIMIT 1";
        let opt = query_row(&self.conn, qry, NO_PARAMS)?;
        Ok(opt.expect("CORRUPTION: No canonical burnchain tip"))
    }

    pub fn get_burnchain_block(
        conn: &DBConn,
        block: &BurnchainHeaderHash,
    ) -> Result<BurnchainBlockData, BurnchainError> {
        let block_header_qry =
            "SELECT * FROM burnchain_db_block_headers WHERE block_hash = ? LIMIT 1";
        let block_ops_qry = "SELECT * FROM burnchain_db_block_ops WHERE block_hash = ?";

        let block_header = query_row(conn, block_header_qry, &[block])?
            .ok_or_else(|| BurnchainError::UnknownBlock(block.clone()))?;
        let block_ops = query_rows(conn, block_ops_qry, &[block])?;

        Ok(BurnchainBlockData {
            header: block_header,
            ops: block_ops,
        })
    }

    fn inner_get_burnchain_op(conn: &DBConn, txid: &Txid) -> Option<BlockstackOperationType> {
        let qry = "SELECT op FROM burnchain_db_block_ops WHERE txid = ?";

        match query_row(conn, qry, &[txid]) {
            Ok(res) => res,
            Err(e) => {
                warn!(
                    "BurnchainDB Error finding burnchain op: {:?}. txid = {}",
                    e, txid
                );
                None
            }
        }
    }

    pub fn get_burnchain_op(&self, txid: &Txid) -> Option<BlockstackOperationType> {
        BurnchainDB::inner_get_burnchain_op(&self.conn, txid)
    }

    /// Filter out the burnchain block's transactions that could be blockstack transactions.
    /// Return the ordered list of blockstack operations by vtxindex
    fn get_blockstack_transactions(
        &self,
        burnchain: &Burnchain,
        block: &BurnchainBlock,
        block_header: &BurnchainBlockHeader,
    ) -> Vec<BlockstackOperationType> {
        debug!(
            "Extract Blockstack transactions from block {} {}",
            block.block_height(),
            &block.block_hash()
        );

        let mut ops = Vec::new();
        let mut pre_stx_ops = HashMap::new();

        for tx in block.txs().iter() {
            let result =
                Burnchain::classify_transaction(burnchain, self, block_header, &tx, &pre_stx_ops);
            if let Some(classified_tx) = result {
                if let BlockstackOperationType::PreStx(pre_stx_op) = classified_tx {
                    pre_stx_ops.insert(pre_stx_op.txid.clone(), pre_stx_op);
                } else {
                    ops.push(classified_tx);
                }
            }
        }

        ops.extend(
            pre_stx_ops
                .into_iter()
                .map(|(_, op)| BlockstackOperationType::PreStx(op)),
        );

        ops.sort_by_key(|op| op.vtxindex());

        ops
    }

    pub fn get_affirmation_map(
        conn: &DBConn,
        affirmation_id: u64,
    ) -> Result<Option<AffirmationMap>, DBError> {
        let sql = "SELECT affirmation_map FROM affirmation_maps WHERE affirmation_id = ?1";
        let args: &[&dyn ToSql] = &[&u64_to_sql(affirmation_id)?];
        query_row(conn, sql, args)
    }

    pub fn get_affirmation_weight(
        conn: &DBConn,
        affirmation_id: u64,
    ) -> Result<Option<u64>, DBError> {
        let sql = "SELECT weight FROM affirmation_maps WHERE affirmation_id = ?1";
        let args: &[&dyn ToSql] = &[&u64_to_sql(affirmation_id)?];
        query_row(conn, sql, args)
    }

    pub fn get_affirmation_map_id(
        conn: &DBConn,
        affirmation_map: &AffirmationMap,
    ) -> Result<Option<u64>, DBError> {
        let sql = "SELECT affirmation_id FROM affirmation_maps WHERE affirmation_map = ?1";
        let args: &[&dyn ToSql] = &[&affirmation_map.encode()];
        query_row(conn, sql, args)
    }

    pub fn get_affirmation_map_id_at(
        conn: &DBConn,
        burn_header_hash: &BurnchainHeaderHash,
        txid: &Txid,
    ) -> Result<Option<u64>, DBError> {
        let sql = "SELECT affirmation_id FROM block_commit_metadata WHERE burn_block_hash = ?1 AND txid = ?2";
        let args: &[&dyn ToSql] = &[burn_header_hash, txid];
        query_row(conn, sql, args)
    }

    pub fn get_affirmation_map_at(
        conn: &DBConn,
        burn_header_hash: &BurnchainHeaderHash,
        txid: &Txid,
    ) -> Result<Option<AffirmationMap>, DBError> {
        let am_id_opt = BurnchainDB::get_affirmation_map_id_at(conn, burn_header_hash, txid)?;
        match am_id_opt {
            Some(am_id) => BurnchainDB::get_affirmation_map(conn, am_id),
            None => Ok(None),
        }
    }

    pub fn get_block_commit_affirmation_id(
        conn: &DBConn,
        block_commit: &LeaderBlockCommitOp,
    ) -> Result<Option<u64>, DBError> {
        BurnchainDB::get_affirmation_map_id_at(
            conn,
            &block_commit.burn_header_hash,
            &block_commit.txid,
        )
    }

    pub fn is_anchor_block(
        conn: &DBConn,
        burn_header_hash: &BurnchainHeaderHash,
        txid: &Txid,
    ) -> Result<bool, DBError> {
        let sql = "SELECT 1 FROM block_commit_metadata WHERE anchor_block IS NOT NULL AND burn_block_hash = ?1 AND txid = ?2";
        let args: &[&dyn ToSql] = &[burn_header_hash, txid];
        query_row(conn, sql, args)?.ok_or(DBError::NotFoundError)
    }

    pub fn has_anchor_block(conn: &DBConn, reward_cycle: u64) -> Result<bool, DBError> {
        let sql = "SELECT 1 FROM block_commit_metadata WHERE anchor_block = ?1";
        let args: &[&dyn ToSql] = &[&u64_to_sql(reward_cycle)?];
        Ok(query_row::<bool, _>(conn, sql, args)?.is_some())
    }

    pub fn get_anchor_block_commit(
        conn: &DBConn,
        reward_cycle: u64,
    ) -> Result<Option<(LeaderBlockCommitOp, BlockCommitMetadata)>, DBError> {
        let sql = "SELECT * FROM block_commit_metadata WHERE anchor_block = ?1";
        let args: &[&dyn ToSql] = &[&u64_to_sql(reward_cycle)?];
        let commit_metadata = match query_row::<BlockCommitMetadata, _>(conn, sql, args)? {
            Some(cmt) => cmt,
            None => {
                return Ok(None);
            }
        };

        let commit = BurnchainDB::get_block_commit(conn, &commit_metadata.txid)?
            .expect("BUG: no block-commit for block-commit metadata");

        Ok(Some((commit, commit_metadata)))
    }

    pub fn get_block_commit_affirmation_map(
        conn: &DBConn,
        block_commit: &LeaderBlockCommitOp,
    ) -> Result<Option<AffirmationMap>, DBError> {
        let am_id = match BurnchainDB::get_block_commit_affirmation_id(conn, block_commit)? {
            Some(am_id) => am_id,
            None => {
                return Ok(None);
            }
        };

        BurnchainDB::get_affirmation_map(conn, am_id)
    }

    // do NOT call directly; only use in tests
    pub fn store_new_burnchain_block_ops_unchecked<B: BurnchainHeaderReader>(
        &mut self,
        burnchain: &Burnchain,
        indexer: &B,
        block_header: &BurnchainBlockHeader,
        blockstack_ops: &Vec<BlockstackOperationType>,
    ) -> Result<(), BurnchainError> {
        let db_tx = self.tx_begin()?;

        test_debug!(
            "Store block {},{} with {} ops",
            &block_header.block_hash,
            block_header.block_height,
            blockstack_ops.len()
        );
        db_tx.store_burnchain_db_entry(block_header)?;
        db_tx.store_blockstack_ops(burnchain, indexer, &block_header, blockstack_ops)?;

        db_tx.commit()?;
        Ok(())
    }

    pub fn store_new_burnchain_block<B: BurnchainHeaderReader>(
        &mut self,
        burnchain: &Burnchain,
        indexer: &B,
        block: &BurnchainBlock,
    ) -> Result<Vec<BlockstackOperationType>, BurnchainError> {
        let header = block.header();
        debug!("Storing new burnchain block";
              "burn_header_hash" => %header.block_hash.to_string());
        let mut blockstack_ops = self.get_blockstack_transactions(burnchain, block, &header);
        apply_blockstack_txs_safety_checks(header.block_height, &mut blockstack_ops);

        self.store_new_burnchain_block_ops_unchecked(burnchain, indexer, &header, &blockstack_ops)?;
        Ok(blockstack_ops)
    }

    #[cfg(test)]
    pub fn raw_store_burnchain_block<B: BurnchainHeaderReader>(
        &mut self,
        burnchain: &Burnchain,
        indexer: &B,
        header: BurnchainBlockHeader,
        mut blockstack_ops: Vec<BlockstackOperationType>,
    ) -> Result<(), BurnchainError> {
        apply_blockstack_txs_safety_checks(header.block_height, &mut blockstack_ops);

        let db_tx = self.tx_begin()?;

        db_tx.store_burnchain_db_entry(&header)?;
        db_tx.store_blockstack_ops(burnchain, indexer, &header, &blockstack_ops)?;

        db_tx.commit()?;

        Ok(())
    }

    pub fn get_block_commit(
        conn: &DBConn,
        txid: &Txid,
    ) -> Result<Option<LeaderBlockCommitOp>, DBError> {
        let op = BurnchainDB::inner_get_burnchain_op(conn, txid);
        if let Some(BlockstackOperationType::LeaderBlockCommit(opdata)) = op {
            Ok(Some(opdata))
        } else {
            test_debug!("No block-commit tx {}", &txid);
            Ok(None)
        }
    }

    pub fn get_commit_in_block_at(
        conn: &DBConn,
        header_hash: &BurnchainHeaderHash,
        block_ptr: u32,
        vtxindex: u16,
    ) -> Result<Option<LeaderBlockCommitOp>, DBError> {
        let qry = "SELECT txid FROM block_commit_metadata WHERE block_height = ?1 AND vtxindex = ?2 AND burn_block_hash = ?3";
        let args: &[&dyn ToSql] = &[&block_ptr, &vtxindex, &header_hash];
        let txid = match query_row(&conn, qry, args) {
            Ok(Some(txid)) => txid,
            Ok(None) => {
                test_debug!(
                    "No block-commit metadata at block {}: {},{}",
                    &header_hash,
                    &block_ptr,
                    &vtxindex
                );
                return Ok(None);
            }
            Err(e) => {
                debug!(
                    "BurnchainDB Error {:?} finding PoX affirmation at {},{} in {:?}",
                    e, block_ptr, vtxindex, &header_hash
                );
                return Ok(None);
            }
        };

        BurnchainDB::get_block_commit(conn, &txid)
    }

    pub fn get_commit_at<B: BurnchainHeaderReader>(
        conn: &DBConn,
        indexer: &B,
        block_ptr: u32,
        vtxindex: u16,
    ) -> Result<Option<LeaderBlockCommitOp>, DBError> {
        let header_hash = match indexer.read_burnchain_header(block_ptr as u64)? {
            Some(hdr) => hdr.block_hash,
            None => {
                test_debug!("No headers at height {}", block_ptr);
                return Ok(None);
            }
        };

        BurnchainDB::get_commit_in_block_at(conn, &header_hash, block_ptr, vtxindex)
    }

    pub fn get_commit_metadata(
        conn: &DBConn,
        burn_block_hash: &BurnchainHeaderHash,
        txid: &Txid,
    ) -> Result<Option<BlockCommitMetadata>, DBError> {
        let args: &[&dyn ToSql] = &[burn_block_hash, txid];
        query_row_panic(
            conn,
            "SELECT * FROM block_commit_metadata WHERE burn_block_hash = ?1 AND txid = ?2",
            args,
            || {
                format!(
                    "BUG: more than one block-commit {},{}",
                    burn_block_hash, txid
                )
            },
        )
    }

    pub fn get_commit_metadata_at<B: BurnchainHeaderReader>(
        conn: &DBConn,
        indexer: &B,
        block_ptr: u32,
        vtxindex: u16,
    ) -> Result<Option<BlockCommitMetadata>, DBError> {
        let header_hash = match indexer.read_burnchain_header(block_ptr as u64)? {
            Some(hdr) => hdr.block_hash,
            None => {
                test_debug!("No headers at height {}", block_ptr);
                return Ok(None);
            }
        };

        let commit = BurnchainDB::get_commit_in_block_at(conn, &header_hash, block_ptr, vtxindex)?
            .expect(&format!(
                "BUG: no metadata for stored block-commit {},{},{})",
                &header_hash, block_ptr, vtxindex
            ));

        BurnchainDB::get_commit_metadata(conn, &header_hash, &commit.txid)
    }

    /// Get the block-commit and block metadata for the anchor block with the heaviest affirmation
    /// weight.
    pub fn get_heaviest_anchor_block(
        conn: &DBConn,
    ) -> Result<Option<(LeaderBlockCommitOp, BlockCommitMetadata)>, DBError> {
        match query_row::<BlockCommitMetadata, _>(
                        conn, "SELECT block_commit_metadata.* \
                               FROM affirmation_maps JOIN block_commit_metadata ON affirmation_maps.affirmation_id = block_commit_metadata.affirmation_id \
                               WHERE block_commit_metadata.anchor_block IS NOT NULL \
                               ORDER BY affirmation_maps.weight DESC, block_commit_metadata.anchor_block DESC",
                        NO_PARAMS
        )? {
            Some(metadata) => {
                let commit = BurnchainDB::get_block_commit(conn, &metadata.txid)?
                    .expect("BUG: no block commit for existing metadata");

                Ok(Some((commit, metadata)))
            }
            None => {
                test_debug!("No anchor block affirmations maps");
                Ok(None)
            }
        }
    }

    /// Find the affirmation map of the anchor block whose affirmation map is the heaviest.
    /// In the event of a tie, pick the one from the anchor block of the latest reward cycle.
    pub fn get_heaviest_anchor_block_affirmation_map(
        conn: &DBConn,
        burnchain: &Burnchain,
    ) -> Result<AffirmationMap, DBError> {
        match BurnchainDB::get_heaviest_anchor_block(conn)? {
            Some((_, metadata)) => {
                let last_reward_cycle = burnchain
                    .block_height_to_reward_cycle(metadata.block_height)
                    .unwrap_or(0)
                    + 1;

                // is there an override set for this reward cycle?
                if let Some(am) =
                    BurnchainDB::get_override_affirmation_map(conn, last_reward_cycle)?
                {
                    warn!(
                        "Overriding heaviest affirmation map for reward cycle {} to {}",
                        last_reward_cycle, &am
                    );
                    return Ok(am);
                }

                let am = BurnchainDB::get_affirmation_map(conn, metadata.affirmation_id)?.expect(
                    &format!(
                        "BUG: failed to load affirmation map {}",
                        metadata.affirmation_id
                    ),
                );

                if cfg!(test) {
                    let _weight =
                        BurnchainDB::get_affirmation_weight(conn, metadata.affirmation_id)?.expect(
                            &format!(
                                "BUG: have affirmation map {} but no weight",
                                &metadata.affirmation_id
                            ),
                        );

                    test_debug!(
                        "Heaviest anchor block affirmation map is {:?} (ID {}, weight {})",
                        &am,
                        metadata.affirmation_id,
                        _weight
                    );
                }
                Ok(am)
            }
            None => {
                test_debug!("No anchor block affirmations maps");
                Ok(AffirmationMap::empty())
            }
        }
    }

    /// Load an overridden affirmation map.
    /// You'd only do this in network emergencies, where node operators are expected to declare an
    /// anchor block missing (or present).  Ideally there'd be a smart contract somewhere for this.
    pub fn get_override_affirmation_map(
        conn: &DBConn,
        reward_cycle: u64,
    ) -> Result<Option<AffirmationMap>, DBError> {
        let am_opt: Option<AffirmationMap> = query_row_panic(
            conn,
            "SELECT affirmation_map FROM overrides WHERE reward_cycle = ?1",
            &[&u64_to_sql(reward_cycle)?],
            || format!("BUG: more than one override affirmation map for the same reward cycle"),
        )?;
        if let Some(am) = &am_opt {
            assert_eq!((am.len() + 1) as u64, reward_cycle);
        }
        Ok(am_opt)
    }

    /// Get the canonical affirmation map.  This is the heaviest anchor block affirmation map, but
    /// accounting for any subsequent reward cycles whose anchor blocks either aren't on the
    /// heaviest anchor block affirmation map, or which have no anchor blocks.
    pub fn get_canonical_affirmation_map<F>(
        conn: &DBConn,
        burnchain: &Burnchain,
        mut unconfirmed_oracle: F,
    ) -> Result<AffirmationMap, DBError>
    where
        F: FnMut(LeaderBlockCommitOp, BlockCommitMetadata) -> bool,
    {
        let canonical_tip =
            BurnchainDB::inner_get_canonical_chain_tip(conn).map_err(|e| match e {
                BurnchainError::DBError(dbe) => dbe,
                _ => DBError::Other(format!("Burnchain error: {:?}", &e)),
            })?;

        let last_reward_cycle = burnchain
            .block_height_to_reward_cycle(canonical_tip.block_height)
            .unwrap_or(0)
            + 1;

        // is there an override set for this reward cycle?
        if let Some(am) = BurnchainDB::get_override_affirmation_map(conn, last_reward_cycle)? {
            warn!(
                "Overriding heaviest affirmation map for reward cycle {} to {}",
                last_reward_cycle, &am
            );
            return Ok(am);
        }

        let mut heaviest_am =
            BurnchainDB::get_heaviest_anchor_block_affirmation_map(conn, burnchain)?;
        let start_rc = (heaviest_am.len() as u64) + 1;

        test_debug!(
            "Add reward cycles {}-{} to heaviest anchor block affirmation map {}",
            start_rc,
            last_reward_cycle,
            &heaviest_am
        );
        for rc in start_rc..last_reward_cycle {
            if let Some((commit, metadata)) = BurnchainDB::get_anchor_block_commit(conn, rc)? {
                let present = unconfirmed_oracle(commit, metadata);
                if present {
                    test_debug!("Assume present anchor block at {}", rc);
                    heaviest_am.push(AffirmationMapEntry::PoxAnchorBlockPresent);
                } else {
                    test_debug!("Assume absent anchor block at {}", rc);
                    heaviest_am.push(AffirmationMapEntry::PoxAnchorBlockAbsent);
                }
            } else {
                test_debug!("Assume no anchor block at {}", rc);
                heaviest_am.push(AffirmationMapEntry::Nothing);
            }
        }

        Ok(heaviest_am)
    }
}
