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
use std::fmt;
use std::fs;
use std::io;
use std::io::prelude::*;
use std::path::{Path, PathBuf};

use rusqlite::{types::ToSql, OptionalExtension, Row};

use chainstate::burn::ConsensusHash;
use chainstate::stacks::db::*;
use chainstate::stacks::Error;
use chainstate::stacks::*;
use core::FIRST_BURNCHAIN_CONSENSUS_HASH;
use core::FIRST_STACKS_BLOCK_HASH;
use util::db::Error as db_error;
use util::db::{
    query_count, query_row, query_row_columns, query_row_panic, query_rows, DBConn, FromColumn,
    FromRow,
};
use vm::costs::ExecutionCost;

use crate::types::chainstate::{
    StacksBlockHeader, StacksBlockId, StacksMicroblockHeader, StacksWorkScore,
};

impl FromRow<StacksBlockHeader> for StacksBlockHeader {
    fn from_row<'a>(row: &'a Row) -> Result<StacksBlockHeader, db_error> {
        let version: u8 = row.get_unwrap("version");
        let total_burn_str: String = row.get_unwrap("total_burn");
        let total_work_str: String = row.get_unwrap("total_work");
        let proof: VRFProof = VRFProof::from_column(row, "proof")?;
        let parent_block = BlockHeaderHash::from_column(row, "parent_block")?;
        let parent_microblock = BlockHeaderHash::from_column(row, "parent_microblock")?;
        let parent_microblock_sequence: u16 = row.get_unwrap("parent_microblock_sequence");
        let tx_merkle_root = Sha512Trunc256Sum::from_column(row, "tx_merkle_root")?;
        let state_index_root = TrieHash::from_column(row, "state_index_root")?;
        let microblock_pubkey_hash = Hash160::from_column(row, "microblock_pubkey_hash")?;

        let block_hash = BlockHeaderHash::from_column(row, "block_hash")?;

        let total_burn = total_burn_str
            .parse::<u64>()
            .map_err(|_e| db_error::ParseError)?;
        let total_work = total_work_str
            .parse::<u64>()
            .map_err(|_e| db_error::ParseError)?;

        let header = StacksBlockHeader {
            version,
            total_work: StacksWorkScore {
                burn: total_burn,
                work: total_work,
            },
            proof,
            parent_block,
            parent_microblock,
            parent_microblock_sequence,
            tx_merkle_root,
            state_index_root,
            microblock_pubkey_hash,
        };

        if block_hash != FIRST_STACKS_BLOCK_HASH && header.block_hash() != block_hash {
            return Err(db_error::ParseError);
        }

        Ok(header)
    }
}

impl FromRow<StacksMicroblockHeader> for StacksMicroblockHeader {
    fn from_row<'a>(row: &'a Row) -> Result<StacksMicroblockHeader, db_error> {
        let version: u8 = row.get_unwrap("version");
        let sequence: u16 = row.get_unwrap("sequence");
        let prev_block = BlockHeaderHash::from_column(row, "prev_block")?;
        let tx_merkle_root = Sha512Trunc256Sum::from_column(row, "tx_merkle_root")?;
        let signature = MessageSignature::from_column(row, "signature")?;

        let microblock_hash = BlockHeaderHash::from_column(row, "microblock_hash")?;

        let microblock_header = StacksMicroblockHeader {
            version,
            sequence,
            prev_block,
            tx_merkle_root,
            signature,
        };

        if microblock_hash != microblock_header.block_hash() {
            return Err(db_error::ParseError);
        }

        Ok(microblock_header)
    }
}

impl StacksChainState {
    /// Insert a block header that is paired with an already-existing block commit and snapshot
    pub fn insert_stacks_block_header(
        tx: &mut StacksDBTx,
        parent_id: &StacksBlockId,
        tip_info: &StacksHeaderInfo,
        anchored_block_cost: &ExecutionCost,
    ) -> Result<(), Error> {
        assert_eq!(
            tip_info.block_height,
            tip_info.anchored_header.total_work.work
        );
        assert!(tip_info.burn_header_timestamp < i64::max_value() as u64);

        let header = &tip_info.anchored_header;
        let index_root = &tip_info.index_root;
        let consensus_hash = &tip_info.consensus_hash;
        let burn_header_hash = &tip_info.burn_header_hash;
        let block_height = tip_info.block_height;
        let burn_header_height = tip_info.burn_header_height;
        let burn_header_timestamp = tip_info.burn_header_timestamp;

        let total_work_str = format!("{}", header.total_work.work);
        let total_burn_str = format!("{}", header.total_work.burn);
        let block_size_str = format!("{}", tip_info.anchored_block_size);

        let block_hash = header.block_hash();

        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_hash);

        assert!(block_height < (i64::max_value() as u64));

        let args: &[&dyn ToSql] = &[
            &header.version,
            &total_burn_str,
            &total_work_str,
            &header.proof,
            &header.parent_block,
            &header.parent_microblock,
            &header.parent_microblock_sequence,
            &header.tx_merkle_root,
            &header.state_index_root,
            &header.microblock_pubkey_hash,
            &block_hash,
            &index_block_hash,
            &consensus_hash,
            &burn_header_hash,
            &(burn_header_height as i64),
            &(burn_header_timestamp as i64),
            &(block_height as i64),
            &index_root,
            anchored_block_cost,
            &block_size_str,
            parent_id,
        ];

        tx.execute("INSERT INTO block_headers \
                    (version, \
                    total_burn, \
                    total_work, \
                    proof, \
                    parent_block, \
                    parent_microblock, \
                    parent_microblock_sequence, \
                    tx_merkle_root, \
                    state_index_root, \
                    microblock_pubkey_hash, \
                    block_hash, \
                    index_block_hash, \
                    consensus_hash, \
                    burn_header_hash, \
                    burn_header_height, \
                    burn_header_timestamp, \
                    block_height, \
                    index_root,
                    cost,
                    block_size,
                    parent_block_id) \
                    VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?18, ?19, ?20, ?21)", args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        Ok(())
    }

    pub fn get_stacks_block_anchored_cost(
        conn: &DBConn,
        block: &StacksBlockId,
    ) -> Result<Option<ExecutionCost>, Error> {
        let qry = "SELECT cost FROM block_headers WHERE index_block_hash = ?";
        conn.query_row(qry, &[block], |row| row.get(0))
            .optional()
            .map_err(|e| Error::from(db_error::from(e)))
    }

    pub fn is_stacks_block_processed(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<bool, Error> {
        let sql = "SELECT 1 FROM block_headers WHERE consensus_hash = ?1 AND block_hash = ?2";
        let args: &[&dyn ToSql] = &[&consensus_hash, &block_hash];
        match conn.query_row(sql, args, |_| Ok(true)) {
            Ok(_) => Ok(true),
            Err(rusqlite::Error::QueryReturnedNoRows) => Ok(false),
            Err(e) => Err(Error::DBError(e.into())),
        }
    }

    /// Get a stacks header info by burn block and block hash (i.e. by primary key).
    /// Does not get back data about the parent microblock stream.
    pub fn get_anchored_block_header_info(
        conn: &Connection,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<StacksHeaderInfo>, Error> {
        let sql = "SELECT * FROM block_headers WHERE consensus_hash = ?1 AND block_hash = ?2";
        let args: &[&dyn ToSql] = &[&consensus_hash, &block_hash];
        query_row_panic(conn, sql, args, || {
            "FATAL: multiple rows for the same block hash".to_string()
        })
        .map_err(Error::DBError)
    }

    /// Get a stacks header info by index block hash (i.e. by the hash of the burn block header
    /// hash and the block hash -- the hash of the primary key)
    pub fn get_stacks_block_header_info_by_index_block_hash(
        conn: &Connection,
        index_block_hash: &StacksBlockId,
    ) -> Result<Option<StacksHeaderInfo>, Error> {
        let sql = "SELECT * FROM block_headers WHERE index_block_hash = ?1";
        query_row_panic(conn, sql, &[&index_block_hash], || {
            "FATAL: multiple rows for the same block hash".to_string()
        })
        .map_err(Error::DBError)
    }

    /// Get an ancestor block header
    pub fn get_tip_ancestor(
        tx: &mut StacksDBTx,
        tip: &StacksHeaderInfo,
        height: u64,
    ) -> Result<Option<StacksHeaderInfo>, Error> {
        assert!(tip.block_height >= height);
        StacksChainState::get_index_tip_ancestor(tx, &tip.index_block_hash(), height)
    }

    /// Get an ancestor block header given an index hash
    pub fn get_index_tip_ancestor(
        tx: &mut StacksDBTx,
        tip_index_hash: &StacksBlockId,
        height: u64,
    ) -> Result<Option<StacksHeaderInfo>, Error> {
        match tx
            .get_ancestor_block_hash(height, tip_index_hash)
            .map_err(Error::DBError)?
        {
            Some(bhh) => {
                StacksChainState::get_stacks_block_header_info_by_index_block_hash(tx, &bhh)
            }
            None => Ok(None),
        }
    }

    /// Get a segment of headers from the canonical chain
    pub fn get_ancestors_headers(
        conn: &Connection,
        upper_bound_header: StacksHeaderInfo,
        lower_bound_height: u64,
    ) -> Result<Vec<StacksHeaderInfo>, Error> {
        let mut ancestors = vec![];
        let mut ancestry_cursor = Some(upper_bound_header);
        while let Some(cursor) = ancestry_cursor.take() {
            if cursor.block_height < lower_bound_height {
                break;
            }
            let block_id = cursor.index_block_hash();
            ancestors.push(cursor.clone());
            let parent_block_id = StacksChainState::get_parent_block_id(conn, &block_id)?;
            if let Some(parent_block_id) = parent_block_id {
                ancestry_cursor =
                    StacksChainState::get_stacks_block_header_info_by_index_block_hash(
                        conn,
                        &parent_block_id,
                    )?;
            } else {
                ancestry_cursor = None;
            }
        }
        Ok(ancestors)
    }

    /// Get the genesis (boot code) block header
    pub fn get_genesis_header_info(conn: &Connection) -> Result<StacksHeaderInfo, Error> {
        // by construction, only one block can have height 0 in this DB
        let sql = "SELECT * FROM block_headers WHERE consensus_hash = ?1 AND block_height = 0";
        let args: &[&dyn ToSql] = &[&FIRST_BURNCHAIN_CONSENSUS_HASH];
        let row_opt = query_row(conn, sql, args)?;
        Ok(row_opt.expect("BUG: no genesis header info"))
    }

    /// Get the parent block ID for this block
    pub fn get_parent_block_id(
        conn: &Connection,
        block_id: &StacksBlockId,
    ) -> Result<Option<StacksBlockId>, Error> {
        let sql = "SELECT parent_block_id FROM block_headers WHERE index_block_hash = ?1 LIMIT 1";
        let args: &[&dyn ToSql] = &[block_id];
        let mut rows = query_row_columns::<StacksBlockId, _>(conn, sql, args, "parent_block_id")?;
        Ok(rows.pop())
    }

    /// Is this block present and processed?
    pub fn has_stacks_block(conn: &Connection, block_id: &StacksBlockId) -> Result<bool, Error> {
        let sql = "SELECT 1 FROM block_headers WHERE index_block_hash = ?1 LIMIT 1";
        let args: &[&dyn ToSql] = &[block_id];
        Ok(conn
            .query_row(sql, args, |_r| Ok(()))
            .optional()
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?
            .is_some())
    }
}
