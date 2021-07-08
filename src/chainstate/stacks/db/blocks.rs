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
use std::collections::{HashMap, HashSet};
use std::convert::From;
use std::fmt;
use std::fs;
use std::io;
use std::io::prelude::*;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use rand::thread_rng;
use rand::Rng;
use rand::RngCore;
use rusqlite::Connection;
use rusqlite::DatabaseName;
use rusqlite::{Error as sqlite_error, OptionalExtension};

use crate::codec::MAX_MESSAGE_LEN;
use chainstate::burn::db::sortdb::*;
use chainstate::burn::operations::*;
use chainstate::burn::BlockSnapshot;
use chainstate::stacks::db::accounts::MinerReward;
use chainstate::stacks::db::transactions::TransactionNonceMismatch;
use chainstate::stacks::db::*;
use chainstate::stacks::index::MarfTrieId;
use chainstate::stacks::Error;
use chainstate::stacks::*;
use chainstate::stacks::{
    C32_ADDRESS_VERSION_MAINNET_MULTISIG, C32_ADDRESS_VERSION_MAINNET_SINGLESIG,
    C32_ADDRESS_VERSION_TESTNET_MULTISIG, C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
};
use clarity_vm::clarity::{ClarityBlockConnection, ClarityConnection, ClarityInstance};
use core::mempool::MAXIMUM_MEMPOOL_TX_CHAINING;
use core::*;
use net::BlocksInvData;
use net::Error as net_error;
use util::db::u64_to_sql;
use util::db::Error as db_error;
use util::db::{
    query_count, query_int, query_row, query_row_columns, query_row_panic, query_rows,
    tx_busy_handler, DBConn, FromColumn, FromRow,
};
use util::get_epoch_time_ms;
use util::get_epoch_time_secs;
use util::hash::to_hex;
use util::retry::BoundReader;
use util::strings::StacksString;
pub use vm::analysis::errors::{CheckError, CheckErrors};
use vm::analysis::run_analysis;
use vm::ast::build_ast;
use vm::contexts::AssetMap;
use vm::contracts::Contract;
use vm::costs::LimitedCostTracker;
use vm::database::{BurnStateDB, ClarityDatabase, NULL_BURN_STATE_DB, NULL_HEADER_DB};
use vm::types::{
    AssetIdentifier, BuffData, PrincipalData, QualifiedContractIdentifier, SequenceData,
    StandardPrincipalData, TupleData, TypeSignature, Value,
};

use crate::types::chainstate::{
    StacksAddress, StacksBlockHeader, StacksBlockId, StacksMicroblockHeader,
};
use crate::{types, util};
use types::chainstate::BurnchainHeaderHash;

#[derive(Debug, Clone, PartialEq)]
pub struct StagingMicroblock {
    pub consensus_hash: ConsensusHash,
    pub anchored_block_hash: BlockHeaderHash,
    pub microblock_hash: BlockHeaderHash,
    pub parent_hash: BlockHeaderHash,
    pub sequence: u16,
    pub processed: bool,
    pub orphaned: bool,
    pub block_data: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StagingBlock {
    pub consensus_hash: ConsensusHash,
    pub anchored_block_hash: BlockHeaderHash,
    pub parent_consensus_hash: ConsensusHash,
    pub parent_anchored_block_hash: BlockHeaderHash,
    pub parent_microblock_hash: BlockHeaderHash,
    pub parent_microblock_seq: u16,
    pub microblock_pubkey_hash: Hash160,
    pub height: u64,
    pub processed: bool,
    pub attachable: bool,
    pub orphaned: bool,
    pub commit_burn: u64,
    pub sortition_burn: u64,
    pub block_data: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StagingUserBurnSupport {
    pub consensus_hash: ConsensusHash,
    pub anchored_block_hash: BlockHeaderHash,
    pub address: StacksAddress,
    pub burn_amount: u64,
    pub vtxindex: u32,
}

#[derive(Debug)]
pub enum MemPoolRejection {
    SerializationFailure(codec_error),
    DeserializationFailure(codec_error),
    FailedToValidate(Error),
    FeeTooLow(u64, u64),
    BadNonces(TransactionNonceMismatch),
    NotEnoughFunds(u128, u128),
    NoSuchContract,
    NoSuchPublicFunction,
    BadFunctionArgument(CheckError),
    ContractAlreadyExists(QualifiedContractIdentifier),
    PoisonMicroblocksDoNotConflict,
    NoAnchorBlockWithPubkeyHash(Hash160),
    InvalidMicroblocks,
    BadAddressVersionByte,
    NoCoinbaseViaMempool,
    NoSuchChainTip(ConsensusHash, BlockHeaderHash),
    ConflictingNonceInMempool,
    TooMuchChaining {
        max_nonce: u64,
        actual_nonce: u64,
        principal: PrincipalData,
        is_origin: bool,
    },
    BadTransactionVersion,
    TransferRecipientIsSender(PrincipalData),
    TransferAmountMustBePositive,
    DBError(db_error),
    Other(String),
}

impl MemPoolRejection {
    pub fn into_json(self, txid: &Txid) -> serde_json::Value {
        use self::MemPoolRejection::*;
        let (reason_code, reason_data) = match self {
            SerializationFailure(e) => ("Serialization", Some(json!({"message": e.to_string()}))),
            DeserializationFailure(e) => {
                ("Deserialization", Some(json!({"message": e.to_string()})))
            }
            TooMuchChaining {
                max_nonce,
                actual_nonce,
                principal,
                is_origin,
                ..
            } => (
                "TooMuchChaining",
                Some(
                    json!({"message": "Nonce would exceed chaining limit in mempool",
                                "expected": max_nonce,
                                "actual": actual_nonce,
                                "principal": principal.to_string(),
                                "is_origin": is_origin
                    }),
                ),
            ),
            BadTransactionVersion => ("BadTransactionVersion", None),
            FailedToValidate(e) => (
                "SignatureValidation",
                Some(json!({"message": e.to_string()})),
            ),
            FeeTooLow(actual, expected) => (
                "FeeTooLow",
                Some(json!({
                                                "expected": expected,
                                                "actual": actual})),
            ),
            TransferRecipientIsSender(recipient) => (
                "TransferRecipientCannotEqualSender",
                Some(json!({"recipient": recipient.to_string()})),
            ),
            TransferAmountMustBePositive => ("TransferAmountMustBePositive", None),
            BadNonces(TransactionNonceMismatch {
                expected,
                actual,
                principal,
                is_origin,
                ..
            }) => (
                "BadNonce",
                Some(json!({
                     "expected": expected,
                     "actual": actual,
                     "principal": principal.to_string(),
                     "is_origin": is_origin})),
            ),
            NotEnoughFunds(expected, actual) => (
                "NotEnoughFunds",
                Some(json!({
                    "expected": format!("0x{}", to_hex(&expected.to_be_bytes())),
                    "actual": format!("0x{}", to_hex(&actual.to_be_bytes()))
                })),
            ),
            NoSuchContract => ("NoSuchContract", None),
            NoSuchPublicFunction => ("NoSuchPublicFunction", None),
            BadFunctionArgument(e) => (
                "BadFunctionArgument",
                Some(json!({"message": e.to_string()})),
            ),
            ConflictingNonceInMempool => ("ConflictingNonceInMempool", None),
            ContractAlreadyExists(id) => (
                "ContractAlreadyExists",
                Some(json!({ "contract_identifier": id.to_string() })),
            ),
            PoisonMicroblocksDoNotConflict => ("PoisonMicroblocksDoNotConflict", None),
            NoAnchorBlockWithPubkeyHash(_h) => ("PoisonMicroblockHasUnknownPubKeyHash", None),
            InvalidMicroblocks => ("PoisonMicroblockIsInvalid", None),
            BadAddressVersionByte => ("BadAddressVersionByte", None),
            NoCoinbaseViaMempool => ("NoCoinbaseViaMempool", None),
            // this should never happen via the RPC interface
            NoSuchChainTip(..) => ("ServerFailureNoSuchChainTip", None),
            DBError(e) => (
                "ServerFailureDatabase",
                Some(json!({"message": e.to_string()})),
            ),
            Other(s) => ("ServerFailureOther", Some(json!({ "message": s }))),
        };
        let mut result = json!({
            "txid": format!("{}", txid.to_hex()),
            "error": "transaction rejected",
            "reason": reason_code,
        });
        if let Some(reason_data) = reason_data {
            result
                .as_object_mut()
                .unwrap()
                .insert("reason_data".to_string(), reason_data);
        }
        result
    }
}

impl From<db_error> for MemPoolRejection {
    fn from(e: db_error) -> MemPoolRejection {
        MemPoolRejection::DBError(e)
    }
}

// These constants are mempool acceptance heuristics, but
//  not part of the protocol consensus (i.e., a block
//  that includes a transaction that violates these won't
//  be invalid)
pub const MINIMUM_TX_FEE: u64 = 1;
pub const MINIMUM_TX_FEE_RATE_PER_BYTE: u64 = 1;

impl StagingBlock {
    pub fn is_first_mined(&self) -> bool {
        self.parent_anchored_block_hash == FIRST_STACKS_BLOCK_HASH
    }
}

impl FromRow<StagingMicroblock> for StagingMicroblock {
    fn from_row<'a>(row: &'a Row) -> Result<StagingMicroblock, db_error> {
        let anchored_block_hash: BlockHeaderHash =
            BlockHeaderHash::from_column(row, "anchored_block_hash")?;
        let consensus_hash: ConsensusHash = ConsensusHash::from_column(row, "consensus_hash")?;
        let microblock_hash: BlockHeaderHash =
            BlockHeaderHash::from_column(row, "microblock_hash")?;
        let parent_hash: BlockHeaderHash = BlockHeaderHash::from_column(row, "parent_hash")?;
        let sequence: u16 = row.get_unwrap("sequence");
        let processed_i64: i64 = row.get_unwrap("processed");
        let orphaned_i64: i64 = row.get_unwrap("orphaned");
        let block_data: Vec<u8> = vec![];

        let processed = processed_i64 != 0;
        let orphaned = orphaned_i64 != 0;

        Ok(StagingMicroblock {
            consensus_hash,
            anchored_block_hash,
            microblock_hash,
            parent_hash,
            sequence,
            processed,
            orphaned,
            block_data,
        })
    }
}

impl FromRow<StagingBlock> for StagingBlock {
    fn from_row<'a>(row: &'a Row) -> Result<StagingBlock, db_error> {
        let anchored_block_hash: BlockHeaderHash =
            BlockHeaderHash::from_column(row, "anchored_block_hash")?;
        let parent_anchored_block_hash: BlockHeaderHash =
            BlockHeaderHash::from_column(row, "parent_anchored_block_hash")?;
        let consensus_hash: ConsensusHash = ConsensusHash::from_column(row, "consensus_hash")?;
        let parent_consensus_hash: ConsensusHash =
            ConsensusHash::from_column(row, "parent_consensus_hash")?;
        let parent_microblock_hash: BlockHeaderHash =
            BlockHeaderHash::from_column(row, "parent_microblock_hash")?;
        let parent_microblock_seq: u16 = row.get_unwrap("parent_microblock_seq");
        let microblock_pubkey_hash: Hash160 = Hash160::from_column(row, "microblock_pubkey_hash")?;
        let height = u64::from_column(row, "height")?;
        let attachable_i64: i64 = row.get_unwrap("attachable");
        let processed_i64: i64 = row.get_unwrap("processed");
        let orphaned_i64: i64 = row.get_unwrap("orphaned");
        let commit_burn = u64::from_column(row, "commit_burn")?;
        let sortition_burn = u64::from_column(row, "sortition_burn")?;
        let block_data: Vec<u8> = vec![];

        let processed = processed_i64 != 0;
        let attachable = attachable_i64 != 0;
        let orphaned = orphaned_i64 != 0;

        Ok(StagingBlock {
            anchored_block_hash,
            parent_anchored_block_hash,
            consensus_hash,
            parent_consensus_hash,
            parent_microblock_hash,
            parent_microblock_seq,
            microblock_pubkey_hash,
            height,
            processed,
            attachable,
            orphaned,
            commit_burn,
            sortition_burn,
            block_data,
        })
    }
}

impl FromRow<StagingUserBurnSupport> for StagingUserBurnSupport {
    fn from_row<'a>(row: &'a Row) -> Result<StagingUserBurnSupport, db_error> {
        let anchored_block_hash: BlockHeaderHash =
            BlockHeaderHash::from_column(row, "anchored_block_hash")?;
        let consensus_hash: ConsensusHash = ConsensusHash::from_column(row, "consensus_hash")?;
        let address: StacksAddress = StacksAddress::from_column(row, "address")?;
        let burn_amount = u64::from_column(row, "burn_amount")?;
        let vtxindex: u32 = row.get_unwrap("vtxindex");

        Ok(StagingUserBurnSupport {
            anchored_block_hash,
            consensus_hash,
            address,
            burn_amount,
            vtxindex,
        })
    }
}

impl StagingMicroblock {
    #[cfg(test)]
    pub fn try_into_microblock(self) -> Result<StacksMicroblock, StagingMicroblock> {
        StacksMicroblock::consensus_deserialize(&mut &self.block_data[..]).map_err(|_e| self)
    }
}

impl BlockStreamData {
    pub fn new_block(index_block_hash: StacksBlockId) -> BlockStreamData {
        BlockStreamData {
            index_block_hash: index_block_hash,
            rowid: None,
            offset: 0,
            total_bytes: 0,

            is_microblock: false,
            microblock_hash: BlockHeaderHash([0u8; 32]),
            parent_index_block_hash: StacksBlockId([0u8; 32]),
            seq: 0,
            unconfirmed: false,
            num_mblocks_buf: [0u8; 4],
            num_mblocks_ptr: 0,
        }
    }

    pub fn new_microblock_confirmed(
        chainstate: &StacksChainState,
        tail_index_microblock_hash: StacksBlockId,
    ) -> Result<BlockStreamData, Error> {
        // look up parent
        let mblock_info = StacksChainState::load_staging_microblock_info_indexed(
            &chainstate.db(),
            &tail_index_microblock_hash,
        )?
        .ok_or(Error::NoSuchBlockError)?;

        let parent_index_block_hash = StacksBlockHeader::make_index_block_hash(
            &mblock_info.consensus_hash,
            &mblock_info.anchored_block_hash,
        );

        // need to send out the consensus_serialize()'ed array length before sending microblocks.
        // this is exactly what seq tells us, though.
        let num_mblocks_buf = ((mblock_info.sequence as u32) + 1).to_be_bytes();

        Ok(BlockStreamData {
            index_block_hash: StacksBlockId([0u8; 32]),
            rowid: None,
            offset: 0,
            total_bytes: 0,

            is_microblock: true,
            microblock_hash: mblock_info.microblock_hash,
            parent_index_block_hash: parent_index_block_hash,
            seq: mblock_info.sequence,
            unconfirmed: false,
            num_mblocks_buf: num_mblocks_buf,
            num_mblocks_ptr: 0,
        })
    }

    pub fn new_microblock_unconfirmed(
        chainstate: &StacksChainState,
        anchored_index_block_hash: StacksBlockId,
        seq: u16,
    ) -> Result<BlockStreamData, Error> {
        let mblock_info = StacksChainState::load_next_descendant_microblock(
            &chainstate.db(),
            &anchored_index_block_hash,
            seq,
        )?
        .ok_or(Error::NoSuchBlockError)?;

        Ok(BlockStreamData {
            index_block_hash: anchored_index_block_hash.clone(),
            rowid: None,
            offset: 0,
            total_bytes: 0,

            is_microblock: true,
            microblock_hash: mblock_info.block_hash(),
            parent_index_block_hash: anchored_index_block_hash,
            seq: seq,
            unconfirmed: true,
            num_mblocks_buf: [0u8; 4],
            num_mblocks_ptr: 4, // stops us from trying to send a length prefix
        })
    }

    pub fn stream_to<W: Write>(
        &mut self,
        chainstate: &mut StacksChainState,
        fd: &mut W,
        count: u64,
    ) -> Result<u64, Error> {
        if self.is_microblock {
            let mut num_written = 0;
            if !self.unconfirmed {
                // Confirmed microblocks are represented as a consensus-encoded vector of
                // microblocks, in reverse sequence order.
                // Write 4-byte length prefix first
                while self.num_mblocks_ptr < self.num_mblocks_buf.len() {
                    // stream length prefix
                    test_debug!(
                        "Confirmed microblock stream for {}: try to send length prefix {:?} (ptr={})",
                        &self.microblock_hash,
                        &self.num_mblocks_buf[self.num_mblocks_ptr..],
                        self.num_mblocks_ptr
                    );
                    let num_sent = match fd.write(&self.num_mblocks_buf[self.num_mblocks_ptr..]) {
                        Ok(0) => {
                            // done (disconnected)
                            test_debug!(
                                "Confirmed microblock stream for {}: wrote 0 bytes",
                                &self.microblock_hash
                            );
                            return Ok(num_written);
                        }
                        Ok(n) => {
                            self.num_mblocks_ptr += n;
                            n as u64
                        }
                        Err(e) => {
                            if e.kind() == io::ErrorKind::Interrupted {
                                // EINTR; try again
                                continue;
                            } else if e.kind() == io::ErrorKind::WouldBlock
                                || (cfg!(windows) && e.kind() == io::ErrorKind::TimedOut)
                            {
                                // blocked
                                return Ok(num_written);
                            } else {
                                return Err(Error::WriteError(e));
                            }
                        }
                    };
                    num_written += num_sent;
                    test_debug!(
                        "Confirmed microblock stream for {}: sent {} bytes ({} total)",
                        &self.microblock_hash,
                        num_sent,
                        num_written
                    );
                }
                StacksChainState::stream_microblocks_confirmed(&chainstate, fd, self, count)
                    .and_then(|bytes_sent| Ok(bytes_sent + num_written))
            } else {
                StacksChainState::stream_microblocks_unconfirmed(&chainstate, fd, self, count)
                    .and_then(|bytes_sent| Ok(bytes_sent + num_written))
            }
        } else {
            chainstate.stream_block(fd, self, count)
        }
    }
}

impl StacksChainState {
    fn get_index_block_pathbuf(blocks_dir: &str, index_block_hash: &StacksBlockId) -> PathBuf {
        let block_hash_bytes = index_block_hash.as_bytes();
        let mut block_path = PathBuf::from(blocks_dir);

        block_path.push(to_hex(&block_hash_bytes[0..2]));
        block_path.push(to_hex(&block_hash_bytes[2..4]));
        block_path.push(format!("{}", index_block_hash));

        block_path
    }

    /// Get the path to a block in the chunk store
    pub fn get_index_block_path(
        blocks_dir: &str,
        index_block_hash: &StacksBlockId,
    ) -> Result<String, Error> {
        let block_path = StacksChainState::get_index_block_pathbuf(blocks_dir, index_block_hash);

        let blocks_path_str = block_path
            .to_str()
            .ok_or_else(|| Error::DBError(db_error::ParseError))?
            .to_string();
        Ok(blocks_path_str)
    }

    /// Get the path to a block in the chunk store, given the burn header hash and block hash.
    pub fn get_block_path(
        blocks_dir: &str,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<String, Error> {
        let index_block_hash = StacksBlockHeader::make_index_block_hash(consensus_hash, block_hash);
        StacksChainState::get_index_block_path(blocks_dir, &index_block_hash)
    }

    /// Make a directory tree for storing this block to the chunk store, and return the block's path
    fn make_block_dir(
        blocks_dir: &str,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<String, Error> {
        let index_block_hash = StacksBlockHeader::make_index_block_hash(consensus_hash, block_hash);
        let block_hash_bytes = index_block_hash.as_bytes();
        let mut block_path = PathBuf::from(blocks_dir);

        block_path.push(to_hex(&block_hash_bytes[0..2]));
        block_path.push(to_hex(&block_hash_bytes[2..4]));

        let _ = StacksChainState::mkdirs(&block_path)?;

        block_path.push(format!("{}", to_hex(block_hash_bytes)));
        let blocks_path_str = block_path
            .to_str()
            .ok_or_else(|| Error::DBError(db_error::ParseError))?
            .to_string();
        Ok(blocks_path_str)
    }

    pub fn atomic_file_store<F>(
        path: &String,
        delete_on_error: bool,
        mut writer: F,
    ) -> Result<(), Error>
    where
        F: FnMut(&mut fs::File) -> Result<(), Error>,
    {
        let path_tmp = format!("{}.tmp", path);
        let mut fd = fs::OpenOptions::new()
            .read(false)
            .write(true)
            .create(true)
            .truncate(true)
            .open(&path_tmp)
            .map_err(|e| {
                if e.kind() == io::ErrorKind::NotFound {
                    error!("File not found: {:?}", &path_tmp);
                    Error::DBError(db_error::NotFoundError)
                } else {
                    error!("Failed to open {:?}: {:?}", &path_tmp, &e);
                    Error::DBError(db_error::IOError(e))
                }
            })?;

        writer(&mut fd).map_err(|e| {
            if delete_on_error {
                // abort
                let _ = fs::remove_file(&path_tmp);
            }
            e
        })?;

        fd.sync_all()
            .map_err(|e| Error::DBError(db_error::IOError(e)))?;

        // atomically put this file in place
        // TODO: this is atomic but not crash-consistent!  need to fsync the dir as well
        trace!("Rename {:?} to {:?}", &path_tmp, &path);
        fs::rename(&path_tmp, &path).map_err(|e| Error::DBError(db_error::IOError(e)))?;

        Ok(())
    }

    pub fn atomic_file_write(path: &String, bytes: &Vec<u8>) -> Result<(), Error> {
        StacksChainState::atomic_file_store(path, false, |ref mut fd| {
            fd.write_all(bytes)
                .map_err(|e| Error::DBError(db_error::IOError(e)))
        })
    }

    pub fn get_file_size(path: &String) -> Result<u64, Error> {
        let sz = match fs::metadata(path) {
            Ok(md) => md.len(),
            Err(e) => {
                if e.kind() == io::ErrorKind::NotFound {
                    return Err(Error::DBError(db_error::NotFoundError));
                } else {
                    error!("Failed to stat {:?}: {:?}", &path, &e);
                    return Err(Error::DBError(db_error::IOError(e)));
                }
            }
        };
        Ok(sz)
    }

    pub fn consensus_load<T: StacksMessageCodec>(path: &String) -> Result<T, Error> {
        let mut fd = fs::OpenOptions::new()
            .read(true)
            .write(false)
            .open(path)
            .map_err(|e| {
                if e.kind() == io::ErrorKind::NotFound {
                    Error::DBError(db_error::NotFoundError)
                } else {
                    Error::DBError(db_error::IOError(e))
                }
            })?;

        let mut bound_reader = BoundReader::from_reader(&mut fd, MAX_MESSAGE_LEN as u64);
        let inst = T::consensus_deserialize(&mut bound_reader).map_err(Error::CodecError)?;
        Ok(inst)
    }

    /// Do we have a stored a block in the chunk store?
    /// Will be true even if it's invalid.
    pub fn has_block_indexed(
        blocks_dir: &String,
        index_block_hash: &StacksBlockId,
    ) -> Result<bool, Error> {
        let block_path = StacksChainState::get_index_block_path(blocks_dir, index_block_hash)?;
        match fs::metadata(block_path) {
            Ok(_) => Ok(true),
            Err(e) => {
                if e.kind() == io::ErrorKind::NotFound {
                    Ok(false)
                } else {
                    Err(Error::DBError(db_error::IOError(e)))
                }
            }
        }
    }

    /// Do we have a stored a block in the chunk store?
    /// Will be true only if it's also valid (i.e. non-zero sized)
    pub fn has_valid_block_indexed(
        blocks_dir: &String,
        index_block_hash: &StacksBlockId,
    ) -> Result<bool, Error> {
        let block_path = StacksChainState::get_index_block_path(blocks_dir, index_block_hash)?;
        match fs::metadata(block_path) {
            Ok(md) => Ok(md.len() > 0),
            Err(e) => {
                if e.kind() == io::ErrorKind::NotFound {
                    Ok(false)
                } else {
                    Err(Error::DBError(db_error::IOError(e)))
                }
            }
        }
    }

    /// Have we processed and stored a particular block?
    pub fn has_stored_block(
        blocks_db: &DBConn,
        blocks_dir: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<bool, Error> {
        let staging_status_opt =
            StacksChainState::get_staging_block_status(blocks_db, consensus_hash, block_hash)?
                .map(|processed| !processed);

        match staging_status_opt {
            Some(staging_status) => {
                let index_block_hash =
                    StacksBlockHeader::make_index_block_hash(consensus_hash, block_hash);
                if staging_status {
                    // not processed yet
                    test_debug!(
                        "Block {}/{} ({}) is staging",
                        consensus_hash,
                        block_hash,
                        &index_block_hash
                    );
                    Ok(false)
                } else {
                    // have a row in the DB at least.
                    // only accepted if we stored it
                    StacksChainState::has_block_indexed(blocks_dir, &index_block_hash)
                }
            }
            None => {
                // no row in the DB, so not processed at all.
                Ok(false)
            }
        }
    }

    /// Store a block to the chunk store, named by its hash
    pub fn store_block(
        blocks_dir: &String,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
    ) -> Result<(), Error> {
        let block_hash = block.block_hash();
        let block_path = StacksChainState::make_block_dir(blocks_dir, consensus_hash, &block_hash)?;

        test_debug!(
            "Store {}/{} to {}",
            consensus_hash,
            &block_hash,
            &block_path
        );
        StacksChainState::atomic_file_store(&block_path, true, |ref mut fd| {
            block.consensus_serialize(fd).map_err(Error::CodecError)
        })
    }

    /// Store an empty block to the chunk store, named by its hash.
    #[cfg(test)]
    fn store_empty_block(
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<(), Error> {
        let block_path =
            StacksChainState::make_block_dir(blocks_path, consensus_hash, &block_hash)?;
        StacksChainState::atomic_file_write(&block_path, &vec![])
    }

    /// Mark a block in the filesystem as invalid
    fn free_block(
        blocks_dir: &str,
        consensus_hash: &ConsensusHash,
        block_header_hash: &BlockHeaderHash,
    ) -> () {
        let block_path =
            StacksChainState::make_block_dir(blocks_dir, consensus_hash, &block_header_hash)
                .expect("FATAL: failed to create block directory");

        let sz = fs::metadata(&block_path)
            .expect(&format!("FATAL: failed to stat '{}'", &block_path))
            .len();

        if sz > 0 {
            // try make this thread-safe. It's okay if this block gets copied more than once; we
            // only care that at least one copy survives for further analysis.
            let random_bytes = thread_rng().gen::<[u8; 8]>();
            let random_bytes_str = to_hex(&random_bytes);
            let index_block_hash = StacksBlockId::new(consensus_hash, block_header_hash);
            let mut invalid_path =
                StacksChainState::get_index_block_pathbuf(blocks_dir, &index_block_hash);
            invalid_path
                .file_name()
                .expect("FATAL: index block path did not have file name");
            invalid_path.set_extension(&format!("invalid-{}", &random_bytes_str));

            fs::copy(&block_path, &invalid_path).expect(&format!(
                "FATAL: failed to copy '{}' to '{}'",
                &block_path,
                &invalid_path.to_string_lossy(),
            ));

            // already freed?
            let sz = fs::metadata(&invalid_path)
                .expect(&format!(
                    "FATAL: failed to stat '{}'",
                    &invalid_path.to_string_lossy()
                ))
                .len();

            if sz > 0 {
                // truncate the original
                fs::OpenOptions::new()
                    .read(false)
                    .write(true)
                    .truncate(true)
                    .open(&block_path)
                    .expect(&format!(
                        "FATAL: Failed to mark block path '{}' as free",
                        &block_path
                    ));
            }
        }
    }

    /// Free up all state for an invalid block
    fn free_block_state(
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        block_header: &StacksBlockHeader,
    ) -> () {
        StacksChainState::free_block(blocks_path, consensus_hash, &block_header.block_hash())
    }

    /// Get a list of all anchored blocks' hashes, and their burnchain headers
    pub fn list_blocks(
        blocks_conn: &DBConn,
    ) -> Result<Vec<(ConsensusHash, BlockHeaderHash)>, Error> {
        let list_block_sql = "SELECT * FROM staging_blocks ORDER BY height".to_string();
        let mut blocks = query_rows::<StagingBlock, _>(blocks_conn, &list_block_sql, NO_PARAMS)
            .map_err(Error::DBError)?;

        Ok(blocks
            .drain(..)
            .map(|b| (b.consensus_hash, b.anchored_block_hash))
            .collect())
    }

    /// Get all stacks block headers.  Great for testing!
    pub fn get_all_staging_block_headers(blocks_conn: &DBConn) -> Result<Vec<StagingBlock>, Error> {
        let sql = "SELECT * FROM staging_blocks ORDER BY height".to_string();
        query_rows::<StagingBlock, _>(blocks_conn, &sql, NO_PARAMS).map_err(Error::DBError)
    }

    /// Get a list of all microblocks' hashes, and their anchored blocks' hashes
    #[cfg(test)]
    pub fn list_microblocks(
        blocks_conn: &DBConn,
        blocks_dir: &String,
    ) -> Result<Vec<(ConsensusHash, BlockHeaderHash, Vec<BlockHeaderHash>)>, Error> {
        let mut blocks = StacksChainState::list_blocks(blocks_conn)?;
        let mut ret = vec![];

        for (consensus_hash, block_hash) in blocks.drain(..) {
            let list_microblock_sql = "SELECT * FROM staging_microblocks WHERE anchored_block_hash = ?1 AND consensus_hash = ?2 ORDER BY sequence".to_string();
            let list_microblock_args: [&dyn ToSql; 2] = [&block_hash, &consensus_hash];
            let mut microblocks = query_rows::<StagingMicroblock, _>(
                blocks_conn,
                &list_microblock_sql,
                &list_microblock_args,
            )
            .map_err(Error::DBError)?;

            let microblock_hashes = microblocks.drain(..).map(|mb| mb.microblock_hash).collect();
            ret.push((consensus_hash, block_hash, microblock_hashes));
        }

        Ok(ret)
    }

    /// Load up a blocks' bytes from the chunk store.
    /// Returns Ok(Some(bytes)) on success, if found.
    /// Returns Ok(none) if this block was found, but is known to be invalid
    /// Returns Err(...) on not found or I/O error
    pub fn load_block_bytes(
        blocks_dir: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<Vec<u8>>, Error> {
        let block_path = StacksChainState::get_block_path(blocks_dir, consensus_hash, block_hash)?;
        let sz = StacksChainState::get_file_size(&block_path)?;
        if sz == 0 {
            debug!("Zero-sized block {}", block_hash);
            return Ok(None);
        }
        if sz > MAX_MESSAGE_LEN as u64 {
            debug!("Invalid block {}: too big", block_hash);
            return Ok(None);
        }

        let mut fd = fs::OpenOptions::new()
            .read(true)
            .write(false)
            .open(&block_path)
            .map_err(|e| {
                if e.kind() == io::ErrorKind::NotFound {
                    Error::DBError(db_error::NotFoundError)
                } else {
                    Error::DBError(db_error::IOError(e))
                }
            })?;

        let mut ret = vec![];
        fd.read_to_end(&mut ret)
            .map_err(|e| Error::DBError(db_error::IOError(e)))?;
        Ok(Some(ret))
    }

    /// Load up a block from the chunk store (staging or confirmed)
    /// Returns Ok(Some(block)) if found.
    /// Returns Ok(None) if this block was found, but is known to be invalid
    /// Returns Err(...) on not found or I/O error
    pub fn load_block(
        blocks_dir: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<StacksBlock>, Error> {
        let block_path = StacksChainState::get_block_path(blocks_dir, consensus_hash, block_hash)?;
        let sz = StacksChainState::get_file_size(&block_path)?;
        if sz == 0 {
            debug!("Zero-sized block {}", &block_hash);
            return Ok(None);
        }

        let block: StacksBlock = StacksChainState::consensus_load(&block_path)?;
        Ok(Some(block))
    }

    /// Load up an anchored block header from the chunk store.
    /// Returns Ok(Some(blockheader)) if found.
    /// Returns Ok(None) if this block was found, but is known to be invalid
    /// Returns Err(...) on not found or I/O error
    pub fn load_block_header(
        blocks_dir: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<StacksBlockHeader>, Error> {
        let block_path = StacksChainState::get_block_path(blocks_dir, consensus_hash, block_hash)?;
        let sz = StacksChainState::get_file_size(&block_path)?;
        if sz == 0 {
            debug!("Zero-sized block {}", &block_hash);
            return Ok(None);
        }

        let block_header: StacksBlockHeader = StacksChainState::consensus_load(&block_path)?;
        Ok(Some(block_header))
    }

    /// Closure for defaulting to an empty microblock stream if a microblock stream file is not found
    fn empty_stream(e: Error) -> Result<Option<Vec<StacksMicroblock>>, Error> {
        match e {
            Error::DBError(ref dbe) => match dbe {
                db_error::NotFoundError => Ok(Some(vec![])),
                _ => Err(e),
            },
            _ => Err(e),
        }
    }

    /// Load up a blob of data.
    /// Query should be structured to return rows of BLOBs
    fn load_block_data_blobs<P>(
        conn: &DBConn,
        sql_query: &String,
        sql_args: P,
    ) -> Result<Vec<Vec<u8>>, Error>
    where
        P: IntoIterator,
        P::Item: ToSql,
    {
        let mut stmt = conn
            .prepare(sql_query)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        let mut rows = stmt
            .query(sql_args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        // gather
        let mut blobs = vec![];

        while let Some(row) = rows.next().map_err(|e| db_error::SqliteError(e))? {
            let next_blob: Vec<u8> = row.get_unwrap(0);
            blobs.push(next_blob);
        }

        Ok(blobs)
    }

    /// Load up a staging block or microblock's bytes, given its hash and which table to use
    /// Treat an empty array as None.
    fn inner_load_staging_block_bytes(
        block_conn: &DBConn,
        table: &str,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<Vec<u8>>, Error> {
        let sql = format!("SELECT block_data FROM {} WHERE block_hash = ?1", table);
        let args = [&block_hash];
        let mut blobs = StacksChainState::load_block_data_blobs(block_conn, &sql, &args)?;
        let len = blobs.len();
        match len {
            0 => Ok(None),
            1 => {
                let blob = blobs.pop().unwrap();
                if blob.len() == 0 {
                    // cleared
                    Ok(None)
                } else {
                    Ok(Some(blob))
                }
            }
            _ => {
                unreachable!("Got multiple blocks for the same block hash");
            }
        }
    }

    fn load_staging_microblock_bytes(
        block_conn: &DBConn,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<Vec<u8>>, Error> {
        StacksChainState::inner_load_staging_block_bytes(
            block_conn,
            "staging_microblocks_data",
            block_hash,
        )
    }

    fn has_blocks_with_microblock_pubkh(
        block_conn: &DBConn,
        pubkey_hash: &Hash160,
        minimum_block_height: i64,
    ) -> bool {
        let sql = "SELECT 1 FROM staging_blocks WHERE microblock_pubkey_hash = ?1 AND height >= ?2";
        let args: &[&dyn ToSql] = &[pubkey_hash, &minimum_block_height];
        block_conn
            .query_row(sql, args, |_r| Ok(()))
            .optional()
            .expect("DB CORRUPTION: block header DB corrupted!")
            .is_some()
    }

    /// Load up a preprocessed (queued) but still unprocessed block.
    pub fn load_staging_block(
        block_conn: &DBConn,
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<StagingBlock>, Error> {
        let sql = "SELECT * FROM staging_blocks WHERE anchored_block_hash = ?1 AND consensus_hash = ?2 AND orphaned = 0 AND processed = 0".to_string();
        let args: &[&dyn ToSql] = &[&block_hash, &consensus_hash];
        let mut rows =
            query_rows::<StagingBlock, _>(block_conn, &sql, args).map_err(Error::DBError)?;
        let len = rows.len();
        match len {
            0 => Ok(None),
            1 => {
                let mut staging_block = rows.pop().unwrap();

                // load up associated block data
                staging_block.block_data =
                    StacksChainState::load_block_bytes(blocks_path, consensus_hash, block_hash)?
                        .unwrap_or(vec![]);
                Ok(Some(staging_block))
            }
            _ => {
                // should be impossible since this is the primary key
                panic!("Got two or more block rows with same burn and block hashes");
            }
        }
    }

    /// Load up a preprocessed block from the staging DB, regardless of its processed status.
    /// Do not load the associated block.
    pub fn load_staging_block_info(
        block_conn: &DBConn,
        index_block_hash: &StacksBlockId,
    ) -> Result<Option<StagingBlock>, Error> {
        let sql = "SELECT * FROM staging_blocks WHERE index_block_hash = ?1 AND orphaned = 0";
        let args: &[&dyn ToSql] = &[&index_block_hash];
        query_row::<StagingBlock, _>(block_conn, sql, args).map_err(Error::DBError)
    }

    /// Get the parent microblock hash of a preprocessed block from the staging DB, regardless of its processed status.
    pub fn get_staging_block_parent_microblock_hash(
        block_conn: &DBConn,
        index_block_hash: &StacksBlockId,
    ) -> Result<Option<BlockHeaderHash>, Error> {
        let sql = "SELECT parent_microblock_hash FROM staging_blocks WHERE index_block_hash = ?1 AND orphaned = 0";
        block_conn
            .query_row(sql, &[index_block_hash], |row| row.get(0))
            .optional()
            .map_err(|e| Error::DBError(db_error::from(e)))
    }

    #[cfg(test)]
    fn load_staging_block_data(
        block_conn: &DBConn,
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<StacksBlock>, Error> {
        match StacksChainState::load_staging_block(
            block_conn,
            blocks_path,
            consensus_hash,
            block_hash,
        )? {
            Some(staging_block) => {
                if staging_block.block_data.len() == 0 {
                    return Ok(None);
                }

                match StacksBlock::consensus_deserialize(&mut &staging_block.block_data[..]) {
                    Ok(block) => Ok(Some(block)),
                    Err(e) => Err(Error::CodecError(e)),
                }
            }
            None => Ok(None),
        }
    }

    /// Load up the list of users who burned for an unprocessed block.
    fn load_staging_block_user_supports(
        block_conn: &DBConn,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Vec<StagingUserBurnSupport>, Error> {
        let sql = "SELECT * FROM staging_user_burn_support WHERE anchored_block_hash = ?1 AND consensus_hash = ?2".to_string();
        let args: &[&dyn ToSql] = &[&block_hash, &consensus_hash];
        let rows = query_rows::<StagingUserBurnSupport, _>(block_conn, &sql, args)
            .map_err(Error::DBError)?;
        Ok(rows)
    }

    /// Load up a queued block's queued pubkey hash
    fn load_staging_block_pubkey_hash(
        block_conn: &DBConn,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<Hash160>, Error> {
        let sql = "SELECT microblock_pubkey_hash FROM staging_blocks WHERE anchored_block_hash = ?1 AND consensus_hash = ?2 AND processed = 0 AND orphaned = 0";
        let args: &[&dyn ToSql] = &[&block_hash, &consensus_hash];
        let rows = query_row_columns::<Hash160, _>(block_conn, sql, args, "microblock_pubkey_hash")
            .map_err(Error::DBError)?;
        match rows.len() {
            0 => Ok(None),
            1 => Ok(Some(rows[0].clone())),
            _ => {
                // should be impossible since this is the primary key
                panic!("Got two or more block rows with same burn and block hashes");
            }
        }
    }

    /// Load up a block's microblock public key hash, staging or not
    fn load_block_pubkey_hash(
        block_conn: &DBConn,
        block_path: &String,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<Hash160>, Error> {
        let pubkey_hash = match StacksChainState::load_staging_block_pubkey_hash(
            block_conn,
            consensus_hash,
            block_hash,
        )? {
            Some(pubkey_hash) => pubkey_hash,
            None => {
                // maybe it's already processed?
                let header = match StacksChainState::load_block_header(
                    block_path,
                    consensus_hash,
                    block_hash,
                )? {
                    Some(block_header) => block_header,
                    None => {
                        // parent isn't available
                        return Ok(None);
                    }
                };
                header.microblock_pubkey_hash
            }
        };
        Ok(Some(pubkey_hash))
    }

    /// Load up a preprocessed microblock's staging info (processed or not), but via
    /// its parent anchored block's index block hash.
    /// Don't load the microblock itself.
    /// Ignores orphaned microblocks.
    pub fn load_staging_microblock_info(
        blocks_conn: &DBConn,
        parent_index_block_hash: &StacksBlockId,
        microblock_hash: &BlockHeaderHash,
    ) -> Result<Option<StagingMicroblock>, Error> {
        let sql = "SELECT * FROM staging_microblocks WHERE index_block_hash = ?1 AND microblock_hash = ?2 AND orphaned = 0 LIMIT 1";
        let args: &[&dyn ToSql] = &[&parent_index_block_hash, &microblock_hash];
        query_row::<StagingMicroblock, _>(blocks_conn, sql, args).map_err(Error::DBError)
    }

    /// Load up a preprocessed microblock's staging info (processed or not), via its index
    /// microblock hash.
    /// Don't load the microblock itself.
    /// Ignores orphaned microblocks.
    pub fn load_staging_microblock_info_indexed(
        blocks_conn: &DBConn,
        index_microblock_hash: &StacksBlockId,
    ) -> Result<Option<StagingMicroblock>, Error> {
        let sql = "SELECT * FROM staging_microblocks WHERE index_microblock_hash = ?1 AND orphaned = 0 LIMIT 1";
        let args: &[&dyn ToSql] = &[&index_microblock_hash];
        query_row::<StagingMicroblock, _>(blocks_conn, sql, args).map_err(Error::DBError)
    }

    /// Load up a preprocessed microblock (processed or not)
    pub fn load_staging_microblock(
        blocks_conn: &DBConn,
        parent_consensus_hash: &ConsensusHash,
        parent_block_hash: &BlockHeaderHash,
        microblock_hash: &BlockHeaderHash,
    ) -> Result<Option<StagingMicroblock>, Error> {
        let parent_index_hash =
            StacksBlockHeader::make_index_block_hash(parent_consensus_hash, parent_block_hash);
        match StacksChainState::load_staging_microblock_info(
            blocks_conn,
            &parent_index_hash,
            microblock_hash,
        )? {
            Some(mut staging_microblock) => {
                // load associated block data
                staging_microblock.block_data =
                    StacksChainState::load_staging_microblock_bytes(blocks_conn, microblock_hash)?
                        .unwrap_or(vec![]);
                Ok(Some(staging_microblock))
            }
            None => {
                // not present
                Ok(None)
            }
        }
    }

    /// Load up a microblock stream fork, given its parent block hash and burn header hash.
    /// Only returns Some(..) if the stream is contiguous.
    /// If processed_only is true, then only processed microblocks are loaded
    fn inner_load_microblock_stream_fork(
        blocks_conn: &DBConn,
        parent_consensus_hash: &ConsensusHash,
        parent_anchored_block_hash: &BlockHeaderHash,
        tip_microblock_hash: &BlockHeaderHash,
        processed_only: bool,
    ) -> Result<Option<Vec<StacksMicroblock>>, Error> {
        let mut ret = vec![];
        let mut mblock_hash = tip_microblock_hash.clone();
        let mut last_seq = u16::MAX;

        loop {
            let microblock =
                match StacksChainState::load_staging_microblock_bytes(blocks_conn, &mblock_hash)? {
                    Some(mblock_data) => StacksMicroblock::consensus_deserialize(
                        &mut &mblock_data[..],
                    )
                    .expect(&format!(
                        "CORRUPTION: failed to parse microblock data for {}/{}-{}",
                        parent_consensus_hash, parent_anchored_block_hash, &mblock_hash,
                    )),
                    None => {
                        test_debug!(
                            "No such microblock (processed={}): {}/{}-{} ({})",
                            processed_only,
                            parent_consensus_hash,
                            parent_anchored_block_hash,
                            &mblock_hash,
                            last_seq
                        );
                        return Ok(None);
                    }
                };

            if processed_only {
                if !StacksChainState::has_processed_microblocks_indexed(
                    blocks_conn,
                    &StacksBlockHeader::make_index_block_hash(
                        parent_consensus_hash,
                        &microblock.block_hash(),
                    ),
                )? {
                    debug!("Microblock {} is not processed", &microblock.block_hash());
                    return Ok(None);
                }
            }

            test_debug!(
                "Loaded microblock {}/{}-{} (parent={}, expect_seq={})",
                &parent_consensus_hash,
                &parent_anchored_block_hash,
                &microblock.block_hash(),
                &microblock.header.prev_block,
                last_seq.saturating_sub(1)
            );

            if last_seq < u16::MAX && microblock.header.sequence < u16::MAX {
                // should always decrease by 1
                assert_eq!(
                    microblock.header.sequence + 1,
                    last_seq,
                    "BUG: stored microblock {:?} ({}) with sequence {} (expected {})",
                    &microblock,
                    microblock.block_hash(),
                    microblock.header.sequence,
                    last_seq.saturating_sub(1)
                );
            }
            assert_eq!(mblock_hash, microblock.block_hash());

            mblock_hash = microblock.header.prev_block.clone();
            last_seq = microblock.header.sequence;
            ret.push(microblock);

            if mblock_hash == *parent_anchored_block_hash {
                break;
            }
        }
        ret.reverse();
        Ok(Some(ret))
    }

    /// Load up a microblock stream fork, even if its microblocks blocks aren't processed.
    pub fn load_microblock_stream_fork(
        blocks_conn: &DBConn,
        parent_consensus_hash: &ConsensusHash,
        parent_anchored_block_hash: &BlockHeaderHash,
        tip_microblock_hash: &BlockHeaderHash,
    ) -> Result<Option<Vec<StacksMicroblock>>, Error> {
        StacksChainState::inner_load_microblock_stream_fork(
            blocks_conn,
            parent_consensus_hash,
            parent_anchored_block_hash,
            tip_microblock_hash,
            false,
        )
    }

    /// Load up a microblock stream fork, but only if its microblocks are processed.
    pub fn load_processed_microblock_stream_fork(
        blocks_conn: &DBConn,
        parent_consensus_hash: &ConsensusHash,
        parent_anchored_block_hash: &BlockHeaderHash,
        tip_microblock_hash: &BlockHeaderHash,
    ) -> Result<Option<Vec<StacksMicroblock>>, Error> {
        StacksChainState::inner_load_microblock_stream_fork(
            blocks_conn,
            parent_consensus_hash,
            parent_anchored_block_hash,
            tip_microblock_hash,
            true,
        )
    }

    pub fn load_descendant_staging_microblock_stream(
        blocks_conn: &DBConn,
        parent_index_block_hash: &StacksBlockId,
        start_seq: u16,
        last_seq: u16,
    ) -> Result<Option<Vec<StacksMicroblock>>, Error> {
        let res = StacksChainState::load_descendant_staging_microblock_stream_with_poison(
            blocks_conn,
            parent_index_block_hash,
            start_seq,
            last_seq,
        )?;
        Ok(res.map(|(microblocks, _)| microblocks))
    }

    /// Load up a block's longest non-forked descendant microblock stream, given its block hash and burn header hash.
    /// Loads microblocks until a fork junction is found (if any), and drops all microblocks after
    /// it if found.  Ties are broken arbitrarily.
    ///
    /// DO NOT USE IN CONSENSUS CODE.
    pub fn load_descendant_staging_microblock_stream_with_poison(
        blocks_conn: &DBConn,
        parent_index_block_hash: &StacksBlockId,
        start_seq: u16,
        last_seq: u16,
    ) -> Result<Option<(Vec<StacksMicroblock>, Option<TransactionPayload>)>, Error> {
        assert!(last_seq >= start_seq);

        let sql = if start_seq == last_seq {
            // takes the same arguments as the range case below, but will
            "SELECT * FROM staging_microblocks WHERE index_block_hash = ?1 AND sequence == ?2 AND sequence == ?3 AND orphaned = 0 ORDER BY sequence ASC".to_string()
        } else {
            "SELECT * FROM staging_microblocks WHERE index_block_hash = ?1 AND sequence >= ?2 AND sequence < ?3 AND orphaned = 0 ORDER BY sequence ASC".to_string()
        };

        let args: &[&dyn ToSql] = &[parent_index_block_hash, &start_seq, &last_seq];
        let staging_microblocks =
            query_rows::<StagingMicroblock, _>(blocks_conn, &sql, args).map_err(Error::DBError)?;

        if staging_microblocks.len() == 0 {
            // haven't seen any microblocks that descend from this block yet
            test_debug!(
                "No microblocks built on {} up to {}",
                &parent_index_block_hash,
                last_seq
            );
            return Ok(None);
        }

        let mut ret = vec![];
        let mut tip: Option<StacksMicroblock> = None;
        let mut fork_poison = None;
        let mut expected_sequence = start_seq;

        // load associated staging microblock data, but best-effort.
        // Stop loading once we find a fork juncture.
        for i in 0..staging_microblocks.len() {
            let mblock_data = StacksChainState::load_staging_microblock_bytes(
                blocks_conn,
                &staging_microblocks[i].microblock_hash,
            )?
            .expect(&format!(
                "BUG: have record for {}-{} but no data",
                &parent_index_block_hash, &staging_microblocks[i].microblock_hash
            ));

            let mblock = match StacksMicroblock::consensus_deserialize(&mut &mblock_data[..]) {
                Ok(mb) => mb,
                Err(e) => {
                    // found an unparseable microblock. abort load
                    warn!(
                        "Failed to load {}-{} ({}): {:?}",
                        &parent_index_block_hash,
                        &staging_microblocks[i].microblock_hash,
                        staging_microblocks[i].sequence,
                        &e
                    );
                    break;
                }
            };

            if mblock.header.sequence > expected_sequence {
                warn!(
                    "Discontinuous microblock stream: expected seq {}, got {}",
                    expected_sequence, mblock.header.sequence
                );
                break;
            }

            // expect forks, so expected_sequence may not always increase
            expected_sequence =
                cmp::min(mblock.header.sequence, expected_sequence).saturating_add(1);

            if let Some(tip_mblock) = tip {
                if mblock.header.sequence == tip_mblock.header.sequence {
                    debug!(
                        "Microblock fork found off of {} at sequence {}",
                        &parent_index_block_hash, mblock.header.sequence
                    );
                    fork_poison = Some(TransactionPayload::PoisonMicroblock(
                        mblock.header,
                        tip_mblock.header,
                    ));
                    ret.pop(); // last microblock pushed (i.e. the tip) conflicts with mblock
                    break;
                }
            }

            tip = Some(mblock.clone());
            ret.push(mblock);
        }
        if fork_poison.is_none() && ret.len() == 0 {
            // just as if there were no blocks loaded
            Ok(None)
        } else {
            Ok(Some((ret, fork_poison)))
        }
    }

    /// Load up the next block in a microblock stream, assuming there is only one child.
    /// If there are zero children, or more than one child, then returns None.
    ///
    /// DO NOT USE IN CONSENSUS CODE.
    pub fn load_next_descendant_microblock(
        blocks_conn: &DBConn,
        parent_index_block_hash: &StacksBlockId,
        seq: u16,
    ) -> Result<Option<StacksMicroblock>, Error> {
        StacksChainState::load_descendant_staging_microblock_stream(
            blocks_conn,
            parent_index_block_hash,
            seq,
            seq,
        )
        .and_then(|list_opt| match list_opt {
            Some(mut list) => Ok(list.pop()),
            None => Ok(None),
        })
    }

    /// stacks_block _must_ have been committed, or this will return an error
    pub fn get_parent(&self, stacks_block: &StacksBlockId) -> Result<StacksBlockId, Error> {
        let sql = "SELECT parent_block_id FROM block_headers WHERE index_block_hash = ?";
        self.db()
            .query_row(sql, &[stacks_block], |row| row.get(0))
            .map_err(|e| Error::from(db_error::from(e)))
    }

    pub fn get_parent_consensus_hash(
        sort_ic: &SortitionDBConn,
        parent_block_hash: &BlockHeaderHash,
        my_consensus_hash: &ConsensusHash,
    ) -> Result<Option<ConsensusHash>, Error> {
        let sort_handle = SortitionHandleConn::open_reader_consensus(sort_ic, my_consensus_hash)?;

        // find all blocks that we have that could be this block's parent
        let sql = "SELECT * FROM snapshots WHERE winning_stacks_block_hash = ?1";
        let possible_parent_snapshots =
            query_rows::<BlockSnapshot, _>(&sort_handle, &sql, &[parent_block_hash])?;
        for possible_parent in possible_parent_snapshots.into_iter() {
            let burn_ancestor =
                sort_handle.get_block_snapshot(&possible_parent.burn_header_hash)?;
            if let Some(_ancestor) = burn_ancestor {
                // found!
                return Ok(Some(possible_parent.consensus_hash));
            }
        }
        return Ok(None);
    }

    /// Get an anchored block's parent block header.
    /// Doesn't matter if it's staging or not.
    pub fn load_parent_block_header(
        sort_ic: &SortitionDBConn,
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
    ) -> Result<Option<(StacksBlockHeader, ConsensusHash)>, Error> {
        let header = match StacksChainState::load_block_header(
            blocks_path,
            consensus_hash,
            anchored_block_hash,
        )? {
            Some(hdr) => hdr,
            None => {
                return Ok(None);
            }
        };

        let sort_handle = SortitionHandleConn::open_reader_consensus(sort_ic, consensus_hash)?;

        // find all blocks that we have that could be this block's parent
        let sql = "SELECT * FROM snapshots WHERE winning_stacks_block_hash = ?1";
        let possible_parent_snapshots =
            query_rows::<BlockSnapshot, _>(&sort_handle, &sql, &[&header.parent_block])?;
        for possible_parent in possible_parent_snapshots.into_iter() {
            let burn_ancestor =
                sort_handle.get_block_snapshot(&possible_parent.burn_header_hash)?;
            if let Some(ancestor) = burn_ancestor {
                // found!
                let ret = StacksChainState::load_block_header(
                    blocks_path,
                    &ancestor.consensus_hash,
                    &ancestor.winning_stacks_block_hash,
                )?
                .map(|header| (header, ancestor.consensus_hash));

                return Ok(ret);
            }
        }
        return Ok(None);
    }

    /// Store a preprocessed block, queuing it up for subsequent processing.
    /// The caller should at least verify that the block is attached to some fork in the burn
    /// chain.
    fn store_staging_block<'a>(
        tx: &mut DBTx<'a>,
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
        parent_consensus_hash: &ConsensusHash,
        commit_burn: u64,
        sortition_burn: u64,
        download_time: u64,
    ) -> Result<(), Error> {
        debug!(
            "Store anchored block {}/{}, parent in {}",
            consensus_hash,
            block.block_hash(),
            parent_consensus_hash
        );
        assert!(commit_burn < i64::max_value() as u64);
        assert!(sortition_burn < i64::max_value() as u64);

        let block_hash = block.block_hash();
        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_hash);

        let attachable = {
            // if this block has an unprocessed staging parent, then it's not attachable until its parent is.
            let has_unprocessed_parent_sql = "SELECT anchored_block_hash FROM staging_blocks WHERE anchored_block_hash = ?1 AND consensus_hash = ?2 AND processed = 0 AND orphaned = 0 LIMIT 1";
            let has_parent_sql = "SELECT anchored_block_hash FROM staging_blocks WHERE anchored_block_hash = ?1 AND consensus_hash = ?2 LIMIT 1";
            let has_parent_args: &[&dyn ToSql] =
                &[&block.header.parent_block, &parent_consensus_hash];
            let has_unprocessed_parent_rows = query_row_columns::<BlockHeaderHash, _>(
                &tx,
                has_unprocessed_parent_sql,
                has_parent_args,
                "anchored_block_hash",
            )
            .map_err(Error::DBError)?;
            let has_parent_rows = query_row_columns::<BlockHeaderHash, _>(
                &tx,
                has_parent_sql,
                has_parent_args,
                "anchored_block_hash",
            )
            .map_err(Error::DBError)?;
            let parent_not_in_staging_blocks =
                has_parent_rows.len() == 0 && block.header.parent_block != FIRST_STACKS_BLOCK_HASH;
            if has_unprocessed_parent_rows.len() > 0 || parent_not_in_staging_blocks {
                // still have unprocessed parent OR its parent is not in staging_blocks at all -- this block is not attachable
                debug!(
                    "Store non-attachable anchored block {}/{}",
                    consensus_hash,
                    block.block_hash()
                );
                0
            } else {
                // no unprocessed parents -- this block is potentially attachable
                1
            }
        };

        // store block metadata
        let sql = "INSERT OR REPLACE INTO staging_blocks \
                   (anchored_block_hash, \
                   parent_anchored_block_hash, \
                   consensus_hash, \
                   parent_consensus_hash, \
                   parent_microblock_hash, \
                   parent_microblock_seq, \
                   microblock_pubkey_hash, \
                   height, \
                   attachable, \
                   processed, \
                   orphaned, \
                   commit_burn, \
                   sortition_burn, \
                   index_block_hash, \
                   arrival_time, \
                   processed_time, \
                   download_time) \
                   VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17)";
        let args: &[&dyn ToSql] = &[
            &block_hash,
            &block.header.parent_block,
            &consensus_hash,
            &parent_consensus_hash,
            &block.header.parent_microblock,
            &block.header.parent_microblock_sequence,
            &block.header.microblock_pubkey_hash,
            &u64_to_sql(block.header.total_work.work)?,
            &attachable,
            &0,
            &0,
            &u64_to_sql(commit_burn)?,
            &u64_to_sql(sortition_burn)?,
            &index_block_hash,
            &u64_to_sql(get_epoch_time_secs())?,
            &0,
            &u64_to_sql(download_time)?,
        ];

        tx.execute(&sql, args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        StacksChainState::store_block(blocks_path, consensus_hash, block)?;

        // mark all children of this new block as unattachable -- need to attach this block first!
        // this should be done across all burnchains.
        let children_sql =
            "UPDATE staging_blocks SET attachable = 0 WHERE parent_anchored_block_hash = ?1";
        let children_args = [&block_hash];

        tx.execute(&children_sql, &children_args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        Ok(())
    }

    /// Store a preprocessed microblock, queueing it up for subsequent processing.
    /// The caller should at least verify that this block was signed by the miner of the ancestor
    /// anchored block that this microblock builds off of.  Because microblocks may arrive out of
    /// order, this method does not check that.
    /// The consensus_hash and anchored_block_hash correspond to the _parent_ Stacks block.
    /// Microblocks ought to only be stored if they are first confirmed to have been signed.
    pub fn store_staging_microblock<'a>(
        tx: &mut DBTx<'a>,
        parent_consensus_hash: &ConsensusHash,
        parent_anchored_block_hash: &BlockHeaderHash,
        microblock: &StacksMicroblock,
    ) -> Result<(), Error> {
        test_debug!(
            "Store staging microblock {}/{}-{}",
            parent_consensus_hash,
            parent_anchored_block_hash,
            microblock.block_hash()
        );

        let mut microblock_bytes = vec![];
        microblock
            .consensus_serialize(&mut microblock_bytes)
            .map_err(Error::CodecError)?;

        let index_block_hash = StacksBlockHeader::make_index_block_hash(
            parent_consensus_hash,
            parent_anchored_block_hash,
        );

        let index_microblock_hash = StacksBlockHeader::make_index_block_hash(
            parent_consensus_hash,
            &microblock.block_hash(),
        );

        // store microblock metadata
        let sql = "INSERT OR REPLACE INTO staging_microblocks (anchored_block_hash, consensus_hash, index_block_hash, microblock_hash, parent_hash, index_microblock_hash, sequence, processed, orphaned) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)";
        let args: &[&dyn ToSql] = &[
            &parent_anchored_block_hash,
            &parent_consensus_hash,
            &index_block_hash,
            &microblock.block_hash(),
            &microblock.header.prev_block,
            &index_microblock_hash,
            &microblock.header.sequence,
            &0,
            &0,
        ];

        tx.execute(&sql, args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        // store microblock bytes
        let block_sql = "INSERT OR REPLACE INTO staging_microblocks_data \
                         (block_hash, block_data)
                         VALUES (?1, ?2)";
        let block_args: &[&dyn ToSql] = &[&microblock.block_hash(), &microblock_bytes];

        tx.execute(&block_sql, block_args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        Ok(())
    }

    /// Store users who burned in support of a block
    fn store_staging_block_user_burn_supports<'a>(
        tx: &mut DBTx<'a>,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
        burn_supports: &Vec<UserBurnSupportOp>,
    ) -> Result<(), Error> {
        for burn_support in burn_supports.iter() {
            assert!(burn_support.burn_fee < i64::max_value() as u64);
        }

        for burn_support in burn_supports.iter() {
            let sql = "INSERT OR REPLACE INTO staging_user_burn_support (anchored_block_hash, consensus_hash, address, burn_amount, vtxindex) VALUES (?1, ?2, ?3, ?4, ?5)";
            let args: &[&dyn ToSql] = &[
                &consensus_hash,
                &block_hash,
                &burn_support.address.to_string(),
                &u64_to_sql(burn_support.burn_fee)?,
                &burn_support.vtxindex,
            ];

            tx.execute(&sql, args)
                .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;
        }

        Ok(())
    }

    /// Read all the i64 values from a query (possibly none).
    fn read_i64s(conn: &DBConn, query: &str, args: &[&dyn ToSql]) -> Result<Vec<i64>, Error> {
        let mut stmt = conn
            .prepare(query)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;
        let mut rows = stmt
            .query(args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        // gather
        let mut row_data: Vec<i64> = vec![];
        while let Some(row) = rows.next().map_err(|e| db_error::SqliteError(e))? {
            let val_opt: Option<i64> = row.get_unwrap(0);
            if let Some(val) = val_opt {
                row_data.push(val);
            }
        }

        Ok(row_data)
    }

    /// Do we have a block queued up, and if so, is it being processed?.
    /// Return Some(processed) if the block is queued up -- true if processed, false if not
    /// Return None if the block is not queued up
    pub fn get_staging_block_status(
        blocks_conn: &DBConn,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<bool>, Error> {
        StacksChainState::read_i64s(blocks_conn, "SELECT processed FROM staging_blocks WHERE anchored_block_hash = ?1 AND consensus_hash = ?2", &[block_hash, consensus_hash])
            .and_then(|processed| {
                if processed.len() == 0 {
                    Ok(None)
                }
                else if processed.len() == 1 {
                    Ok(Some(processed[0] != 0))
                }
                else {
                    Err(Error::DBError(db_error::Overflow))
                }
            })
    }

    /// Do we have a given Stacks block in any PoX fork or sortition fork?
    pub fn get_staging_block_consensus_hashes(
        blocks_conn: &DBConn,
        block_hash: &BlockHeaderHash,
    ) -> Result<Vec<ConsensusHash>, Error> {
        query_rows::<ConsensusHash, _>(
            blocks_conn,
            "SELECT consensus_hash FROM staging_blocks WHERE anchored_block_hash = ?1",
            &[block_hash],
        )
        .map_err(|e| e.into())
    }

    /// Is a block orphaned?
    pub fn is_block_orphaned(
        blocks_conn: &DBConn,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<bool, Error> {
        StacksChainState::read_i64s(blocks_conn, "SELECT orphaned FROM staging_blocks WHERE anchored_block_hash = ?1 AND consensus_hash = ?2", &[block_hash, consensus_hash])
            .and_then(|orphaned| {
                if orphaned.len() == 0 {
                    Ok(false)
                }
                else if orphaned.len() == 1 {
                    Ok(orphaned[0] != 0)
                }
                else {
                    Err(Error::DBError(db_error::Overflow))
                }
            })
    }

    /// Do we have a microblock in the DB, and if so, has it been processed?
    /// The query takes the consensus hash and block hash of a block that _produced_ this stream.
    /// Return Some(processed) if the microblock is queued up.
    /// Return None if the microblock is not queued up.
    #[cfg(test)]
    pub fn get_microblock_status(
        &self,
        parent_consensus_hash: &ConsensusHash,
        parent_block_hash: &BlockHeaderHash,
        microblock_hash: &BlockHeaderHash,
    ) -> Result<Option<bool>, Error> {
        StacksChainState::read_i64s(&self.db(), "SELECT processed FROM staging_microblocks WHERE anchored_block_hash = ?1 AND microblock_hash = ?2 AND consensus_hash = ?3", &[&parent_block_hash, microblock_hash, &parent_consensus_hash])
            .and_then(|processed| {
                if processed.len() == 0 {
                    Ok(None)
                }
                else if processed.len() == 1 {
                    Ok(Some(processed[0] != 0))
                }
                else {
                    Err(Error::DBError(db_error::Overflow))
                }
            })
    }

    /// Given an anchor block's index hash, does it confirm any microblocks?
    /// Due to the way we process microblocks -- i.e. all microblocks between a parent/child anchor
    /// block are processed atomically -- it is sufficient to check that there exists a microblock
    /// that is the parent microblock of this block, and is processed.
    /// Used for RPC where the tail hash isn't known.
    pub fn has_processed_microblocks(
        &self,
        child_index_block_hash: &StacksBlockId,
    ) -> Result<bool, Error> {
        let (parent_consensus_hash, parent_block_hash) =
            match StacksChainState::get_parent_block_header_hashes(
                &self.db(),
                &child_index_block_hash,
            )? {
                Some(x) => x,
                None => {
                    // no parent stored, so no confirmed microblocks
                    return Ok(false);
                }
            };

        let parent_index_block_hash =
            StacksBlockHeader::make_index_block_hash(&parent_consensus_hash, &parent_block_hash);

        let parent_microblock_hash =
            match StacksChainState::get_staging_block_parent_microblock_hash(
                &self.db(),
                child_index_block_hash,
            )? {
                Some(x) => x,
                None => {
                    // no header record for this block, so it cannot have confirmed anything
                    return Ok(false);
                }
            };

        let sql = "SELECT 1 FROM staging_microblocks WHERE index_block_hash = ?1 AND microblock_hash = ?2 AND processed = 1 AND orphaned = 0";
        let args: &[&dyn ToSql] = &[&parent_index_block_hash, &parent_microblock_hash];
        let res = self
            .db()
            .query_row(sql, args, |_r| Ok(()))
            .optional()
            .expect("DB CORRUPTION: staging blocks DB corrupted!")
            .is_some();

        Ok(res)
    }

    /// Given an anchor block's index hash, and the last microblock hash in a hypothetical tail,
    /// does this anchor block confirm that tail?
    /// Due to the way we process microblocks -- i.e. all microblocks between a parent/child anchor
    /// block are processed atomically -- it is sufficient to check that there exists a microblock
    /// that is the parent microblock of this block, and is processed.
    pub fn has_processed_microblocks_at_tail(
        &self,
        child_index_block_hash: &StacksBlockId,
        parent_microblock_hash: &BlockHeaderHash,
    ) -> Result<bool, Error> {
        StacksChainState::read_i64s(self.db(), "SELECT staging_microblocks.processed
                                                FROM staging_blocks JOIN staging_microblocks ON staging_blocks.parent_anchored_block_hash = staging_microblocks.anchored_block_hash AND staging_blocks.parent_consensus_hash = staging_microblocks.consensus_hash
                                                WHERE staging_blocks.index_block_hash = ?1 AND staging_microblocks.microblock_hash = ?2 AND staging_microblocks.orphaned = 0", &[child_index_block_hash, &parent_microblock_hash])
            .and_then(|processed| {
                if processed.len() == 0 {
                    Ok(false)
                }
                else if processed.len() == 1 {
                    Ok(processed[0] != 0)
                }
                else {
                    Err(Error::DBError(db_error::Overflow))
                }
            })
    }

    /// Generate a blocks inventory message, given the output of
    /// SortitionDB::get_stacks_header_hashes().  Note that header_hashes must be less than or equal to
    /// pox_constants.reward_cycle_length, in order to generate a valid BlocksInvData payload.
    pub fn get_blocks_inventory(
        &self,
        header_hashes: &[(ConsensusHash, Option<BlockHeaderHash>)],
    ) -> Result<BlocksInvData, Error> {
        let mut block_bits = Vec::with_capacity(header_hashes.len());
        let mut microblock_bits = Vec::with_capacity(header_hashes.len());

        let mut block_bench_total = 0;
        let mut mblock_bench_total = 0;

        for (consensus_hash, stacks_header_hash_opt) in header_hashes.iter() {
            match stacks_header_hash_opt {
                None => {
                    test_debug!(
                        "Do not have any block in burn block {} in {}",
                        &consensus_hash,
                        &self.blocks_path
                    );
                    block_bits.push(false);
                    microblock_bits.push(false);
                }
                Some(ref stacks_header_hash) => {
                    let index_block_hash = StacksBlockHeader::make_index_block_hash(
                        consensus_hash,
                        stacks_header_hash,
                    );

                    let block_bench_start = get_epoch_time_ms();
                    let mut parent_microblock_hash = None;

                    match StacksChainState::load_block_header(
                        &self.blocks_path,
                        &consensus_hash,
                        &stacks_header_hash,
                    ) {
                        Ok(Some(hdr)) => {
                            test_debug!(
                                "Have anchored block {} in {}",
                                &index_block_hash,
                                &self.blocks_path
                            );
                            if hdr.parent_microblock != EMPTY_MICROBLOCK_PARENT_HASH {
                                parent_microblock_hash = Some(hdr.parent_microblock.clone());
                            }
                            block_bits.push(true);
                        }
                        _ => {
                            test_debug!("Do not have anchored block {}", &index_block_hash);
                            block_bits.push(false);
                        }
                    }

                    let block_bench_end = get_epoch_time_ms();
                    block_bench_total += block_bench_end.saturating_sub(block_bench_start);

                    let mblock_bench_begin = get_epoch_time_ms();
                    if let Some(parent_microblock) = parent_microblock_hash {
                        if self.has_processed_microblocks_at_tail(
                            &index_block_hash,
                            &parent_microblock,
                        )? {
                            test_debug!(
                                "Have processed microblocks confirmed by anchored block {}",
                                &index_block_hash,
                            );
                            microblock_bits.push(true);
                        } else {
                            test_debug!("Do not have processed microblocks confirmed by anchored block {} -- no index hash)", &index_block_hash);
                            microblock_bits.push(false);
                        }
                    } else {
                        test_debug!(
                            "Do not have processed microblocks confirmed by anchored block {}",
                            &index_block_hash
                        );
                        microblock_bits.push(false);
                    }

                    let mblock_bench_end = get_epoch_time_ms();
                    mblock_bench_total += mblock_bench_end.saturating_sub(mblock_bench_begin);
                }
            }
        }

        assert_eq!(block_bits.len(), microblock_bits.len());

        let block_bitvec = BlocksInvData::compress_bools(&block_bits);
        let microblocks_bitvec = BlocksInvData::compress_bools(&microblock_bits);

        debug!(
            "Time to evaluate {} entries: {}ms for blocks, {}ms for microblocks",
            header_hashes.len(),
            block_bench_total,
            mblock_bench_total
        );

        Ok(BlocksInvData {
            bitlen: block_bits.len() as u16,
            block_bitvec: block_bitvec,
            microblocks_bitvec: microblocks_bitvec,
        })
    }

    /// Do we have a staging block?  Return true if the block is present and marked as unprocessed;
    /// false otherwise
    pub fn has_staging_block(
        blocks_conn: &DBConn,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<bool, Error> {
        match StacksChainState::get_staging_block_status(blocks_conn, consensus_hash, block_hash)? {
            Some(processed) => Ok(!processed),
            None => Ok(false),
        }
    }

    /// Delete a microblock's data from the DB
    fn delete_microblock_data(
        tx: &mut DBTx,
        microblock_hash: &BlockHeaderHash,
    ) -> Result<(), Error> {
        let args = [&microblock_hash];

        // copy into the invalidated_microblocks_data table
        let copy_sql = "INSERT OR REPLACE INTO invalidated_microblocks_data SELECT * FROM staging_microblocks_data WHERE block_hash = ?1";
        tx.execute(copy_sql, &args)?;

        // clear out the block data from staging
        let clear_sql = "DELETE FROM staging_microblocks_data WHERE block_hash = ?1";
        tx.execute(clear_sql, &args)?;

        Ok(())
    }

    /// Mark an anchored block as orphaned and both orphan and delete its descendant microblock data.
    /// The blocks database will eventually delete all orphaned data.
    fn delete_orphaned_epoch_data<'a>(
        tx: &mut DBTx<'a>,
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
    ) -> Result<(), Error> {
        // This block is orphaned
        let update_block_sql = "UPDATE staging_blocks SET orphaned = 1, processed = 1, attachable = 0 WHERE consensus_hash = ?1 AND anchored_block_hash = ?2";
        let update_block_args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];

        // All descendants of this processed block are never attachable.
        // Indicate this by marking all children as orphaned (but not procesed), across all burnchain forks.
        let update_children_sql = "UPDATE staging_blocks SET orphaned = 1, processed = 0, attachable = 0 WHERE parent_consensus_hash = ?1 AND parent_anchored_block_hash = ?2";
        let update_children_args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];

        // find all orphaned microblocks, and delete the block data
        let find_orphaned_microblocks_sql = "SELECT microblock_hash FROM staging_microblocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2";
        let find_orphaned_microblocks_args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];
        let orphaned_microblock_hashes = query_row_columns::<BlockHeaderHash, _>(
            tx,
            find_orphaned_microblocks_sql,
            find_orphaned_microblocks_args,
            "microblock_hash",
        )?;

        // drop microblocks (this processes them)
        let update_microblock_children_sql = "UPDATE staging_microblocks SET orphaned = 1, processed = 1 WHERE consensus_hash = ?1 AND anchored_block_hash = ?2";
        let update_microblock_children_args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];

        tx.execute(update_block_sql, update_block_args)?;

        tx.execute(update_children_sql, update_children_args)?;

        tx.execute(
            update_microblock_children_sql,
            update_microblock_children_args,
        )?;

        for mblock_hash in orphaned_microblock_hashes {
            StacksChainState::delete_microblock_data(tx, &mblock_hash)?;
        }

        // mark the block as invalid if we haven't already
        let block_path =
            StacksChainState::get_block_path(blocks_path, consensus_hash, anchored_block_hash)?;
        match fs::metadata(&block_path) {
            Ok(_) => {
                StacksChainState::free_block(blocks_path, consensus_hash, anchored_block_hash);
            }
            Err(_) => {
                StacksChainState::atomic_file_write(&block_path, &vec![])?;
            }
        }

        Ok(())
    }

    /// Forget that a block and microblock stream was marked as invalid, given a particular consensus hash.
    /// This is necessary when dealing with PoX reorgs, whereby an epoch can be unprocessible on one
    /// fork but processable on another (i.e. the same block can show up in two different PoX
    /// forks, but will only be valid in at most one of them).
    /// This does not restore any block data; it merely makes it possible to go re-process them.
    pub fn forget_orphaned_epoch_data<'a>(
        tx: &mut DBTx<'a>,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
    ) -> Result<(), Error> {
        test_debug!(
            "Forget that {}/{} is orphaned, if it is orphaned at all",
            consensus_hash,
            anchored_block_hash
        );

        let sql = "DELETE FROM staging_blocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2 AND orphaned = 1 AND processed = 1";
        let args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];

        tx.execute(sql, args)?;

        let sql = "DELETE FROM staging_microblocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2 AND orphaned = 1 AND processed = 1";

        tx.execute(sql, args)?;

        Ok(())
    }

    /// Clear out a staging block -- mark it as processed.
    /// Mark its children as attachable.
    /// Idempotent.
    /// sort_tx_opt is required if accept is true
    fn set_block_processed<'a, 'b>(
        tx: &mut DBTx<'a>,
        mut sort_tx_opt: Option<&mut SortitionHandleTx<'b>>,
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
        accept: bool,
    ) -> Result<(), Error> {
        let sql = "SELECT * FROM staging_blocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2 AND orphaned = 0".to_string();
        let args: &[&dyn ToSql] = &[&consensus_hash, &anchored_block_hash];

        let has_stored_block = StacksChainState::has_stored_block(
            tx,
            blocks_path,
            consensus_hash,
            anchored_block_hash,
        )?;

        let rows = query_rows::<StagingBlock, _>(tx, &sql, args).map_err(Error::DBError)?;
        let block = match rows.len() {
            0 => {
                // not an error if this block was already orphaned
                let orphan_sql = "SELECT * FROM staging_blocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2 AND orphaned = 1".to_string();
                let orphan_args: &[&dyn ToSql] = &[&consensus_hash, &anchored_block_hash];
                let orphan_rows = query_rows::<StagingBlock, _>(tx, &orphan_sql, orphan_args)
                    .map_err(Error::DBError)?;
                if orphan_rows.len() == 1 {
                    return Ok(());
                } else {
                    test_debug!(
                        "No such block at {}/{}",
                        consensus_hash,
                        anchored_block_hash
                    );
                    return Err(Error::DBError(db_error::NotFoundError));
                }
            }
            1 => rows[0].clone(),
            _ => {
                // should never happen
                panic!("Multiple staging blocks with same burn hash and block hash");
            }
        };

        if !block.processed {
            if !has_stored_block {
                if accept {
                    debug!(
                        "Accept block {}/{} as {}",
                        consensus_hash,
                        anchored_block_hash,
                        StacksBlockHeader::make_index_block_hash(
                            &consensus_hash,
                            &anchored_block_hash
                        )
                    );
                } else {
                    info!("Reject block {}/{}", consensus_hash, anchored_block_hash);
                }
            } else {
                debug!(
                    "Already stored block {}/{} ({})",
                    consensus_hash,
                    anchored_block_hash,
                    StacksBlockHeader::make_index_block_hash(&consensus_hash, &anchored_block_hash)
                );
            }
        } else {
            debug!(
                "Already processed block {}/{} ({})",
                consensus_hash,
                anchored_block_hash,
                StacksBlockHeader::make_index_block_hash(&consensus_hash, &anchored_block_hash)
            );
        }

        let update_sql = "UPDATE staging_blocks SET processed = 1, processed_time = ?1 WHERE consensus_hash = ?2 AND anchored_block_hash = ?3".to_string();
        let update_args: &[&dyn ToSql] = &[
            &u64_to_sql(get_epoch_time_secs())?,
            &consensus_hash,
            &anchored_block_hash,
        ];

        tx.execute(&update_sql, update_args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        if accept {
            // if we accepted this block, then children of this processed block are now attachable.
            // Applies across all burnchain forks
            let update_children_sql =
                "UPDATE staging_blocks SET attachable = 1 WHERE parent_anchored_block_hash = ?1"
                    .to_string();
            let update_children_args = [&anchored_block_hash];

            tx.execute(&update_children_sql, &update_children_args)
                .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

            // mark this block as processed in the burn db too
            match sort_tx_opt {
                Some(ref mut sort_tx) => {
                    sort_tx.set_stacks_block_accepted(
                        consensus_hash,
                        &block.parent_anchored_block_hash,
                        &block.anchored_block_hash,
                        block.height,
                    )?;
                }
                None => {
                    if !cfg!(test) {
                        // not allowed in production
                        panic!("No burn DB transaction given to block processor");
                    }
                }
            }
        } else {
            // Otherwise, all descendants of this processed block are never attachable.
            // Mark this block's children as orphans, blow away its data, and blow away its descendant microblocks.
            debug!("Orphan block {}/{}", consensus_hash, anchored_block_hash);
            StacksChainState::delete_orphaned_epoch_data(
                tx,
                blocks_path,
                consensus_hash,
                anchored_block_hash,
            )?;
        }

        Ok(())
    }

    #[cfg(test)]
    fn set_block_orphaned<'a>(
        tx: &mut DBTx<'a>,
        blocks_path: &String,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
    ) -> Result<(), Error> {
        // This block is orphaned
        let update_block_sql = "UPDATE staging_blocks SET orphaned = 1, processed = 1, attachable = 0 WHERE consensus_hash = ?1 AND anchored_block_hash = ?2".to_string();
        let update_block_args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];

        // find all orphaned microblocks, and delete the block data
        let find_orphaned_microblocks_sql = "SELECT microblock_hash FROM staging_microblocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2";
        let find_orphaned_microblocks_args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];
        let orphaned_microblock_hashes = query_row_columns::<BlockHeaderHash, _>(
            tx,
            find_orphaned_microblocks_sql,
            find_orphaned_microblocks_args,
            "microblock_hash",
        )
        .map_err(Error::DBError)?;

        // drop microblocks (this processes them)
        let update_microblock_children_sql = "UPDATE staging_microblocks SET orphaned = 1, processed = 1 WHERE consensus_hash = ?1 AND anchored_block_hash = ?2".to_string();
        let update_microblock_children_args: &[&dyn ToSql] = &[consensus_hash, anchored_block_hash];

        tx.execute(&update_block_sql, update_block_args)
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        // mark the block as empty if we haven't already
        let block_path =
            StacksChainState::get_block_path(blocks_path, consensus_hash, anchored_block_hash)?;
        match fs::metadata(&block_path) {
            Ok(_) => {
                StacksChainState::free_block(blocks_path, consensus_hash, anchored_block_hash);
            }
            Err(_) => {
                StacksChainState::atomic_file_write(&block_path, &vec![])?;
            }
        }

        Ok(())
    }

    /// Drop a trail of staging microblocks.  Mark them as orphaned and delete their data.
    /// Also, orphan any anchored children blocks that build off of the now-orphaned microblocks.
    fn drop_staging_microblocks<'a>(
        tx: &mut DBTx<'a>,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
        invalid_block_hash: &BlockHeaderHash,
    ) -> Result<(), Error> {
        // find offending sequence
        let seq_sql = "SELECT sequence FROM staging_microblocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2 AND microblock_hash = ?3 AND processed = 0 AND orphaned = 0".to_string();
        let seq_args: &[&dyn ToSql] = &[&consensus_hash, &anchored_block_hash, &invalid_block_hash];
        let seq = match query_int::<_>(tx, &seq_sql, seq_args) {
            Ok(seq) => seq,
            Err(e) => match e {
                db_error::NotFoundError => {
                    // no microblocks to delete
                    return Ok(());
                }
                _ => {
                    return Err(Error::DBError(e));
                }
            },
        };

        debug!(
            "Drop staging microblocks {}/{} up to {} ({})",
            consensus_hash, anchored_block_hash, invalid_block_hash, seq
        );

        // drop staging children at and beyond the invalid block
        let update_microblock_children_sql = "UPDATE staging_microblocks SET orphaned = 1, processed = 1 WHERE anchored_block_hash = ?1 AND sequence >= ?2".to_string();
        let update_microblock_children_args: &[&dyn ToSql] = &[&anchored_block_hash, &seq];

        tx.execute(
            &update_microblock_children_sql,
            update_microblock_children_args,
        )
        .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

        // find all orphaned microblocks hashes, and delete the block data
        let find_orphaned_microblocks_sql = "SELECT microblock_hash FROM staging_microblocks WHERE anchored_block_hash = ?1 AND sequence >= ?2";
        let find_orphaned_microblocks_args: &[&dyn ToSql] = &[&anchored_block_hash, &seq];
        let orphaned_microblock_hashes = query_row_columns::<BlockHeaderHash, _>(
            tx,
            find_orphaned_microblocks_sql,
            find_orphaned_microblocks_args,
            "microblock_hash",
        )
        .map_err(Error::DBError)?;

        // garbage-collect
        for mblock_hash in orphaned_microblock_hashes.iter() {
            StacksChainState::delete_microblock_data(tx, &mblock_hash)?;
        }

        for mblock_hash in orphaned_microblock_hashes.iter() {
            // orphan any staging blocks that build on the now-invalid microblocks
            let update_block_children_sql = "UPDATE staging_blocks SET orphaned = 1, processed = 0, attachable = 0 WHERE parent_microblock_hash = ?1".to_string();
            let update_block_children_args = [&mblock_hash];

            tx.execute(&update_block_children_sql, &update_block_children_args)
                .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;
        }

        Ok(())
    }

    /// Mark a range of a stream of microblocks as confirmed.
    /// All the corresponding blocks must have been validated and proven contiguous.
    fn set_microblocks_processed<'a>(
        tx: &mut DBTx<'a>,
        child_consensus_hash: &ConsensusHash,
        child_anchored_block_hash: &BlockHeaderHash,
        last_microblock_hash: &BlockHeaderHash,
    ) -> Result<(), Error> {
        let child_index_block_hash = StacksBlockHeader::make_index_block_hash(
            child_consensus_hash,
            child_anchored_block_hash,
        );
        let (parent_consensus_hash, parent_block_hash) =
            match StacksChainState::get_parent_block_header_hashes(tx, &child_index_block_hash)? {
                Some(x) => x,
                None => {
                    return Ok(());
                }
            };
        let parent_index_hash =
            StacksBlockHeader::make_index_block_hash(&parent_consensus_hash, &parent_block_hash);

        let mut mblock_hash = last_microblock_hash.clone();
        let sql = "UPDATE staging_microblocks SET processed = 1 WHERE consensus_hash = ?1 AND anchored_block_hash = ?2 AND microblock_hash = ?3";

        loop {
            test_debug!("Set {}-{} processed", &parent_index_hash, &mblock_hash);

            // confirm this microblock
            let args: &[&dyn ToSql] = &[&parent_consensus_hash, &parent_block_hash, &mblock_hash];
            tx.execute(sql, args)
                .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

            // find the parent so we can confirm it as well
            let mblock_info_opt = StacksChainState::load_staging_microblock_info(
                tx,
                &parent_index_hash,
                &mblock_hash,
            )?;

            if let Some(mblock_info) = mblock_info_opt {
                if mblock_info.parent_hash == parent_block_hash {
                    // at head of stream
                    break;
                } else {
                    mblock_hash = mblock_info.parent_hash;
                }
            } else {
                // missing parent microblock -- caller should abort this DB transaction
                debug!(
                    "No such staging microblock {}/{}-{}",
                    &parent_consensus_hash, &parent_block_hash, &mblock_hash
                );
                return Err(Error::NoSuchBlockError);
            }
        }

        Ok(())
    }

    /// Is a particular microblock stored in the staging DB, given the index anchored block hash of the block
    /// that confirms it?
    pub fn has_staging_microblock_indexed(
        &self,
        child_index_block_hash: &StacksBlockId,
        seq: u16,
    ) -> Result<bool, Error> {
        let (parent_consensus_hash, parent_block_hash) =
            match StacksChainState::get_parent_block_header_hashes(
                &self.db(),
                &child_index_block_hash,
            )? {
                Some(x) => x,
                None => {
                    return Ok(false);
                }
            };
        let parent_index_block_hash =
            StacksBlockHeader::make_index_block_hash(&parent_consensus_hash, &parent_block_hash);
        StacksChainState::read_i64s(&self.db(), "SELECT processed FROM staging_microblocks WHERE index_block_hash = ?1 AND sequence = ?2", &[&parent_index_block_hash, &seq])
            .and_then(|processed| {
                if processed.len() == 0 {
                    Ok(false)
                }
                else if processed.len() == 1 {
                    Ok(processed[0] == 0)
                }
                else {
                    Err(Error::DBError(db_error::Overflow))
                }
            })
    }

    /// Do we have a particular microblock stream given its indexed tail microblock hash?
    /// Used by the RPC endpoint to determine if we can serve back a stream of microblocks.
    pub fn has_processed_microblocks_indexed(
        conn: &DBConn,
        index_microblock_hash: &StacksBlockId,
    ) -> Result<bool, Error> {
        let sql = "SELECT 1 FROM staging_microblocks WHERE index_microblock_hash = ?1 AND processed = 1 AND orphaned = 0";
        let args: &[&dyn ToSql] = &[index_microblock_hash];
        let res = conn
            .query_row(&sql, args, |_r| Ok(()))
            .optional()
            .expect("DB CORRUPTION: block header DB corrupted!")
            .is_some();
        Ok(res)
    }

    /// Given an index anchor block hash, get the index microblock hash for a confirmed microblock stream.
    pub fn get_confirmed_microblock_index_hash(
        &self,
        child_index_block_hash: &StacksBlockId,
    ) -> Result<Option<StacksBlockId>, Error> {
        // get parent's consensus hash and block hash
        let (parent_consensus_hash, _) = match StacksChainState::get_parent_block_header_hashes(
            &self.db(),
            child_index_block_hash,
        )? {
            Some(x) => x,
            None => {
                test_debug!("No such block: {:?}", &child_index_block_hash);
                return Ok(None);
            }
        };

        // get the child's staging block info
        let child_block_info =
            match StacksChainState::load_staging_block_info(&self.db(), child_index_block_hash)? {
                Some(hdr) => hdr,
                None => {
                    test_debug!("No such block: {:?}", &child_index_block_hash);
                    return Ok(None);
                }
            };

        Ok(Some(StacksBlockHeader::make_index_block_hash(
            &parent_consensus_hash,
            &child_block_info.parent_microblock_hash,
        )))
    }

    /// Do we have any unconfirmed microblocks at or after the given sequence number that descend
    /// from the anchored block identified by the given parent_index_block_hash?
    /// Does not consider whether or not they are valid.
    /// Used mainly for paging through unconfirmed microblocks in the RPC interface.
    pub fn has_any_staging_microblock_indexed(
        &self,
        parent_index_block_hash: &StacksBlockId,
        min_seq: u16,
    ) -> Result<bool, Error> {
        StacksChainState::read_i64s(&self.db(), "SELECT processed FROM staging_microblocks WHERE index_block_hash = ?1 AND sequence >= ?2 LIMIT 1", &[&parent_index_block_hash, &min_seq])
            .and_then(|processed| Ok(processed.len() > 0))
    }

    /// Do we have a given microblock as a descendant of a given anchored block?
    /// Does not consider whether or not it has been processed or is orphaned.
    /// Used by the relayer to decide whether or not a microblock should be relayed.
    /// Used by the microblock-preprocessor to decide whether or not to store the microblock.
    pub fn has_descendant_microblock_indexed(
        &self,
        parent_index_block_hash: &StacksBlockId,
        microblock_hash: &BlockHeaderHash,
    ) -> Result<bool, Error> {
        StacksChainState::read_i64s(&self.db(), "SELECT processed FROM staging_microblocks WHERE index_block_hash = ?1 AND microblock_hash = ?2 LIMIT 1", &[parent_index_block_hash, microblock_hash])
            .and_then(|processed| Ok(processed.len() > 0))
    }

    /// Do we have any microblock available to serve in any capacity, given its parent anchored block's
    /// index block hash?
    #[cfg(test)]
    fn has_microblocks_indexed(
        &self,
        parent_index_block_hash: &StacksBlockId,
    ) -> Result<bool, Error> {
        StacksChainState::read_i64s(
            &self.db(),
            "SELECT processed FROM staging_microblocks WHERE index_block_hash = ?1 LIMIT 1",
            &[&parent_index_block_hash],
        )
        .and_then(|processed| Ok(processed.len() > 0))
    }

    /// Given an index block hash, get the consensus hash and block hash
    fn inner_get_block_header_hashes(
        blocks_db: &DBConn,
        index_block_hash: &StacksBlockId,
        consensus_hash_col: &str,
        anchored_block_col: &str,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash)>, Error> {
        let sql = format!(
            "SELECT {},{} FROM staging_blocks WHERE index_block_hash = ?1",
            consensus_hash_col, anchored_block_col
        );
        let args = [index_block_hash as &dyn ToSql];

        blocks_db
            .query_row(&sql, &args, |row| {
                let anchored_block_hash = BlockHeaderHash::from_column(row, anchored_block_col)
                    .expect("Expected anchored_block_hash - database corrupted");
                let consensus_hash = ConsensusHash::from_column(row, consensus_hash_col)
                    .expect("Expected consensus_hash - database corrupted");
                Ok((consensus_hash, anchored_block_hash))
            })
            .optional()
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))
    }

    /// Given an index block hash, get its consensus hash and block hash if it exists
    pub fn get_block_header_hashes(
        &self,
        index_block_hash: &StacksBlockId,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash)>, Error> {
        StacksChainState::inner_get_block_header_hashes(
            &self.db(),
            index_block_hash,
            "consensus_hash",
            "anchored_block_hash",
        )
    }

    /// Given an index block hash, get the parent consensus hash and block hash if it exists
    pub fn get_parent_block_header_hashes(
        blocks_conn: &DBConn,
        index_block_hash: &StacksBlockId,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash)>, Error> {
        StacksChainState::inner_get_block_header_hashes(
            blocks_conn,
            index_block_hash,
            "parent_consensus_hash",
            "parent_anchored_block_hash",
        )
    }

    /// Given an index microblock hash, get the microblock hash and its anchored block and
    /// consensus hash
    pub fn get_microblock_parent_header_hashes(
        blocks_conn: &DBConn,
        index_microblock_hash: &StacksBlockId,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash, BlockHeaderHash)>, Error> {
        let sql = format!("SELECT consensus_hash,anchored_block_hash,microblock_hash FROM staging_microblocks WHERE index_microblock_hash = ?1");
        let args = [index_microblock_hash as &dyn ToSql];

        blocks_conn
            .query_row(&sql, &args, |row| {
                let consensus_hash = ConsensusHash::from_column(row, "consensus_hash")
                    .expect("Expected consensus_hash - database corrupted");
                let anchored_block_hash = BlockHeaderHash::from_column(row, "anchored_block_hash")
                    .expect("Expected anchored_block_hash - database corrupted");
                let microblock_hash = BlockHeaderHash::from_column(row, "microblock_hash")
                    .expect("Expected microblock_hash - database corrupted");
                Ok((consensus_hash, anchored_block_hash, microblock_hash))
            })
            .optional()
            .map_err(|e| Error::DBError(db_error::SqliteError(e)))
    }

    /// Get the sqlite rowid for a staging microblock, given the hash of the microblock.
    /// Returns None if no such microblock.
    fn stream_microblock_get_rowid(
        blocks_conn: &DBConn,
        parent_index_block_hash: &StacksBlockId,
        microblock_hash: &BlockHeaderHash,
    ) -> Result<Option<i64>, Error> {
        let sql = "SELECT staging_microblocks_data.rowid FROM \
                   staging_microblocks JOIN staging_microblocks_data \
                   ON staging_microblocks.microblock_hash = staging_microblocks_data.block_hash \
                   WHERE staging_microblocks.index_block_hash = ?1 AND staging_microblocks.microblock_hash = ?2";
        let args = [
            parent_index_block_hash as &dyn ToSql,
            microblock_hash as &dyn ToSql,
        ];
        query_row(blocks_conn, sql, &args).map_err(Error::DBError)
    }

    /// Load up the metadata on a microblock stream (but don't get the data itself)
    /// DO NOT USE IN PRODUCTION -- doesn't work for microblock forks.
    #[cfg(test)]
    fn stream_microblock_get_info(
        blocks_conn: &DBConn,
        parent_index_block_hash: &StacksBlockId,
    ) -> Result<Vec<StagingMicroblock>, Error> {
        let sql = "SELECT * FROM staging_microblocks WHERE index_block_hash = ?1 ORDER BY sequence"
            .to_string();
        let args = [parent_index_block_hash as &dyn ToSql];
        let microblock_info =
            query_rows::<StagingMicroblock, _>(blocks_conn, &sql, &args).map_err(Error::DBError)?;
        Ok(microblock_info)
    }

    /// Stream data from one Read to one Write
    fn stream_data<W: Write, R: Read + Seek>(
        fd: &mut W,
        stream: &mut BlockStreamData,
        input: &mut R,
        count: u64,
    ) -> Result<u64, Error> {
        input
            .seek(SeekFrom::Start(stream.offset))
            .map_err(Error::ReadError)?;

        let mut buf = vec![0u8; count as usize];
        let nr = input.read(&mut buf).map_err(Error::ReadError)?;
        fd.write_all(&buf[0..nr]).map_err(Error::WriteError)?;

        stream.offset += nr as u64;
        stream.total_bytes += nr as u64;

        Ok(nr as u64)
    }

    /// Stream a single microblock's data from the staging database.
    /// If this method returns 0, it's because we're EOF on the blob.
    fn stream_one_microblock<W: Write>(
        blocks_conn: &DBConn,
        fd: &mut W,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<u64, Error> {
        let rowid = match stream.rowid {
            None => {
                // need to get rowid in order to get the blob
                match StacksChainState::stream_microblock_get_rowid(
                    blocks_conn,
                    &stream.parent_index_block_hash,
                    &stream.microblock_hash,
                )? {
                    Some(rid) => rid,
                    None => {
                        test_debug!("Microblock hash={:?} not in DB", &stream.microblock_hash,);
                        return Err(Error::NoSuchBlockError);
                    }
                }
            }
            Some(rid) => rid,
        };

        stream.rowid = Some(rowid);
        let mut blob = blocks_conn
            .blob_open(
                DatabaseName::Main,
                "staging_microblocks_data",
                "block_data",
                rowid,
                true,
            )
            .map_err(|e| {
                match e {
                    sqlite_error::SqliteFailure(_, _) => {
                        // blob got moved out of staging
                        Error::NoSuchBlockError
                    }
                    _ => Error::DBError(db_error::SqliteError(e)),
                }
            })?;

        let num_bytes = StacksChainState::stream_data(fd, stream, &mut blob, count)?;
        test_debug!(
            "Stream microblock rowid={} hash={} offset={} total_bytes={}, num_bytes={}",
            rowid,
            &stream.microblock_hash,
            stream.offset,
            stream.total_bytes,
            num_bytes
        );
        Ok(num_bytes)
    }

    /// Stream multiple microblocks from staging, moving in reverse order from the stream tail to the stream head.
    /// Returns total number of bytes written (will be equal to the number of bytes read).
    /// Returns 0 if we run out of microblocks in the staging db
    fn stream_microblocks_confirmed<W: Write>(
        chainstate: &StacksChainState,
        fd: &mut W,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<u64, Error> {
        let mut to_write = count;
        while to_write > 0 {
            let nw =
                StacksChainState::stream_one_microblock(&chainstate.db(), fd, stream, to_write)?;
            if nw == 0 {
                // EOF on microblock blob; move to the next one (its parent)
                let mblock_info = match StacksChainState::load_staging_microblock_info(
                    &chainstate.db(),
                    &stream.parent_index_block_hash,
                    &stream.microblock_hash,
                )? {
                    Some(x) => x,
                    None => {
                        // out of mblocks
                        debug!(
                            "Out of microblocks to stream after confirmed microblock {}",
                            &stream.microblock_hash
                        );
                        break;
                    }
                };

                let rowid = match StacksChainState::stream_microblock_get_rowid(
                    &chainstate.db(),
                    &stream.parent_index_block_hash,
                    &mblock_info.parent_hash,
                )? {
                    Some(rid) => rid,
                    None => {
                        // out of mblocks
                        debug!(
                            "No rowid found for confirmed stream microblock {}",
                            &mblock_info.parent_hash
                        );
                        break;
                    }
                };

                stream.offset = 0;
                stream.rowid = Some(rowid);
                stream.microblock_hash = mblock_info.parent_hash;
            } else {
                to_write = to_write
                    .checked_sub(nw)
                    .expect("BUG: wrote more data than called for");
            }
            debug!(
                "Streaming microblock={}: to_write={}, nw={}",
                &stream.microblock_hash, to_write, nw
            );
        }
        debug!(
            "Streamed confirmed microblocks: {} - {} = {}",
            count,
            to_write,
            count - to_write
        );
        Ok(count - to_write)
    }

    /// Stream block data from the chunk store.
    fn stream_data_from_chunk_store<W: Write>(
        blocks_path: &String,
        fd: &mut W,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<u64, Error> {
        let block_path =
            StacksChainState::get_index_block_path(blocks_path, &stream.index_block_hash)?;

        // The reason we open a file on each call to stream data is because we don't want to
        // exhaust the supply of file descriptors.  Maybe a future version of this code will do
        // something like cache the set of open files so we don't have to keep re-opening them.
        let mut file_fd = fs::OpenOptions::new()
            .read(true)
            .write(false)
            .create(false)
            .truncate(false)
            .open(&block_path)
            .map_err(|e| {
                if e.kind() == io::ErrorKind::NotFound {
                    error!("File not found: {:?}", &block_path);
                    Error::NoSuchBlockError
                } else {
                    Error::ReadError(e)
                }
            })?;

        StacksChainState::stream_data(fd, stream, &mut file_fd, count)
    }

    /// Stream block data from the chain state.
    /// Returns the number of bytes written, and updates `stream` to point to the next point to
    /// read.  Writes the bytes streamed to `fd`.
    pub fn stream_block<W: Write>(
        &mut self,
        fd: &mut W,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<u64, Error> {
        StacksChainState::stream_data_from_chunk_store(&self.blocks_path, fd, stream, count)
    }

    /// Stream unconfirmed microblocks from the staging DB.  Pull only from the staging DB.
    /// Returns the number of bytes written, and updates `stream` to point to the next point to
    /// read.  Wrties the bytes streamed to `fd`.
    pub fn stream_microblocks_unconfirmed<W: Write>(
        chainstate: &StacksChainState,
        fd: &mut W,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<u64, Error> {
        let mut to_write = count;
        while to_write > 0 {
            let nw =
                StacksChainState::stream_one_microblock(&chainstate.db(), fd, stream, to_write)?;
            if nw == 0 {
                // EOF on microblock blob; move to the next one
                let next_seq = match stream.seq {
                    u16::MAX => {
                        return Err(Error::NoSuchBlockError);
                    }
                    x => x + 1,
                };
                let next_mblock_hash = match StacksChainState::load_next_descendant_microblock(
                    &chainstate.db(),
                    &stream.index_block_hash,
                    next_seq,
                )? {
                    Some(mblock) => {
                        test_debug!(
                            "Switch to {}-{} ({})",
                            &stream.index_block_hash,
                            &mblock.block_hash(),
                            next_seq
                        );
                        mblock.block_hash()
                    }
                    None => {
                        // EOF on stream
                        break;
                    }
                };

                let rowid = match StacksChainState::stream_microblock_get_rowid(
                    &chainstate.db(),
                    &stream.parent_index_block_hash,
                    &next_mblock_hash,
                )? {
                    Some(rid) => rid,
                    None => {
                        // out of mblocks
                        break;
                    }
                };

                stream.offset = 0;
                stream.rowid = Some(rowid);
                stream.microblock_hash = next_mblock_hash;
                stream.seq = next_seq;
            } else {
                to_write = to_write
                    .checked_sub(nw)
                    .expect("BUG: wrote more data than called for");
            }
        }
        Ok(count - to_write)
    }

    fn extract_signed_microblocks(
        parent_anchored_block_header: &StacksBlockHeader,
        microblocks: &Vec<StacksMicroblock>,
    ) -> Vec<StacksMicroblock> {
        let mut signed_microblocks = vec![];
        for microblock in microblocks.iter() {
            let mut dup = microblock.clone();
            if dup
                .verify(&parent_anchored_block_header.microblock_pubkey_hash)
                .is_err()
            {
                warn!(
                    "Microblock {} not signed by {}",
                    microblock.block_hash(),
                    parent_anchored_block_header.microblock_pubkey_hash
                );
                continue;
            }
            signed_microblocks.push(microblock.clone());
        }
        signed_microblocks
    }

    /// Given a microblock stream, does it connect the parent and child anchored blocks?
    /// * verify that the blocks are a contiguous sequence, with no duplicate sequence numbers
    /// * verify that each microblock is signed by the parent anchor block's key
    /// The stream must be in order by sequence number, and there must be no duplicates.
    /// If the stream connects to the anchored block, then
    /// return the index in the given microblocks vec that corresponds to the highest valid
    /// block -- i.e. the microblock indicated by the anchored header as the parent.
    /// If there was a duplicate sequence number, then also return a poison-microblock
    /// transaction for the two headers with the lowest duplicate sequence number.
    /// Return None if the stream does not connect to this block (e.g. it's incomplete or the like)
    pub fn validate_parent_microblock_stream(
        parent_anchored_block_header: &StacksBlockHeader,
        anchored_block_header: &StacksBlockHeader,
        microblocks: &Vec<StacksMicroblock>,
        verify_signatures: bool,
    ) -> Option<(usize, Option<TransactionPayload>)> {
        if anchored_block_header.is_first_mined() {
            // there had better be zero microblocks
            if anchored_block_header.parent_microblock == EMPTY_MICROBLOCK_PARENT_HASH
                && anchored_block_header.parent_microblock_sequence == 0
            {
                return Some((0, None));
            } else {
                warn!(
                    "Block {} has no ancestor, and should have no microblock parents",
                    anchored_block_header.block_hash()
                );
                return None;
            }
        }

        let signed_microblocks = if verify_signatures {
            StacksChainState::extract_signed_microblocks(&parent_anchored_block_header, microblocks)
        } else {
            microblocks.clone()
        };

        if signed_microblocks.len() == 0 {
            if anchored_block_header.parent_microblock == EMPTY_MICROBLOCK_PARENT_HASH
                && anchored_block_header.parent_microblock_sequence == 0
            {
                // expected empty
                debug!(
                    "No microblocks between {} and {}",
                    parent_anchored_block_header.block_hash(),
                    anchored_block_header.block_hash()
                );
                return Some((0, None));
            } else {
                // did not expect empty
                warn!(
                    "Missing microblocks between {} and {}",
                    parent_anchored_block_header.block_hash(),
                    anchored_block_header.block_hash()
                );
                return None;
            }
        }

        if signed_microblocks[0].header.sequence != 0 {
            // discontiguous -- must start with seq 0
            warn!(
                "Discontiguous stream -- first microblock header sequence is {}",
                signed_microblocks[0].header.sequence
            );
            return None;
        }

        if signed_microblocks[0].header.prev_block != parent_anchored_block_header.block_hash() {
            // discontiguous -- not connected to parent
            warn!("Discontiguous stream -- does not connect to parent");
            return None;
        }

        // sanity check -- in order by sequence and no sequence duplicates
        for i in 1..signed_microblocks.len() {
            if signed_microblocks[i - 1].header.sequence > signed_microblocks[i].header.sequence {
                panic!("BUG: out-of-sequence microblock stream");
            }
            let cur_seq = (signed_microblocks[i - 1].header.sequence as u32) + 1;
            if cur_seq < (signed_microblocks[i].header.sequence as u32) {
                // discontiguous
                warn!(
                    "Discontiguous stream -- {} < {}",
                    cur_seq, signed_microblocks[i].header.sequence
                );
                return None;
            }
        }

        // sanity check -- all parent block hashes are unique.  If there are duplicates, then the
        // miner equivocated.
        let mut parent_hashes: HashMap<BlockHeaderHash, StacksMicroblockHeader> = HashMap::new();
        for i in 0..signed_microblocks.len() {
            let signed_microblock = &signed_microblocks[i];
            if parent_hashes.contains_key(&signed_microblock.header.prev_block) {
                debug!(
                    "Deliberate microblock fork: duplicate parent {}",
                    signed_microblock.header.prev_block
                );
                let conflicting_microblock_header = parent_hashes
                    .get(&signed_microblock.header.prev_block)
                    .unwrap();

                return Some((
                    i - 1,
                    Some(TransactionPayload::PoisonMicroblock(
                        signed_microblock.header.clone(),
                        conflicting_microblock_header.clone(),
                    )),
                ));
            }
            parent_hashes.insert(
                signed_microblock.header.prev_block.clone(),
                signed_microblock.header.clone(),
            );
        }

        // hashes are contiguous enough -- for each seqnum, there is a microblock with seqnum+1 with the
        // microblock at seqnum as its parent.  There may be more than one.
        for i in 1..signed_microblocks.len() {
            if signed_microblocks[i - 1].header.sequence == signed_microblocks[i].header.sequence
                && signed_microblocks[i - 1].block_hash() != signed_microblocks[i].block_hash()
            {
                // deliberate microblock fork
                debug!(
                    "Deliberate microblock fork at sequence {}",
                    signed_microblocks[i - 1].header.sequence
                );
                return Some((
                    i - 1,
                    Some(TransactionPayload::PoisonMicroblock(
                        signed_microblocks[i - 1].header.clone(),
                        signed_microblocks[i].header.clone(),
                    )),
                ));
            }

            if signed_microblocks[i - 1].block_hash() != signed_microblocks[i].header.prev_block {
                // discontiguous
                debug!("Discontinuous stream -- blocks not linked by hash");
                return None;
            }
        }

        if anchored_block_header.parent_microblock == EMPTY_MICROBLOCK_PARENT_HASH
            && anchored_block_header.parent_microblock_sequence == 0
        {
            // expected empty
            debug!(
                "Empty microblock stream between {} and {}",
                parent_anchored_block_header.block_hash(),
                anchored_block_header.block_hash()
            );
            return Some((0, None));
        }

        let mut end = 0;
        let mut connects = false;
        for i in 0..signed_microblocks.len() {
            if signed_microblocks[i].block_hash() == anchored_block_header.parent_microblock {
                end = i + 1;
                connects = true;
                break;
            }
        }

        if !connects {
            // discontiguous
            debug!(
                "Discontiguous stream: block {} does not connect to tail",
                anchored_block_header.block_hash()
            );
            return None;
        }

        return Some((end, None));
    }

    /// Validate an anchored block against the burn chain state.
    /// Returns Some(commit burn, total burn) if valid
    /// Returns None if not valid
    /// * consensus_hash is the PoX history hash of the burnchain block whose sortition
    /// (ostensibly) selected this block for inclusion.
    fn validate_anchored_block_burnchain(
        db_handle: &SortitionHandleConn,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
        mainnet: bool,
        chain_id: u32,
    ) -> Result<Option<(u64, u64)>, Error> {
        // sortition-winning block commit for this block?
        let block_hash = block.block_hash();
        let (block_commit, stacks_chain_tip) = match db_handle
            .get_block_snapshot_of_parent_stacks_block(consensus_hash, &block_hash)
        {
            Ok(Some(bc)) => bc,
            Ok(None) => {
                // unsoliciated
                warn!(
                    "Received unsolicited block: {}/{}",
                    consensus_hash, block_hash
                );
                return Ok(None);
            }
            Err(db_error::InvalidPoxSortition) => {
                warn!(
                    "Received unsolicited block on non-canonical PoX fork: {}/{}",
                    consensus_hash, block_hash
                );
                return Ok(None);
            }
            Err(e) => {
                return Err(e.into());
            }
        };

        // burn chain tip that selected this commit's block
        let burn_chain_tip = db_handle
            .get_block_snapshot(&block_commit.burn_header_hash)?
            .expect("FATAL: have block commit but no block snapshot");

        // this is the penultimate burnchain snapshot with the VRF seed that this
        // block's miner had to prove on to generate the block-commit and block itself.
        let penultimate_sortition_snapshot = db_handle
            .get_block_snapshot_by_height(block_commit.block_height - 1)?
            .expect("FATAL: have block commit but no sortition snapshot");

        // key of the winning leader
        let leader_key = db_handle
            .get_leader_key_at(
                block_commit.key_block_ptr as u64,
                block_commit.key_vtxindex as u32,
            )?
            .expect("FATAL: have block commit but no leader key");

        // attaches to burn chain
        match block.header.validate_burnchain(
            &burn_chain_tip,
            &penultimate_sortition_snapshot,
            &leader_key,
            &block_commit,
            &stacks_chain_tip,
        ) {
            Ok(_) => {}
            Err(_) => {
                warn!(
                    "Invalid block, could not validate on burnchain: {}/{}",
                    consensus_hash, block_hash
                );

                return Ok(None);
            }
        };

        // static checks on transactions all pass
        let valid = block.validate_transactions_static(mainnet, chain_id);
        if !valid {
            warn!(
                "Invalid block, transactions failed static checks: {}/{}",
                consensus_hash, block_hash
            );
            return Ok(None);
        }

        let sortition_burns =
            SortitionDB::get_block_burn_amount(db_handle, &penultimate_sortition_snapshot)
                .expect("FATAL: have block commit but no total burns in its sortition");

        Ok(Some((block_commit.burn_fee, sortition_burns)))
    }

    /// Pre-process and store an anchored block to staging, queuing it up for
    /// subsequent processing once all of its ancestors have been processed.
    ///
    /// Caller must have called SortitionDB::expects_stacks_block() to determine if this block belongs
    /// to the blockchain.  The consensus_hash is the hash of the burnchain block whose sortition
    /// elected the given Stacks block.
    ///
    /// If we find the same Stacks block in two or more burnchain forks, insert it there too
    ///
    /// sort_ic: an indexed connection to a sortition DB
    /// consensus_hash: this is the consensus hash of the sortition that chose this block
    /// block: the actual block data for this anchored Stacks block
    /// parent_consensus_hash: this the consensus hash of the sortition that chose this Stack's block's parent
    pub fn preprocess_anchored_block(
        &mut self,
        sort_ic: &SortitionDBConn,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
        parent_consensus_hash: &ConsensusHash,
        download_time: u64,
    ) -> Result<bool, Error> {
        debug!(
            "preprocess anchored block {}/{}",
            consensus_hash,
            block.block_hash()
        );

        let sort_handle = SortitionHandleConn::open_reader_consensus(sort_ic, consensus_hash)?;

        let mainnet = self.mainnet;
        let chain_id = self.chain_id;
        let blocks_path = self.blocks_path.clone();
        let mut block_tx = self.db_tx_begin()?;

        // already in queue or already processed?
        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(consensus_hash, &block.block_hash());
        if StacksChainState::has_stored_block(
            &block_tx,
            &blocks_path,
            consensus_hash,
            &block.block_hash(),
        )? {
            debug!(
                "Block already stored and processed: {}/{} ({})",
                consensus_hash,
                &block.block_hash(),
                &index_block_hash
            );
            return Ok(false);
        } else if StacksChainState::has_staging_block(
            &block_tx,
            consensus_hash,
            &block.block_hash(),
        )? {
            debug!(
                "Block already stored (but not processed): {}/{} ({})",
                consensus_hash,
                &block.block_hash(),
                &index_block_hash
            );
            return Ok(false);
        } else if StacksChainState::has_valid_block_indexed(&blocks_path, &index_block_hash)? {
            debug!(
                "Block already stored to chunk store: {}/{} ({})",
                consensus_hash,
                &block.block_hash(),
                &index_block_hash
            );
            return Ok(false);
        }

        // find all user burns that supported this block
        let user_burns = sort_handle.get_winning_user_burns_by_block()?;

        // does this block match the burnchain state? skip if not
        let validation_res = StacksChainState::validate_anchored_block_burnchain(
            &sort_handle,
            consensus_hash,
            block,
            mainnet,
            chain_id,
        )?;
        let (commit_burn, sortition_burn) = match validation_res {
            Some((commit_burn, sortition_burn)) => (commit_burn, sortition_burn),
            None => {
                let msg = format!(
                    "Invalid block {}: does not correspond to burn chain state",
                    block.block_hash()
                );
                warn!("{}", &msg);

                // orphan it
                StacksChainState::set_block_processed(
                    &mut block_tx,
                    None,
                    &blocks_path,
                    consensus_hash,
                    &block.block_hash(),
                    false,
                )?;

                block_tx.commit()?;
                return Err(Error::InvalidStacksBlock(msg));
            }
        };

        debug!("Storing staging block");

        // queue block up for processing
        StacksChainState::store_staging_block(
            &mut block_tx,
            &blocks_path,
            consensus_hash,
            &block,
            parent_consensus_hash,
            commit_burn,
            sortition_burn,
            download_time,
        )?;

        // store users who burned for this block so they'll get rewarded if we process it
        StacksChainState::store_staging_block_user_burn_supports(
            &mut block_tx,
            consensus_hash,
            &block.block_hash(),
            &user_burns,
        )?;

        block_tx.commit()?;

        // ready to go
        Ok(true)
    }

    /// Pre-process and store a microblock to staging, queueing it up for subsequent processing
    /// once all of its ancestors have been processed.
    ///
    /// The anchored block this microblock builds off of must have already been stored somewhere,
    /// staging or accepted, so we can verify the signature over this block.
    ///
    /// This method is `&mut self` to ensure that concurrent renames don't corrupt our chain state.
    ///
    /// If we find the same microblock in multiple burnchain forks, insert it into both.
    ///
    /// Return true if we stored the microblock.
    /// Return false if we did not store it (i.e. we already had it, we don't have its parent)
    /// Return Err(..) if the microblock is invalid, or we couldn't process it
    pub fn preprocess_streamed_microblock(
        &mut self,
        parent_consensus_hash: &ConsensusHash,
        parent_anchored_block_hash: &BlockHeaderHash,
        microblock: &StacksMicroblock,
    ) -> Result<bool, Error> {
        debug!(
            "preprocess microblock {}/{}-{}, parent {}",
            parent_consensus_hash,
            parent_anchored_block_hash,
            microblock.block_hash(),
            microblock.header.prev_block
        );

        let parent_index_hash = StacksBlockHeader::make_index_block_hash(
            parent_consensus_hash,
            parent_anchored_block_hash,
        );

        // already queued or already processed?
        if self.has_descendant_microblock_indexed(&parent_index_hash, &microblock.block_hash())? {
            debug!(
                "Microblock already stored and/or processed: {}/{} {} {}",
                parent_consensus_hash,
                &parent_anchored_block_hash,
                microblock.block_hash(),
                microblock.header.sequence
            );

            // try to process it nevertheless
            return Ok(false);
        }

        let mainnet = self.mainnet;
        let chain_id = self.chain_id;
        let blocks_path = self.blocks_path.clone();

        let mut blocks_tx = self.db_tx_begin()?;

        let pubkey_hash = if let Some(pubkh) = StacksChainState::load_block_pubkey_hash(
            &blocks_tx,
            &blocks_path,
            parent_consensus_hash,
            parent_anchored_block_hash,
        )? {
            pubkh
        } else {
            // don't have the parent
            return Ok(false);
        };

        let mut dup = microblock.clone();
        if let Err(e) = dup.verify(&pubkey_hash) {
            let msg = format!(
                "Invalid microblock {}: failed to verify signature with {}: {:?}",
                microblock.block_hash(),
                pubkey_hash,
                &e
            );
            warn!("{}", &msg);
            return Err(Error::InvalidStacksMicroblock(msg, microblock.block_hash()));
        }

        // static checks on transactions all pass
        let valid = microblock.validate_transactions_static(mainnet, chain_id);
        if !valid {
            let msg = format!(
                "Invalid microblock {}: one or more transactions failed static tests",
                microblock.block_hash()
            );
            warn!("{}", &msg);
            return Err(Error::InvalidStacksMicroblock(msg, microblock.block_hash()));
        }

        // add to staging
        StacksChainState::store_staging_microblock(
            &mut blocks_tx,
            parent_consensus_hash,
            parent_anchored_block_hash,
            microblock,
        )?;

        blocks_tx.commit()?;

        Ok(true)
    }

    /// Given a burnchain snapshot, a Stacks block and a microblock stream, preprocess them all.
    /// This does not work when forking
    #[cfg(test)]
    pub fn preprocess_stacks_epoch(
        &mut self,
        sort_ic: &SortitionDBConn,
        snapshot: &BlockSnapshot,
        block: &StacksBlock,
        microblocks: &Vec<StacksMicroblock>,
    ) -> Result<(), Error> {
        let parent_sn = {
            let db_handle = sort_ic.as_handle(&snapshot.sortition_id);
            let sn = match db_handle.get_block_snapshot(&snapshot.parent_burn_header_hash)? {
                Some(sn) => sn,
                None => {
                    return Err(Error::NoSuchBlockError);
                }
            };
            sn
        };

        self.preprocess_anchored_block(
            sort_ic,
            &snapshot.consensus_hash,
            block,
            &parent_sn.consensus_hash,
            5,
        )?;
        let block_hash = block.block_hash();
        for mblock in microblocks.iter() {
            self.preprocess_streamed_microblock(&snapshot.consensus_hash, &block_hash, mblock)?;
        }
        Ok(())
    }

    /// Get the coinbase at this burn block height, in microSTX
    pub fn get_coinbase_reward(burn_block_height: u64, first_burn_block_height: u64) -> u128 {
        /*
        From https://forum.stacks.org/t/pox-consensus-and-stx-future-supply

        """

        1000 STX for years 0-4
        500 STX for years 4-8
        250 STX for years 8-12
        125 STX in perpetuity


        From the Token Whitepaper:

        We expect that once native mining goes live, approximately 4383 blocks will be pro-
        cessed per month, or approximately 52,596 blocks will be processed per year.

        """
        */
        // this is saturating subtraction for the initial reward calculation
        //   where we are computing the coinbase reward for blocks that occur *before*
        //   the `first_burn_block_height`
        let effective_ht = burn_block_height.saturating_sub(first_burn_block_height);
        let blocks_per_year = 52596;
        let stx_reward = if effective_ht < blocks_per_year * 4 {
            1000
        } else if effective_ht < blocks_per_year * 8 {
            500
        } else if effective_ht < blocks_per_year * 12 {
            250
        } else {
            125
        };

        stx_reward * (MICROSTACKS_PER_STACKS as u128)
    }

    /// Create the block reward.
    /// `coinbase_reward_ustx` is the total coinbase reward for this block, including any
    ///    accumulated rewards from missed sortitions or initial mining rewards.
    fn make_scheduled_miner_reward(
        mainnet: bool,
        parent_block_hash: &BlockHeaderHash,
        parent_consensus_hash: &ConsensusHash,
        block: &StacksBlock,
        block_consensus_hash: &ConsensusHash,
        block_height: u64,
        anchored_fees: u128,
        streamed_fees: u128,
        stx_burns: u128,
        burnchain_commit_burn: u64,
        burnchain_sortition_burn: u64,
        coinbase_reward_ustx: u128,
    ) -> Result<MinerPaymentSchedule, Error> {
        let coinbase_tx = block.get_coinbase_tx().ok_or(Error::InvalidStacksBlock(
            "No coinbase transaction".to_string(),
        ))?;
        let miner_auth = coinbase_tx.get_origin();
        let miner_addr = if mainnet {
            miner_auth.address_mainnet()
        } else {
            miner_auth.address_testnet()
        };

        let miner_reward = MinerPaymentSchedule {
            address: miner_addr,
            block_hash: block.block_hash(),
            consensus_hash: block_consensus_hash.clone(),
            parent_block_hash: parent_block_hash.clone(),
            parent_consensus_hash: parent_consensus_hash.clone(),
            coinbase: coinbase_reward_ustx,
            tx_fees_anchored: anchored_fees,
            tx_fees_streamed: streamed_fees,
            stx_burns: stx_burns,
            burnchain_commit_burn: burnchain_commit_burn,
            burnchain_sortition_burn: burnchain_sortition_burn,
            miner: true,
            stacks_block_height: block_height,
            vtxindex: 0,
        };

        Ok(miner_reward)
    }

    /// Given a staging block, load up its parent microblock stream from staging.
    /// All of the parent anchored block's microblocks will be loaded, if we have them and they're
    /// not orphaned.
    /// Return Ok(Some(microblocks)) if we got microblocks (even if it's an empty stream)
    /// Return Ok(None) if there are no staging microblocks yet
    fn find_parent_microblock_stream(
        blocks_conn: &DBConn,
        staging_block: &StagingBlock,
    ) -> Result<Option<Vec<StacksMicroblock>>, Error> {
        if staging_block.parent_microblock_hash == EMPTY_MICROBLOCK_PARENT_HASH
            && staging_block.parent_microblock_seq == 0
        {
            // no parent microblocks, ever
            return Ok(Some(vec![]));
        }

        // find the microblock stream fork that this block confirms
        match StacksChainState::load_microblock_stream_fork(
            blocks_conn,
            &staging_block.parent_consensus_hash,
            &staging_block.parent_anchored_block_hash,
            &staging_block.parent_microblock_hash,
        )? {
            Some(microblocks) => {
                return Ok(Some(microblocks));
            }
            None => {
                // parent microblocks haven't arrived yet, or there are none
                debug!(
                    "No parent microblock stream for {}: expected a stream with tail {},{}",
                    staging_block.anchored_block_hash,
                    staging_block.parent_microblock_hash,
                    staging_block.parent_microblock_seq
                );
                return Ok(None);
            }
        }
    }

    /// Find a block that we accepted to staging, but had a parent that we ended up
    /// rejecting.  Garbage-collect its data.
    /// Call this method repeatedly to remove long chains of orphaned blocks and microblocks from
    /// staging.
    /// Returns true if an orphan block was processed
    fn process_next_orphaned_staging_block<'a>(
        blocks_tx: &mut DBTx<'a>,
        blocks_path: &String,
    ) -> Result<bool, Error> {
        test_debug!("Find next orphaned block");

        // go through staging blocks and see if any of them have not been processed yet, but are
        // orphaned
        let sql = "SELECT * FROM staging_blocks WHERE processed = 0 AND orphaned = 1 ORDER BY RANDOM() LIMIT 1";
        let mut rows =
            query_rows::<StagingBlock, _>(blocks_tx, sql, NO_PARAMS).map_err(Error::DBError)?;
        if rows.len() == 0 {
            test_debug!("No orphans to remove");
            return Ok(false);
        }

        let orphan_block = rows.pop().unwrap();

        test_debug!(
            "Delete orphaned block {}/{} and its microblocks, and orphan its children",
            &orphan_block.consensus_hash,
            &orphan_block.anchored_block_hash
        );

        StacksChainState::delete_orphaned_epoch_data(
            blocks_tx,
            blocks_path,
            &orphan_block.consensus_hash,
            &orphan_block.anchored_block_hash,
        )?;
        Ok(true)
    }

    /// How many attachable staging blocks do we have, up to a limit, at or after the given
    /// timestamp?
    pub fn count_attachable_staging_blocks(
        blocks_conn: &DBConn,
        limit: u64,
        min_arrival_time: u64,
    ) -> Result<u64, Error> {
        let sql = "SELECT COUNT(*) FROM staging_blocks WHERE processed = 0 AND attachable = 1 AND orphaned = 0 AND arrival_time >= ?1 LIMIT ?2".to_string();
        let cnt = query_count(
            blocks_conn,
            &sql,
            &[&u64_to_sql(min_arrival_time)?, &u64_to_sql(limit)?],
        )
        .map_err(Error::DBError)?;
        Ok(cnt as u64)
    }

    /// How many processed staging blocks do we have, up to a limit, at or after the given
    /// timestamp?
    pub fn count_processed_staging_blocks(
        blocks_conn: &DBConn,
        limit: u64,
        min_arrival_time: u64,
    ) -> Result<u64, Error> {
        let sql = "SELECT COUNT(*) FROM staging_blocks WHERE processed = 1 AND orphaned = 0 AND processed_time > 0 AND processed_time >= ?1 LIMIT ?2".to_string();
        let cnt = query_count(
            blocks_conn,
            &sql,
            &[&u64_to_sql(min_arrival_time)?, &u64_to_sql(limit)?],
        )
        .map_err(Error::DBError)?;
        Ok(cnt as u64)
    }

    /// Measure how long a block waited in-between when it arrived and when it got processed.
    /// Includes both orphaned and accepted blocks.
    pub fn measure_block_wait_time(
        blocks_conn: &DBConn,
        start_height: u64,
        end_height: u64,
    ) -> Result<Vec<i64>, Error> {
        let sql = "SELECT processed_time - arrival_time FROM staging_blocks WHERE processed = 1 AND height >= ?1 AND height < ?2";
        let args: &[&dyn ToSql] = &[&u64_to_sql(start_height)?, &u64_to_sql(end_height)?];
        let list = query_rows::<i64, _>(blocks_conn, &sql, args)?;
        Ok(list)
    }

    /// Measure how long a block took to be downloaded (for blocks that we downloaded).
    /// Includes _all_ blocks.
    pub fn measure_block_download_time(
        blocks_conn: &DBConn,
        start_height: u64,
        end_height: u64,
    ) -> Result<Vec<i64>, Error> {
        let sql = "SELECT download_time FROM staging_blocks WHERE height >= ?1 AND height < ?2";
        let args: &[&dyn ToSql] = &[&u64_to_sql(start_height)?, &u64_to_sql(end_height)?];
        let list = query_rows::<i64, _>(blocks_conn, &sql, args)?;
        Ok(list)
    }

    /// Given access to the chain state (headers) and the staging blocks, find a staging block we
    /// can process, as well as its parent microblocks that it confirms
    /// Returns Some(microblocks, staging block) if we found a sequence of blocks to process.
    /// Returns None if not.
    fn find_next_staging_block<'a>(
        blocks_tx: &mut StacksDBTx<'a>,
        blocks_path: &String,
        sort_tx: &mut SortitionHandleTx,
    ) -> Result<Option<(Vec<StacksMicroblock>, StagingBlock)>, Error> {
        test_debug!("Find next staging block");

        let mut to_delete = vec![];

        // put this in a block so stmt goes out of scope before we start to delete PoX-orphaned
        // blocks
        {
            // go through staging blocks and see if any of them match headers, are attachable, and are
            // recent (i.e. less than 10 minutes old)
            // pick randomly -- don't allow the network sender to choose the processing order!
            let sql = "SELECT * FROM staging_blocks WHERE processed = 0 AND attachable = 1 AND orphaned = 0 ORDER BY RANDOM()".to_string();
            let mut stmt = blocks_tx
                .prepare(&sql)
                .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

            let mut rows = stmt
                .query(NO_PARAMS)
                .map_err(|e| Error::DBError(db_error::SqliteError(e)))?;

            while let Some(row) = rows.next().map_err(|e| db_error::SqliteError(e))? {
                let mut candidate = StagingBlock::from_row(&row).map_err(Error::DBError)?;

                // block must correspond to a valid PoX snapshot
                let sn_opt =
                    SortitionDB::get_block_snapshot_consensus(sort_tx, &candidate.consensus_hash)?;
                if sn_opt.is_none() {
                    info!(
                        "Block {}/{} does not correspond to a sortition",
                        &candidate.consensus_hash, &candidate.anchored_block_hash
                    );
                    to_delete.push((
                        candidate.consensus_hash.clone(),
                        candidate.anchored_block_hash.clone(),
                    ));
                    continue;
                } else if let Some(sn) = sn_opt {
                    if !sn.pox_valid {
                        info!(
                            "Block {}/{} corresponds to an invalid PoX sortition",
                            &candidate.consensus_hash, &candidate.anchored_block_hash
                        );
                        to_delete.push((
                            candidate.consensus_hash.clone(),
                            candidate.anchored_block_hash.clone(),
                        ));
                        continue;
                    }
                }

                debug!(
                    "Consider block {}/{} whose parent is {}/{} with {} parent microblocks tailed at {}",
                    &candidate.consensus_hash,
                    &candidate.anchored_block_hash,
                    &candidate.parent_consensus_hash,
                    &candidate.parent_anchored_block_hash,
                    if candidate.parent_microblock_hash != BlockHeaderHash([0u8; 32]) { (candidate.parent_microblock_seq as u32) + 1 } else { 0 },
                    &candidate.parent_microblock_hash
                );

                let can_attach = {
                    if candidate.parent_anchored_block_hash == FIRST_STACKS_BLOCK_HASH {
                        // this block's parent is the boot code -- it's the first-ever block,
                        // so it can be processed immediately
                        true
                    } else {
                        // not the first-ever block.  Does this connect to a previously-accepted
                        // block in the headers database?
                        let hdr_sql = "SELECT * FROM block_headers WHERE block_hash = ?1 AND consensus_hash = ?2".to_string();
                        let hdr_args: &[&dyn ToSql] = &[
                            &candidate.parent_anchored_block_hash,
                            &candidate.parent_consensus_hash,
                        ];
                        let hdr_row = query_row_panic::<StacksHeaderInfo, _, _>(
                            blocks_tx,
                            &hdr_sql,
                            hdr_args,
                            || {
                                format!(
                                    "Stored the same block twice: {}/{}",
                                    &candidate.parent_anchored_block_hash,
                                    &candidate.parent_consensus_hash
                                )
                            },
                        )?;
                        match hdr_row {
                            Some(_) => {
                                debug!(
                                    "Have parent {}/{} for this block, will process",
                                    &candidate.parent_consensus_hash,
                                    &candidate.parent_anchored_block_hash
                                );
                                true
                            }
                            None => {
                                // no parent processed for this block
                                debug!(
                                    "No such parent {}/{} for block, cannot process",
                                    &candidate.parent_consensus_hash,
                                    &candidate.parent_anchored_block_hash
                                );
                                false
                            }
                        }
                    }
                };

                if can_attach {
                    // load up the block data
                    candidate.block_data = match StacksChainState::load_block_bytes(
                        blocks_path,
                        &candidate.consensus_hash,
                        &candidate.anchored_block_hash,
                    )? {
                        Some(bytes) => {
                            if bytes.len() == 0 {
                                error!(
                                    "CORRUPTION: No block data for {}/{}",
                                    &candidate.consensus_hash, &candidate.anchored_block_hash
                                );
                                panic!();
                            }
                            bytes
                        }
                        None => {
                            error!(
                                "CORRUPTION: No block data for {}/{}",
                                &candidate.consensus_hash, &candidate.anchored_block_hash
                            );
                            panic!();
                        }
                    };

                    // find its microblock parent stream
                    match StacksChainState::find_parent_microblock_stream(blocks_tx, &candidate)? {
                        Some(parent_staging_microblocks) => {
                            return Ok(Some((parent_staging_microblocks, candidate)));
                        }
                        None => {
                            // no microblock data yet, so we can't process this block
                            continue;
                        }
                    }
                }
            }
        }

        for (consensus_hash, anchored_block_hash) in to_delete.into_iter() {
            info!("Orphan {}/{}: it does not connect to a previously-accepted block, because its consensus hash does not match an existing snapshot on the valid PoX fork.", &consensus_hash, &anchored_block_hash);
            let _ = StacksChainState::set_block_processed(
                blocks_tx,
                None,
                blocks_path,
                &consensus_hash,
                &anchored_block_hash,
                false,
            )
            .map_err(|e| {
                warn!(
                    "Failed to orphan {}/{}: {:?}",
                    &consensus_hash, &anchored_block_hash, &e
                );
                e
            });
        }

        // no blocks available
        Ok(None)
    }

    /// Process a stream of microblocks
    /// Return the fees and burns.
    pub fn process_microblocks_transactions(
        clarity_tx: &mut ClarityTx,
        microblocks: &Vec<StacksMicroblock>,
    ) -> Result<(u128, u128, Vec<StacksTransactionReceipt>), (Error, BlockHeaderHash)> {
        let mut fees = 0u128;
        let mut burns = 0u128;
        let mut receipts = vec![];
        for microblock in microblocks.iter() {
            debug!("Process microblock {}", &microblock.block_hash());
            for tx in microblock.txs.iter() {
                let (tx_fee, mut tx_receipt) =
                    StacksChainState::process_transaction(clarity_tx, tx, false)
                        .map_err(|e| (e, microblock.block_hash()))?;

                tx_receipt.microblock_header = Some(microblock.header.clone());
                fees = fees.checked_add(tx_fee as u128).expect("Fee overflow");
                burns = burns
                    .checked_add(tx_receipt.stx_burned as u128)
                    .expect("Burns overflow");
                receipts.push(tx_receipt);
            }
        }
        Ok((fees, burns, receipts))
    }

    /// Process any Stacking-related bitcoin operations
    ///  that haven't been processed in this Stacks fork yet.
    pub fn process_stacking_ops(
        clarity_tx: &mut ClarityTx,
        operations: Vec<StackStxOp>,
    ) -> Vec<StacksTransactionReceipt> {
        let mut all_receipts = vec![];
        let mainnet = clarity_tx.config.mainnet;
        let mut cost_so_far = clarity_tx.cost_so_far();
        for stack_stx_op in operations.into_iter() {
            let StackStxOp {
                sender,
                reward_addr,
                stacked_ustx,
                num_cycles,
                block_height,
                txid,
                burn_header_hash,
                ..
            } = stack_stx_op;
            let result = clarity_tx.connection().as_transaction(|tx| {
                tx.run_contract_call(
                    &sender.into(),
                    None,
                    &boot_code_id("pox", mainnet),
                    "stack-stx",
                    &[
                        Value::UInt(stacked_ustx),
                        reward_addr.as_clarity_tuple().into(),
                        Value::UInt(u128::from(block_height)),
                        Value::UInt(u128::from(num_cycles)),
                    ],
                    |_, _| false,
                )
            });
            match result {
                Ok((value, _, events)) => {
                    if let Value::Response(ref resp) = value {
                        if !resp.committed {
                            debug!("StackStx burn op rejected by PoX contract.";
                                   "txid" => %txid,
                                   "burn_block" => %burn_header_hash,
                                   "contract_call_ecode" => %resp.data);
                        }
                        let mut execution_cost = clarity_tx.cost_so_far();
                        execution_cost
                            .sub(&cost_so_far)
                            .expect("BUG: cost declined between executions");
                        cost_so_far = clarity_tx.cost_so_far();

                        let receipt = StacksTransactionReceipt {
                            transaction: TransactionOrigin::Burn(txid),
                            events,
                            result: value,
                            post_condition_aborted: false,
                            stx_burned: 0,
                            contract_analysis: None,
                            execution_cost,
                            microblock_header: None,
                        };

                        all_receipts.push(receipt);
                    } else {
                        unreachable!(
                            "BUG: Non-response value returned by Stacking STX burnchain op"
                        )
                    }
                }
                Err(e) => {
                    info!("StackStx burn op processing error.";
                           "error" => %format!("{:?}", e),
                           "txid" => %txid,
                           "burn_block" => %burn_header_hash);
                }
            };
        }

        all_receipts
    }

    /// Process any STX transfer bitcoin operations
    ///  that haven't been processed in this Stacks fork yet.
    pub fn process_transfer_ops(
        clarity_tx: &mut ClarityTx,
        mut operations: Vec<TransferStxOp>,
    ) -> Vec<StacksTransactionReceipt> {
        operations.sort_by_key(|op| op.vtxindex);
        let (all_receipts, _) =
            clarity_tx.with_temporary_cost_tracker(LimitedCostTracker::new_free(), |clarity_tx| {
                operations
                    .into_iter()
                    .filter_map(|transfer_stx_op| {
                        let TransferStxOp {
                            sender,
                            recipient,
                            transfered_ustx,
                            txid,
                            burn_header_hash,
                            memo,
                            ..
                        } = transfer_stx_op;
                        let result = clarity_tx.connection().as_transaction(|tx| {
                            tx.run_stx_transfer(
                                &sender.into(),
                                &recipient.into(),
                                transfered_ustx,
                                &BuffData { data: memo },
                            )
                        });
                        match result {
                            Ok((value, _, events)) => Some(StacksTransactionReceipt {
                                transaction: TransactionOrigin::Burn(txid),
                                events,
                                result: value,
                                post_condition_aborted: false,
                                stx_burned: 0,
                                contract_analysis: None,
                                execution_cost: ExecutionCost::zero(),
                                microblock_header: None,
                            }),
                            Err(e) => {
                                info!("TransferStx burn op processing error.";
                              "error" => ?e,
                              "txid" => %txid,
                              "burn_block" => %burn_header_hash);
                                None
                            }
                        }
                    })
                    .collect()
            });

        all_receipts
    }

    /// Process a single anchored block.
    /// Return the fees and burns.
    fn process_block_transactions(
        clarity_tx: &mut ClarityTx,
        block: &StacksBlock,
    ) -> Result<(u128, u128, Vec<StacksTransactionReceipt>), Error> {
        let mut fees = 0u128;
        let mut burns = 0u128;
        let mut receipts = vec![];
        for tx in block.txs.iter() {
            let (tx_fee, tx_receipt) =
                StacksChainState::process_transaction(clarity_tx, tx, false)?;
            fees = fees.checked_add(tx_fee as u128).expect("Fee overflow");
            burns = burns
                .checked_add(tx_receipt.stx_burned as u128)
                .expect("Burns overflow");
            receipts.push(tx_receipt);
        }
        Ok((fees, burns, receipts))
    }

    /// Process a single matured miner reward.
    /// Grant it STX tokens.
    fn process_matured_miner_reward<'a>(
        clarity_tx: &mut ClarityTx<'a>,
        miner_reward: &MinerReward,
    ) -> Result<(), Error> {
        let miner_reward_total = miner_reward.total();
        clarity_tx
            .connection()
            .as_transaction(|x| {
                x.with_clarity_db(|ref mut db| {
                    let miner_principal = PrincipalData::Standard(StandardPrincipalData::from(
                        miner_reward.address.clone(),
                    ));
                    let mut snapshot = db.get_stx_balance_snapshot(&miner_principal);
                    snapshot.credit(miner_reward_total);

                    debug!(
                        "Balance available for {} is {} STX",
                        &miner_reward.address,
                        snapshot.get_available_balance();
                    );
                    snapshot.save();

                    Ok(())
                })
            })
            .map_err(Error::ClarityError)?;
        Ok(())
    }

    /// Process matured miner rewards for this block.
    /// Returns the number of liquid uSTX created -- i.e. the coinbase
    pub fn process_matured_miner_rewards<'a>(
        clarity_tx: &mut ClarityTx<'a>,
        miner_share: &MinerReward,
        users_share: &Vec<MinerReward>,
        parent_share: &MinerReward,
    ) -> Result<u128, Error> {
        let mut coinbase_reward = miner_share.coinbase;
        StacksChainState::process_matured_miner_reward(clarity_tx, miner_share)?;
        for reward in users_share.iter() {
            coinbase_reward += reward.coinbase;
            StacksChainState::process_matured_miner_reward(clarity_tx, reward)?;
        }

        // give the parent its confirmed share of the streamed microblocks
        assert_eq!(parent_share.total(), parent_share.tx_fees_streamed_produced);
        StacksChainState::process_matured_miner_reward(clarity_tx, parent_share)?;
        Ok(coinbase_reward)
    }

    /// Process all STX that unlock at this block height.
    /// Return the total number of uSTX unlocked in this block
    pub fn process_stx_unlocks<'a>(
        clarity_tx: &mut ClarityTx<'a>,
    ) -> Result<(u128, Vec<StacksTransactionEvent>), Error> {
        let mainnet = clarity_tx.config.mainnet;
        let lockup_contract_id = util::boot::boot_code_id("lockup", mainnet);
        clarity_tx
            .connection()
            .as_transaction(|tx_connection| {
                let result = tx_connection.with_clarity_db(|db| {
                    let block_height = Value::UInt(db.get_current_block_height().into());
                    let res = db.fetch_entry_unknown_descriptor(
                        &lockup_contract_id,
                        "lockups",
                        &block_height,
                    )?;
                    Ok(res)
                })?;

                let entries = match result {
                    Value::Optional(_) => match result.expect_optional() {
                        Some(Value::Sequence(SequenceData::List(entries))) => entries.data,
                        _ => return Ok((0, vec![])),
                    },
                    _ => return Ok((0, vec![])),
                };

                let mut total_minted = 0;
                let mut events = vec![];
                for entry in entries.into_iter() {
                    let schedule: TupleData = entry.expect_tuple();
                    let amount = schedule
                        .get("amount")
                        .expect("Lockup malformed")
                        .to_owned()
                        .expect_u128();
                    let recipient = schedule
                        .get("recipient")
                        .expect("Lockup malformed")
                        .to_owned()
                        .expect_principal();
                    total_minted += amount;
                    StacksChainState::account_credit(tx_connection, &recipient, amount as u64);
                    let event = STXEventType::STXMintEvent(STXMintEventData { recipient, amount });
                    events.push(StacksTransactionEvent::STXEvent(event));
                }
                Ok((total_minted, events))
            })
            .map_err(Error::ClarityError)
    }

    /// Given the list of matured miners, find the miner reward schedule that produced the parent
    /// of the block whose coinbase just matured.
    pub fn get_parent_matured_miner(
        stacks_tx: &mut StacksDBTx,
        mainnet: bool,
        latest_matured_miners: &Vec<MinerPaymentSchedule>,
    ) -> Result<MinerPaymentSchedule, Error> {
        let parent_miner = if let Some(ref miner) = latest_matured_miners.first().as_ref() {
            StacksChainState::get_scheduled_block_rewards_at_block(
                stacks_tx,
                &StacksBlockHeader::make_index_block_hash(
                    &miner.parent_consensus_hash,
                    &miner.parent_block_hash,
                ),
            )?
            .pop()
            .unwrap_or_else(|| {
                if miner.parent_consensus_hash == FIRST_BURNCHAIN_CONSENSUS_HASH
                    && miner.parent_block_hash == FIRST_STACKS_BLOCK_HASH
                {
                    MinerPaymentSchedule::genesis(mainnet)
                } else {
                    panic!(
                        "CORRUPTION: parent {}/{} of {}/{} not found in DB",
                        &miner.parent_consensus_hash,
                        &miner.parent_block_hash,
                        &miner.consensus_hash,
                        &miner.block_hash
                    );
                }
            })
        } else {
            MinerPaymentSchedule::genesis(mainnet)
        };

        Ok(parent_miner)
    }

    /// Process the next pre-processed staging block.
    /// We've already processed parent_chain_tip.  chain_tip refers to a block we have _not_
    /// processed yet.
    /// Returns a StacksHeaderInfo with the microblock stream and chain state index root hash filled in, corresponding to the next block to process.
    /// In addition, returns the list of transaction receipts for both the preceeding microblock
    /// stream that the block confirms, as well as the transaction receipts for the anchored
    /// block's transactions.  Finally, it returns the execution costs for the microblock stream
    /// and for the anchored block (separately).
    /// Returns None if we're out of blocks to process.
    fn append_block(
        chainstate_tx: &mut ChainstateTx,
        clarity_instance: &mut ClarityInstance,
        burn_dbconn: &mut SortitionHandleTx,
        parent_chain_tip: &StacksHeaderInfo,
        chain_tip_consensus_hash: &ConsensusHash,
        chain_tip_burn_header_hash: &BurnchainHeaderHash,
        chain_tip_burn_header_height: u32,
        chain_tip_burn_header_timestamp: u64,
        block: &StacksBlock,
        block_size: u64,
        microblocks: &Vec<StacksMicroblock>, // parent microblocks
        burnchain_commit_burn: u64,
        burnchain_sortition_burn: u64,
        user_burns: &Vec<StagingUserBurnSupport>,
    ) -> Result<StacksEpochReceipt, Error> {
        debug!(
            "Process block {:?} with {} transactions",
            &block.block_hash().to_hex(),
            block.txs.len()
        );

        let mainnet = chainstate_tx.get_config().mainnet;
        let next_block_height = block.header.total_work.work;

        // find matured miner rewards, so we can grant them within the Clarity DB tx.
        let latest_matured_miners = StacksChainState::get_scheduled_block_rewards(
            chainstate_tx.deref_mut(),
            &parent_chain_tip,
        )?;

        let matured_miner_parent = StacksChainState::get_parent_matured_miner(
            chainstate_tx.deref_mut(),
            mainnet,
            &latest_matured_miners,
        )?;

        let (
            scheduled_miner_reward,
            tx_receipts,
            microblock_execution_cost,
            block_execution_cost,
            matured_rewards,
            matured_rewards_info,
            parent_burn_block_hash,
            parent_burn_block_height,
            parent_burn_block_timestamp,
        ) = {
            let (parent_consensus_hash, parent_block_hash) = if block.is_first_mined() {
                // has to be the sentinal hashes if this block has no parent
                (
                    FIRST_BURNCHAIN_CONSENSUS_HASH.clone(),
                    FIRST_STACKS_BLOCK_HASH.clone(),
                )
            } else {
                (
                    parent_chain_tip.consensus_hash.clone(),
                    parent_chain_tip.anchored_header.block_hash(),
                )
            };

            // get previous burn block stats
            let (parent_burn_block_hash, parent_burn_block_height, parent_burn_block_timestamp) =
                if block.is_first_mined() {
                    (BurnchainHeaderHash([0; 32]), 0, 0)
                } else {
                    match SortitionDB::get_block_snapshot_consensus(
                        burn_dbconn,
                        &parent_consensus_hash,
                    )? {
                        Some(sn) => (
                            sn.burn_header_hash,
                            sn.block_height as u32,
                            sn.burn_header_timestamp,
                        ),
                        None => {
                            // shouldn't happen
                            warn!(
                                "CORRUPTION: block {}/{} does not correspond to a burn block",
                                &parent_consensus_hash, &parent_block_hash
                            );
                            (BurnchainHeaderHash([0; 32]), 0, 0)
                        }
                    }
                };

            let (last_microblock_hash, last_microblock_seq) = if microblocks.len() > 0 {
                let _first_mblock_hash = microblocks[0].block_hash();
                let num_mblocks = microblocks.len();
                let last_microblock_hash = microblocks[num_mblocks - 1].block_hash();
                let last_microblock_seq = microblocks[num_mblocks - 1].header.sequence;

                debug!(
                    "\n\nAppend {} microblocks {}/{}-{} off of {}/{}\n",
                    num_mblocks,
                    chain_tip_consensus_hash,
                    _first_mblock_hash,
                    last_microblock_hash,
                    parent_consensus_hash,
                    parent_block_hash
                );
                (last_microblock_hash, last_microblock_seq)
            } else {
                (EMPTY_MICROBLOCK_PARENT_HASH.clone(), 0)
            };

            if last_microblock_hash != block.header.parent_microblock
                || last_microblock_seq != block.header.parent_microblock_sequence
            {
                // the pre-processing step should prevent this from being reached
                panic!("BUG: received discontiguous headers for processing: {} (seq={}) does not connect to {} (microblock parent is {} (seq {}))",
                       last_microblock_hash, last_microblock_seq, block.block_hash(), block.header.parent_microblock, block.header.parent_microblock_sequence);
            }

            // get the burnchain block that precedes this block's sortition
            let parent_burn_hash = SortitionDB::get_block_snapshot_consensus(
                &burn_dbconn.tx(),
                &chain_tip_consensus_hash,
            )?
            .expect(
                "BUG: Failed to load snapshot for block snapshot during Stacks block processing",
            )
            .parent_burn_header_hash;
            let stacking_burn_ops =
                SortitionDB::get_stack_stx_ops(&burn_dbconn.tx(), &parent_burn_hash)?;
            let transfer_burn_ops =
                SortitionDB::get_transfer_stx_ops(&burn_dbconn.tx(), &parent_burn_hash)?;

            let parent_block_cost = StacksChainState::get_stacks_block_anchored_cost(
                &chainstate_tx.deref().deref(),
                &StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &parent_block_hash,
                ),
            )?
            .expect(&format!(
                "BUG: no execution cost found for parent block {}/{}",
                parent_consensus_hash, parent_block_hash
            ));

            let mut clarity_tx = StacksChainState::chainstate_block_begin(
                chainstate_tx,
                clarity_instance,
                burn_dbconn,
                &parent_consensus_hash,
                &parent_block_hash,
                &MINER_BLOCK_CONSENSUS_HASH,
                &MINER_BLOCK_HEADER_HASH,
            );

            debug!(
                "Parent block {}/{} cost {:?}",
                &parent_consensus_hash, &parent_block_hash, &parent_block_cost
            );
            clarity_tx.reset_cost(parent_block_cost.clone());

            let matured_miner_rewards_opt = match StacksChainState::find_mature_miner_rewards(
                &mut clarity_tx,
                parent_chain_tip,
                latest_matured_miners,
                matured_miner_parent,
            ) {
                Ok(miner_rewards_opt) => miner_rewards_opt,
                Err(e) => {
                    let msg = format!("Failed to load miner rewards: {:?}", &e);
                    warn!("{}", &msg);

                    clarity_tx.rollback_block();
                    return Err(Error::InvalidStacksBlock(msg));
                }
            };

            // validation check -- is this microblock public key hash new to this fork?  It must
            // be, or this block is invalid.
            match StacksChainState::has_microblock_pubkey_hash(
                &mut clarity_tx,
                &block.header.microblock_pubkey_hash,
            ) {
                Ok(Some(height)) => {
                    // already used
                    let msg = format!(
                        "Invalid stacks block {}/{} -- already used microblock pubkey hash {} at height {}",
                        chain_tip_consensus_hash,
                        block.block_hash(),
                        &block.header.microblock_pubkey_hash,
                        height
                    );
                    warn!("{}", &msg);

                    clarity_tx.rollback_block();
                    return Err(Error::InvalidStacksBlock(msg));
                }
                Ok(None) => {}
                Err(e) => {
                    let msg = format!(
                        "Failed to determine microblock if public key hash {} is used: {:?}",
                        &block.header.microblock_pubkey_hash, &e
                    );
                    warn!("{}", &msg);

                    clarity_tx.rollback_block();
                    return Err(e);
                }
            }

            // process microblock stream.
            // If we go over-budget, then we can't process this block either (which is by design)
            let (microblock_fees, microblock_burns, microblock_txs_receipts) =
                match StacksChainState::process_microblocks_transactions(
                    &mut clarity_tx,
                    &microblocks,
                ) {
                    Err((e, offending_mblock_header_hash)) => {
                        let msg = format!(
                            "Invalid Stacks microblocks {},{} (offender {}): {:?}",
                            block.header.parent_microblock,
                            block.header.parent_microblock_sequence,
                            offending_mblock_header_hash,
                            &e
                        );
                        warn!("{}", &msg);

                        clarity_tx.rollback_block();
                        return Err(Error::InvalidStacksMicroblock(
                            msg,
                            offending_mblock_header_hash,
                        ));
                    }
                    Ok((fees, burns, events)) => (fees, burns, events),
                };

            // find microblock cost
            let mut microblock_cost = clarity_tx.cost_so_far();
            microblock_cost
                .sub(&parent_block_cost)
                .expect("BUG: block_cost + microblock_cost < block_cost");

            // if we get here, then we need to reset the block-cost back to 0 since this begins the
            // epoch defined by this miner.
            clarity_tx.reset_cost(ExecutionCost::zero());

            debug!("Append block";
                   "block" => %format!("{}/{}", chain_tip_consensus_hash, block.block_hash()),
                   "parent_block" => %format!("{}/{}", parent_consensus_hash, parent_block_hash),
                   "stacks_height" => %block.header.total_work.work,
                   "total_burns" => %block.header.total_work.burn,
                   "microblock_parent" => %last_microblock_hash,
                   "microblock_parent_seq" => %last_microblock_seq,
                   "microblock_parent_count" => %microblocks.len());

            // process stacking operations from bitcoin ops
            let mut receipts =
                StacksChainState::process_stacking_ops(&mut clarity_tx, stacking_burn_ops);

            receipts.extend(StacksChainState::process_transfer_ops(
                &mut clarity_tx,
                transfer_burn_ops,
            ));

            // process anchored block
            let (block_fees, block_burns, txs_receipts) =
                match StacksChainState::process_block_transactions(&mut clarity_tx, &block) {
                    Err(e) => {
                        let msg = format!("Invalid Stacks block {}: {:?}", block.block_hash(), &e);
                        warn!("{}", &msg);

                        clarity_tx.rollback_block();
                        return Err(Error::InvalidStacksBlock(msg));
                    }
                    Ok((block_fees, block_burns, txs_receipts)) => {
                        (block_fees, block_burns, txs_receipts)
                    }
                };

            receipts.extend(txs_receipts.into_iter());

            let block_cost = clarity_tx.cost_so_far();

            // grant matured miner rewards
            let new_liquid_miner_ustx =
                if let Some((ref miner_reward, ref user_rewards, ref parent_miner_reward, _)) =
                    matured_miner_rewards_opt.as_ref()
                {
                    // grant in order by miner, then users
                    StacksChainState::process_matured_miner_rewards(
                        &mut clarity_tx,
                        miner_reward,
                        user_rewards,
                        parent_miner_reward,
                    )?
                } else {
                    0
                };

            clarity_tx.increment_ustx_liquid_supply(new_liquid_miner_ustx);

            // obtain reward info for receipt
            let (matured_rewards, matured_rewards_info) =
                if let Some((miner_reward, mut user_rewards, parent_reward, reward_ptr)) =
                    matured_miner_rewards_opt
                {
                    let mut ret = vec![];
                    ret.push(miner_reward);
                    ret.append(&mut user_rewards);
                    ret.push(parent_reward);
                    (ret, Some(reward_ptr))
                } else {
                    (vec![], None)
                };

            // total burns
            let total_burnt = block_burns
                .checked_add(microblock_burns)
                .expect("Overflow: Too many STX burnt");

            // unlock any uSTX
            let (new_unlocked_ustx, mut lockup_events) =
                StacksChainState::process_stx_unlocks(&mut clarity_tx)?;

            // if any, append lockups events to the coinbase receipt
            if lockup_events.len() > 0 {
                // Receipts are appended in order, so the first receipt should be
                // the one of the coinbase transaction
                if let Some(receipt) = receipts.get_mut(0) {
                    if receipt.is_coinbase_tx() {
                        receipt.events.append(&mut lockup_events);
                    }
                } else {
                    warn!("Unable to attach lockups events, first block's transaction is not a coinbase transaction")
                }
            }

            clarity_tx.increment_ustx_liquid_supply(new_unlocked_ustx);

            // record that this microblock public key hash was used at this height
            match StacksChainState::insert_microblock_pubkey_hash(
                &mut clarity_tx,
                block.header.total_work.work as u32,
                &block.header.microblock_pubkey_hash,
            ) {
                Ok(_) => {
                    debug!(
                        "Added microblock public key {} at height {}",
                        &block.header.microblock_pubkey_hash, block.header.total_work.work
                    );
                }
                Err(e) => {
                    let msg = format!(
                        "Failed to insert microblock pubkey hash {} at height {}: {:?}",
                        &block.header.microblock_pubkey_hash, block.header.total_work.work, &e
                    );
                    warn!("{}", &msg);

                    clarity_tx.rollback_block();
                    return Err(Error::InvalidStacksBlock(msg));
                }
            };

            let root_hash = clarity_tx.get_root_hash();
            if root_hash != block.header.state_index_root {
                let msg = format!(
                    "Block {} state root mismatch: expected {}, got {}",
                    block.block_hash(),
                    root_hash,
                    block.header.state_index_root
                );
                warn!("{}", &msg);

                clarity_tx.rollback_block();
                return Err(Error::InvalidStacksBlock(msg));
            }

            debug!("Reached state root {}", root_hash;
                   "microblock cost" => %microblock_cost,
                   "block cost" => %block_cost);

            // good to go!
            clarity_tx.commit_to_block(chain_tip_consensus_hash, &block.block_hash());

            // figure out if there any accumulated rewards by
            //   getting the snapshot that elected this block.
            let accumulated_rewards = SortitionDB::get_block_snapshot_consensus(
                burn_dbconn.tx(),
                chain_tip_consensus_hash,
            )?
            .expect("CORRUPTION: failed to load snapshot that elected processed block")
            .accumulated_coinbase_ustx;

            let coinbase_at_block = StacksChainState::get_coinbase_reward(
                chain_tip_burn_header_height as u64,
                burn_dbconn.context.first_block_height,
            );

            let total_coinbase = coinbase_at_block.saturating_add(accumulated_rewards);

            // calculate reward for this block's miner
            let scheduled_miner_reward = StacksChainState::make_scheduled_miner_reward(
                mainnet,
                &parent_block_hash,
                &parent_consensus_hash,
                &block,
                chain_tip_consensus_hash,
                next_block_height,
                block_fees,
                microblock_fees,
                total_burnt,
                burnchain_commit_burn,
                burnchain_sortition_burn,
                total_coinbase,
            )
            .expect("FATAL: parsed and processed a block without a coinbase");

            receipts.extend(microblock_txs_receipts.into_iter());

            (
                scheduled_miner_reward,
                receipts,
                microblock_cost,
                block_cost,
                matured_rewards,
                matured_rewards_info,
                parent_burn_block_hash,
                parent_burn_block_height,
                parent_burn_block_timestamp,
            )
        };

        let microblock_tail_opt = match microblocks.len() {
            0 => None,
            x => Some(microblocks[x - 1].header.clone()),
        };

        let new_tip = StacksChainState::advance_tip(
            &mut chainstate_tx.tx,
            &parent_chain_tip.anchored_header,
            &parent_chain_tip.consensus_hash,
            &block.header,
            chain_tip_consensus_hash,
            chain_tip_burn_header_hash,
            chain_tip_burn_header_height,
            chain_tip_burn_header_timestamp,
            microblock_tail_opt,
            &scheduled_miner_reward,
            user_burns,
            &block_execution_cost,
            block_size,
        )
        .expect("FATAL: failed to advance chain tip");

        chainstate_tx.log_transactions_processed(&new_tip.index_block_hash(), &tx_receipts);

        let epoch_receipt = StacksEpochReceipt {
            header: new_tip,
            tx_receipts,
            matured_rewards,
            matured_rewards_info,
            parent_microblocks_cost: microblock_execution_cost,
            anchored_block_cost: block_execution_cost,
            parent_burn_block_hash,
            parent_burn_block_height,
            parent_burn_block_timestamp,
        };

        Ok(epoch_receipt)
    }

    /// Verify that a Stacks anchored block attaches to its parent anchored block.
    /// * checks .header.total_work.work
    /// * checks .header.parent_block
    fn check_block_attachment(
        parent_block_header: &StacksBlockHeader,
        block_header: &StacksBlockHeader,
    ) -> bool {
        // must have the right height
        if parent_block_header
            .total_work
            .work
            .checked_add(1)
            .expect("Blockchain height overflow")
            != block_header.total_work.work
        {
            return false;
        }

        // must have right hash linkage
        if parent_block_header.block_hash() != block_header.parent_block {
            return false;
        }

        return true;
    }

    /// Get the parent header info for a block we're processing, if it's known.
    /// The header info will be pulled from the headers DB, so this method only succeeds if the
    /// parent block has been processed.
    /// If it's not known, return None.
    fn get_parent_header_info(
        chainstate_tx: &mut ChainstateTx,
        next_staging_block: &StagingBlock,
    ) -> Result<Option<StacksHeaderInfo>, Error> {
        let parent_block_header_info = match StacksChainState::get_anchored_block_header_info(
            &chainstate_tx.tx,
            &next_staging_block.parent_consensus_hash,
            &next_staging_block.parent_anchored_block_hash,
        )? {
            Some(parent_info) => {
                debug!(
                    "Found parent info {}/{}",
                    next_staging_block.parent_consensus_hash,
                    next_staging_block.parent_anchored_block_hash
                );
                parent_info
            }
            None => {
                if next_staging_block.is_first_mined() {
                    // this is the first-ever mined block
                    debug!("This is the first-ever block in this fork.  Parent is 00000000..00000000/00000000..00000000");
                    StacksChainState::get_anchored_block_header_info(
                        &chainstate_tx.tx,
                        &FIRST_BURNCHAIN_CONSENSUS_HASH,
                        &FIRST_STACKS_BLOCK_HASH,
                    )
                    .expect("FATAL: failed to load initial block header")
                    .expect("FATAL: initial block header not found in headers DB")
                } else {
                    // no parent stored
                    debug!(
                        "No parent block for {}/{} processed yet",
                        next_staging_block.consensus_hash, next_staging_block.anchored_block_hash
                    );
                    return Ok(None);
                }
            }
        };
        Ok(Some(parent_block_header_info))
    }

    /// Extract and parse the block from a loaded staging block, and verify its integrity.
    fn extract_stacks_block(next_staging_block: &StagingBlock) -> Result<StacksBlock, Error> {
        let block = {
            StacksBlock::consensus_deserialize(&mut &next_staging_block.block_data[..])
                .map_err(Error::CodecError)?
        };

        let block_hash = block.block_hash();
        if block_hash != next_staging_block.anchored_block_hash {
            // database corruption
            error!(
                "Staging DB corruption: expected block {}, got {} from disk",
                next_staging_block.anchored_block_hash, block_hash
            );
            return Err(Error::DBError(db_error::Corruption));
        }
        Ok(block)
    }

    /// Given the list of microblocks produced by the given block's parent (and given the parent's
    /// header info), determine which branch connects to the given block.  If there are multiple
    /// branches, punish the parent.  Return the portion of the branch that actually connects to
    /// the given block.
    fn extract_connecting_microblocks(
        parent_block_header_info: &StacksHeaderInfo,
        next_staging_block: &StagingBlock,
        block: &StacksBlock,
        mut next_microblocks: Vec<StacksMicroblock>,
    ) -> Result<Vec<StacksMicroblock>, Error> {
        // NOTE: since we got the microblocks from staging, where their signatures were already
        // validated, we don't need to validate them again.
        let microblock_terminus = match StacksChainState::validate_parent_microblock_stream(
            &parent_block_header_info.anchored_header,
            &block.header,
            &next_microblocks,
            false,
        ) {
            Some((terminus, _)) => terminus,
            None => {
                debug!(
                    "Stopping at block {}/{} -- discontiguous header stream",
                    next_staging_block.consensus_hash, next_staging_block.anchored_block_hash,
                );
                return Ok(vec![]);
            }
        };

        // do not consider trailing microblocks that this anchored block does _not_ confirm
        if microblock_terminus < next_microblocks.len() {
            debug!(
                "Truncate microblock stream from parent {}/{} from {} to {} items",
                parent_block_header_info.consensus_hash,
                parent_block_header_info.anchored_header.block_hash(),
                next_microblocks.len(),
                microblock_terminus
            );
            next_microblocks.truncate(microblock_terminus);
        }

        Ok(next_microblocks)
    }

    /// Find and process the next staging block.
    /// Return the next chain tip if we processed this block, or None if we couldn't.
    /// Return a poison microblock transaction payload if the microblock stream contains a
    /// deliberate miner fork (this is NOT consensus-critical information, but is instead meant for
    /// consumption by future miners).
    pub fn process_next_staging_block(
        &mut self,
        sort_tx: &mut SortitionHandleTx,
    ) -> Result<(Option<StacksEpochReceipt>, Option<TransactionPayload>), Error> {
        let blocks_path = self.blocks_path.clone();
        let (mut chainstate_tx, clarity_instance) = self.chainstate_tx_begin()?;

        // this is a transaction against both the headers and staging blocks databases!
        let (next_microblocks, next_staging_block) =
            match StacksChainState::find_next_staging_block(
                &mut chainstate_tx.tx,
                &blocks_path,
                sort_tx,
            )? {
                Some((next_microblocks, next_staging_block)) => {
                    (next_microblocks, next_staging_block)
                }
                None => {
                    // no more work to do!
                    debug!("No staging blocks");

                    // save any orphaning we did
                    chainstate_tx.commit().map_err(Error::DBError)?;
                    return Ok((None, None));
                }
            };

        let (burn_header_hash, burn_header_height, burn_header_timestamp) =
            match SortitionDB::get_block_snapshot_consensus(
                sort_tx,
                &next_staging_block.consensus_hash,
            )? {
                Some(sn) => (
                    sn.burn_header_hash,
                    sn.block_height as u32,
                    sn.burn_header_timestamp,
                ),
                None => {
                    // shouldn't happen
                    panic!(
                        "CORRUPTION: staging block {}/{} does not correspond to a burn block",
                        &next_staging_block.consensus_hash, &next_staging_block.anchored_block_hash
                    );
                }
            };

        debug!(
            "Process staging block {}/{} in burn block {}, parent microblock {}",
            next_staging_block.consensus_hash,
            next_staging_block.anchored_block_hash,
            &burn_header_hash,
            &next_staging_block.parent_microblock_hash,
        );

        let parent_header_info = match StacksChainState::get_parent_header_info(
            &mut chainstate_tx,
            &next_staging_block,
        )? {
            Some(hinfo) => hinfo,
            None => return Ok((None, None)),
        };

        let block = StacksChainState::extract_stacks_block(&next_staging_block)?;
        let block_size = next_staging_block.block_data.len() as u64;

        // sanity check -- don't process this block again if we already did so
        if StacksChainState::has_stacks_block(
            chainstate_tx.tx.deref().deref(),
            &StacksBlockHeader::make_index_block_hash(
                &next_staging_block.consensus_hash,
                &next_staging_block.anchored_block_hash,
            ),
        )? || StacksChainState::has_stored_block(
            chainstate_tx.tx.deref().deref(),
            &blocks_path,
            &next_staging_block.consensus_hash,
            &next_staging_block.anchored_block_hash,
        )? {
            debug!(
                "Block already processed: {}/{}",
                &next_staging_block.consensus_hash, &next_staging_block.anchored_block_hash
            );

            // clear out
            StacksChainState::set_block_processed(
                chainstate_tx.deref_mut(),
                Some(sort_tx),
                &blocks_path,
                &next_staging_block.consensus_hash,
                &next_staging_block.anchored_block_hash,
                true,
            )?;
            chainstate_tx.commit().map_err(Error::DBError)?;

            return Ok((None, None));
        }

        // validation check -- the block must attach to its accepted parent
        if !StacksChainState::check_block_attachment(
            &parent_header_info.anchored_header,
            &block.header,
        ) {
            let msg = format!(
                "Invalid stacks block {}/{} -- does not attach to parent {}/{}",
                &next_staging_block.consensus_hash,
                block.block_hash(),
                parent_header_info.anchored_header.block_hash(),
                &parent_header_info.consensus_hash
            );
            warn!("{}", &msg);

            // clear out
            StacksChainState::set_block_processed(
                chainstate_tx.deref_mut(),
                None,
                &blocks_path,
                &next_staging_block.consensus_hash,
                &next_staging_block.anchored_block_hash,
                false,
            )?;
            chainstate_tx.commit().map_err(Error::DBError)?;

            return Err(Error::InvalidStacksBlock(msg));
        }

        // validation check -- validate parent microblocks and find the ones that connect the
        // block's parent to this block.
        let next_microblocks = StacksChainState::extract_connecting_microblocks(
            &parent_header_info,
            &next_staging_block,
            &block,
            next_microblocks,
        )?;
        let (last_microblock_hash, last_microblock_seq) = match next_microblocks.len() {
            0 => (EMPTY_MICROBLOCK_PARENT_HASH.clone(), 0),
            _ => {
                let l = next_microblocks.len();
                (
                    next_microblocks[l - 1].block_hash(),
                    next_microblocks[l - 1].header.sequence,
                )
            }
        };
        assert_eq!(
            next_staging_block.parent_microblock_hash,
            last_microblock_hash
        );
        assert_eq!(
            next_staging_block.parent_microblock_seq,
            last_microblock_seq
        );

        // find users that burned in support of this block, so we can calculate the miner reward
        let user_supports = StacksChainState::load_staging_block_user_supports(
            chainstate_tx.deref().deref(),
            &next_staging_block.consensus_hash,
            &next_staging_block.anchored_block_hash,
        )?;

        // attach the block to the chain state and calculate the next chain tip.
        // Execute the confirmed microblocks' transactions against the chain state, and then
        // execute the anchored block's transactions against the chain state.
        let epoch_receipt = match StacksChainState::append_block(
            &mut chainstate_tx,
            clarity_instance,
            sort_tx,
            &parent_header_info,
            &next_staging_block.consensus_hash,
            &burn_header_hash,
            burn_header_height,
            burn_header_timestamp,
            &block,
            block_size,
            &next_microblocks,
            next_staging_block.commit_burn,
            next_staging_block.sortition_burn,
            &user_supports,
        ) {
            Ok(next_chain_tip_info) => next_chain_tip_info,
            Err(e) => {
                // something's wrong with this epoch -- either a microblock was invalid, or the
                // anchored block was invalid.  Either way, the anchored block will _never be_
                // valid, so we can drop it from the chunk store and orphan all of its descendants.
                test_debug!(
                    "Failed to append {}/{}",
                    &next_staging_block.consensus_hash,
                    &block.block_hash()
                );
                StacksChainState::set_block_processed(
                    chainstate_tx.deref_mut(),
                    None,
                    &blocks_path,
                    &next_staging_block.consensus_hash,
                    &block.header.block_hash(),
                    false,
                )?;
                StacksChainState::free_block_state(
                    &blocks_path,
                    &next_staging_block.consensus_hash,
                    &block.header,
                );

                match e {
                    Error::InvalidStacksMicroblock(ref msg, ref header_hash) => {
                        // specifically, an ancestor microblock was invalid.  Drop any descendant microblocks --
                        // they're never going to be valid in _any_ fork, even if they have a clone
                        // in a neighboring burnchain fork.
                        error!(
                            "Parent microblock stream from {}/{} is invalid at microblock {}: {}",
                            parent_header_info.consensus_hash,
                            parent_header_info.anchored_header.block_hash(),
                            header_hash,
                            msg
                        );
                        StacksChainState::drop_staging_microblocks(
                            chainstate_tx.deref_mut(),
                            &parent_header_info.consensus_hash,
                            &parent_header_info.anchored_header.block_hash(),
                            header_hash,
                        )?;
                    }
                    _ => {
                        // block was invalid, but this means all the microblocks it confirmed are
                        // still (potentially) valid.  However, they are not confirmed yet, so
                        // leave them in the staging database.
                    }
                }

                chainstate_tx.commit().map_err(Error::DBError)?;

                return Err(e);
            }
        };

        assert_eq!(
            epoch_receipt.header.anchored_header.block_hash(),
            block.block_hash()
        );
        assert_eq!(
            epoch_receipt.header.consensus_hash,
            next_staging_block.consensus_hash
        );
        assert_eq!(
            epoch_receipt.header.anchored_header.parent_microblock,
            last_microblock_hash
        );
        assert_eq!(
            epoch_receipt
                .header
                .anchored_header
                .parent_microblock_sequence,
            last_microblock_seq
        );

        debug!(
            "Reached chain tip {}/{} from {}/{}",
            epoch_receipt.header.consensus_hash,
            epoch_receipt.header.anchored_header.block_hash(),
            next_staging_block.parent_consensus_hash,
            next_staging_block.parent_anchored_block_hash
        );

        if next_staging_block.parent_microblock_hash != EMPTY_MICROBLOCK_PARENT_HASH
            || next_staging_block.parent_microblock_seq != 0
        {
            // confirmed one or more parent microblocks
            StacksChainState::set_microblocks_processed(
                chainstate_tx.deref_mut(),
                &next_staging_block.consensus_hash,
                &next_staging_block.anchored_block_hash,
                &next_staging_block.parent_microblock_hash,
            )?;
        }

        StacksChainState::set_block_processed(
            chainstate_tx.deref_mut(),
            Some(sort_tx),
            &blocks_path,
            &epoch_receipt.header.consensus_hash,
            &epoch_receipt.header.anchored_header.block_hash(),
            true,
        )?;

        chainstate_tx.commit().map_err(Error::DBError)?;

        Ok((Some(epoch_receipt), None))
    }

    /// Process staging blocks at the canonical chain tip,
    ///  this only needs to be used in contexts that aren't
    ///  PoX aware (i.e., unit tests, and old stacks-node loops),
    /// Elsewhere, block processing is invoked by the ChainsCoordinator,
    ///  which handles tracking the chain tip itself
    #[cfg(test)]
    pub fn process_blocks_at_tip(
        &mut self,
        sort_db: &mut SortitionDB,
        max_blocks: usize,
    ) -> Result<Vec<(Option<StacksEpochReceipt>, Option<TransactionPayload>)>, Error> {
        let tx = sort_db.tx_begin_at_tip();
        self.process_blocks(tx, max_blocks)
    }

    /// Process some staging blocks, up to max_blocks.
    /// Return new chain tips, and optionally any poison microblock payloads for each chain tip
    /// found.  For each chain tip produced, return the header info, receipts, parent microblock
    /// stream execution cost, and block execution cost
    pub fn process_blocks(
        &mut self,
        mut sort_tx: SortitionHandleTx,
        max_blocks: usize,
    ) -> Result<Vec<(Option<StacksEpochReceipt>, Option<TransactionPayload>)>, Error> {
        debug!("Process up to {} blocks", max_blocks);

        let mut ret = vec![];

        if max_blocks == 0 {
            // nothing to do
            return Ok(vec![]);
        }

        for i in 0..max_blocks {
            // process up to max_blocks pending blocks
            match self.process_next_staging_block(&mut sort_tx) {
                Ok((next_tip_opt, next_microblock_poison_opt)) => match next_tip_opt {
                    Some(next_tip) => {
                        ret.push((Some(next_tip), next_microblock_poison_opt));
                    }
                    None => match next_microblock_poison_opt {
                        Some(poison) => {
                            ret.push((None, Some(poison)));
                        }
                        None => {
                            debug!("No more staging blocks -- processed {} in total", i);
                            break;
                        }
                    },
                },
                Err(Error::InvalidStacksBlock(msg)) => {
                    warn!("Encountered invalid block: {}", &msg);
                    continue;
                }
                Err(Error::InvalidStacksMicroblock(msg, hash)) => {
                    warn!("Encountered invalid microblock {}: {}", hash, &msg);
                    continue;
                }
                Err(Error::NetError(net_error::DeserializeError(msg))) => {
                    // happens if we load a zero-sized block (i.e. an invalid block)
                    warn!("Encountered invalid block: {}", &msg);
                    continue;
                }
                Err(e) => {
                    error!("Unrecoverable error when processing blocks: {:?}", &e);
                    return Err(e);
                }
            }
        }

        sort_tx.commit()?;

        let blocks_path = self.blocks_path.clone();
        let mut block_tx = self.db_tx_begin()?;
        for _ in 0..max_blocks {
            // delete up to max_blocks blocks
            let deleted =
                StacksChainState::process_next_orphaned_staging_block(&mut block_tx, &blocks_path)?;
            if !deleted {
                break;
            }
        }
        block_tx.commit()?;

        Ok(ret)
    }

    fn is_valid_address_version(mainnet: bool, version: u8) -> bool {
        if mainnet {
            version == C32_ADDRESS_VERSION_MAINNET_SINGLESIG
                || version == C32_ADDRESS_VERSION_MAINNET_MULTISIG
        } else {
            version == C32_ADDRESS_VERSION_TESTNET_SINGLESIG
                || version == C32_ADDRESS_VERSION_TESTNET_MULTISIG
        }
    }

    /// Get the highest processed block on the canonical burn chain.
    /// Break ties on lexigraphical ordering of the block hash
    /// (i.e. arbitrarily).  The staging block will be returned, but no block data will be filled
    /// in.
    pub fn get_stacks_chain_tip(
        &self,
        sortdb: &SortitionDB,
    ) -> Result<Option<StagingBlock>, Error> {
        let (consensus_hash, block_bhh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn())?;
        let sql = "SELECT * FROM staging_blocks WHERE processed = 1 AND orphaned = 0 AND consensus_hash = ?1 AND anchored_block_hash = ?2";
        let args: &[&dyn ToSql] = &[&consensus_hash, &block_bhh];
        query_row(&self.db(), sql, args).map_err(Error::DBError)
    }

    /// Get the height of a staging block
    pub fn get_stacks_block_height(
        &self,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
    ) -> Result<Option<u64>, Error> {
        let sql = "SELECT height FROM staging_blocks WHERE consensus_hash = ?1 AND anchored_block_hash = ?2";
        let args: &[&dyn ToSql] = &[consensus_hash, block_hash];
        query_row(&self.db(), sql, args).map_err(Error::DBError)
    }

    /// This runs checks for the validity of a transaction that
    ///   can be performed just by inspecting the transaction itself (i.e., without
    ///   consulting chain state).
    fn can_admit_mempool_semantic(
        tx: &StacksTransaction,
        is_mainnet: bool,
    ) -> Result<(), MemPoolRejection> {
        if is_mainnet != tx.is_mainnet() {
            return Err(MemPoolRejection::BadTransactionVersion);
        }
        match tx.payload {
            TransactionPayload::TokenTransfer(ref recipient, amount, ref _memo) => {
                let origin = PrincipalData::from(tx.origin_address());
                if &origin == recipient {
                    return Err(MemPoolRejection::TransferRecipientIsSender(origin));
                }
                if amount == 0 {
                    return Err(MemPoolRejection::TransferAmountMustBePositive);
                }
                if !StacksChainState::is_valid_address_version(is_mainnet, recipient.version()) {
                    return Err(MemPoolRejection::BadAddressVersionByte);
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Check to see if a transaction can be (potentially) appended on top of a given chain tip.
    /// Note that this only checks the transaction against the _anchored chain tip_, not the
    /// unconfirmed microblock stream trailing off of it.
    pub fn will_admit_mempool_tx(
        &mut self,
        current_consensus_hash: &ConsensusHash,
        current_block: &BlockHeaderHash,
        tx: &StacksTransaction,
        tx_size: u64,
    ) -> Result<(), MemPoolRejection> {
        let is_mainnet = self.clarity_state.is_mainnet();
        StacksChainState::can_admit_mempool_semantic(tx, is_mainnet)?;

        let conf = self.config();
        let staging_height =
            match self.get_stacks_block_height(current_consensus_hash, current_block) {
                Ok(Some(height)) => height,
                Ok(None) => {
                    if *current_consensus_hash == FIRST_BURNCHAIN_CONSENSUS_HASH {
                        0
                    } else {
                        return Err(MemPoolRejection::NoSuchChainTip(
                            current_consensus_hash.clone(),
                            current_block.clone(),
                        ));
                    }
                }
                Err(_e) => {
                    panic!("DB CORRUPTION: failed to query block height");
                }
            };

        let has_microblock_pubk = match tx.payload {
            TransactionPayload::PoisonMicroblock(ref microblock_header_1, _) => {
                let microblock_pkh_1 = microblock_header_1
                    .check_recover_pubkey()
                    .map_err(|_e| MemPoolRejection::InvalidMicroblocks)?;

                StacksChainState::has_blocks_with_microblock_pubkh(
                    &self.db(),
                    &microblock_pkh_1,
                    staging_height as i64,
                )
            }
            _ => false, // unused
        };

        let current_tip =
            StacksChainState::get_parent_index_block(current_consensus_hash, current_block);
        let res = match self.with_read_only_clarity_tx(&NULL_BURN_STATE_DB, &current_tip, |conn| {
            StacksChainState::can_include_tx(conn, &conf, has_microblock_pubk, tx, tx_size)
        }) {
            Some(r) => r,
            None => Err(MemPoolRejection::NoSuchChainTip(
                current_consensus_hash.clone(),
                current_block.clone(),
            )),
        };

        match res {
            Ok(x) => Ok(x),
            Err(MemPoolRejection::BadNonces(mismatch_error)) => {
                // try again, but against the _unconfirmed_ chain tip, if we
                // (a) have one, and (b) the expected nonce is less than the given one.
                if self.unconfirmed_state.is_some()
                    && mismatch_error.expected < mismatch_error.actual
                {
                    debug!("Transaction {} is unminable in the confirmed chain tip due to nonce {} != {}; trying the unconfirmed chain tip",
                           &tx.txid(), mismatch_error.expected, mismatch_error.actual);
                    self.with_read_only_unconfirmed_clarity_tx(&NULL_BURN_STATE_DB, |conn| {
                        StacksChainState::can_include_tx(
                            conn,
                            &conf,
                            has_microblock_pubk,
                            tx,
                            tx_size,
                        )
                    })
                    .map_err(|_| {
                        MemPoolRejection::NoSuchChainTip(
                            current_consensus_hash.clone(),
                            current_block.clone(),
                        )
                    })?
                    .expect("BUG: do not have unconfirmed state, despite being Some(..)")
                } else {
                    Err(MemPoolRejection::BadNonces(mismatch_error))
                }
            }
            Err(e) => Err(e),
        }
    }

    /// Given an outstanding clarity connection, can we append the tx to the chain state?
    /// Used when mining transactions.
    fn can_include_tx<T: ClarityConnection>(
        clarity_connection: &mut T,
        chainstate_config: &DBConfig,
        has_microblock_pubkey: bool,
        tx: &StacksTransaction,
        tx_size: u64,
    ) -> Result<(), MemPoolRejection> {
        // 1: must parse (done)

        // 2: it must be validly signed.
        StacksChainState::process_transaction_precheck(&chainstate_config, &tx)
            .map_err(|e| MemPoolRejection::FailedToValidate(e))?;

        // 3: it must pay a tx fee
        let fee = tx.get_tx_fee();

        if fee < MINIMUM_TX_FEE || fee / tx_size < MINIMUM_TX_FEE_RATE_PER_BYTE {
            return Err(MemPoolRejection::FeeTooLow(
                fee,
                cmp::max(MINIMUM_TX_FEE, tx_size * MINIMUM_TX_FEE_RATE_PER_BYTE),
            ));
        }

        // 4: the account nonces must be correct
        let (origin, payer) =
            match StacksChainState::check_transaction_nonces(clarity_connection, &tx, true) {
                Ok(x) => x,
                // if errored, check if MEMPOOL_TX_CHAINING would admit this TX
                Err((e, (origin, payer))) => {
                    // if the nonce is less than expected, then TX_CHAINING would not allow in any case
                    if e.actual < e.expected {
                        return Err(e.into());
                    }

                    let tx_origin_nonce = tx.get_origin().nonce();

                    let origin_max_nonce = origin.nonce + 1 + MAXIMUM_MEMPOOL_TX_CHAINING;
                    if origin_max_nonce < tx_origin_nonce {
                        return Err(MemPoolRejection::TooMuchChaining {
                            max_nonce: origin_max_nonce,
                            actual_nonce: tx_origin_nonce,
                            principal: tx.origin_address().into(),
                            is_origin: true,
                        });
                    }

                    if let Some(sponsor_addr) = tx.sponsor_address() {
                        let tx_sponsor_nonce = tx.get_payer().nonce();
                        let sponsor_max_nonce = payer.nonce + 1 + MAXIMUM_MEMPOOL_TX_CHAINING;
                        if sponsor_max_nonce < tx_sponsor_nonce {
                            return Err(MemPoolRejection::TooMuchChaining {
                                max_nonce: sponsor_max_nonce,
                                actual_nonce: tx_sponsor_nonce,
                                principal: sponsor_addr.into(),
                                is_origin: false,
                            });
                        }
                    }
                    (origin, payer)
                }
            };

        if !StacksChainState::is_valid_address_version(
            chainstate_config.mainnet,
            origin.principal.version(),
        ) || !StacksChainState::is_valid_address_version(
            chainstate_config.mainnet,
            payer.principal.version(),
        ) {
            return Err(MemPoolRejection::BadAddressVersionByte);
        }

        let block_height = clarity_connection
            .with_clarity_db_readonly(|ref mut db| db.get_current_burnchain_block_height() as u64);

        // 5: the paying account must have enough funds
        if !payer
            .stx_balance
            .can_transfer_at_burn_block(fee as u128, block_height)
        {
            match &tx.payload {
                TransactionPayload::TokenTransfer(..) => {
                    // pass: we'll return a total_spent failure below.
                }
                _ => {
                    return Err(MemPoolRejection::NotEnoughFunds(
                        fee as u128,
                        payer.stx_balance.amount_unlocked,
                    ));
                }
            }
        }

        // 6: payload-specific checks
        match &tx.payload {
            TransactionPayload::TokenTransfer(addr, amount, _memo) => {
                // version byte matches?
                if !StacksChainState::is_valid_address_version(
                    chainstate_config.mainnet,
                    addr.version(),
                ) {
                    return Err(MemPoolRejection::BadAddressVersionByte);
                }

                // does the owner have the funds for the token transfer?
                let total_spent = (*amount as u128) + if origin == payer { fee as u128 } else { 0 };
                if !origin
                    .stx_balance
                    .can_transfer_at_burn_block(total_spent, block_height)
                {
                    return Err(MemPoolRejection::NotEnoughFunds(
                        total_spent,
                        origin
                            .stx_balance
                            .get_available_balance_at_burn_block(block_height),
                    ));
                }

                // if the payer for the tx is different from owner, check if they can afford fee
                if origin != payer {
                    if !payer
                        .stx_balance
                        .can_transfer_at_burn_block(fee as u128, block_height)
                    {
                        return Err(MemPoolRejection::NotEnoughFunds(
                            fee as u128,
                            payer.stx_balance.amount_unlocked,
                        ));
                    }
                }
            }
            TransactionPayload::ContractCall(TransactionContractCall {
                address,
                contract_name,
                function_name,
                function_args,
            }) => {
                // version byte matches?
                if !StacksChainState::is_valid_address_version(
                    chainstate_config.mainnet,
                    address.version,
                ) {
                    return Err(MemPoolRejection::BadAddressVersionByte);
                }

                let contract_identifier =
                    QualifiedContractIdentifier::new(address.clone().into(), contract_name.clone());

                clarity_connection.with_analysis_db_readonly(|db| {
                    let function_type = db
                        .get_public_function_type(&contract_identifier, &function_name)
                        .map_err(|_e| MemPoolRejection::NoSuchContract)?
                        .ok_or_else(|| MemPoolRejection::NoSuchPublicFunction)?;
                    function_type
                        .check_args_by_allowing_trait_cast(db, &function_args)
                        .map_err(|e| MemPoolRejection::BadFunctionArgument(e))
                })?;
            }
            TransactionPayload::SmartContract(TransactionSmartContract { name, code_body: _ }) => {
                let contract_identifier =
                    QualifiedContractIdentifier::new(tx.origin_address().into(), name.clone());

                let exists = clarity_connection
                    .with_analysis_db_readonly(|db| db.has_contract(&contract_identifier));

                if exists {
                    return Err(MemPoolRejection::ContractAlreadyExists(contract_identifier));
                }
            }
            TransactionPayload::PoisonMicroblock(microblock_header_1, microblock_header_2) => {
                if microblock_header_1.sequence != microblock_header_2.sequence
                    || microblock_header_1.prev_block != microblock_header_2.prev_block
                    || microblock_header_1.version != microblock_header_2.version
                {
                    return Err(MemPoolRejection::PoisonMicroblocksDoNotConflict);
                }

                let microblock_pkh_1 = microblock_header_1
                    .check_recover_pubkey()
                    .map_err(|_e| MemPoolRejection::InvalidMicroblocks)?;
                let microblock_pkh_2 = microblock_header_2
                    .check_recover_pubkey()
                    .map_err(|_e| MemPoolRejection::InvalidMicroblocks)?;

                if microblock_pkh_1 != microblock_pkh_2 {
                    return Err(MemPoolRejection::PoisonMicroblocksDoNotConflict);
                }

                if !has_microblock_pubkey {
                    return Err(MemPoolRejection::NoAnchorBlockWithPubkeyHash(
                        microblock_pkh_1,
                    ));
                }
            }
            TransactionPayload::Coinbase(_) => return Err(MemPoolRejection::NoCoinbaseViaMempool),
        };

        Ok(())
    }
}

#[cfg(test)]
pub mod test {
    use std::fs;

    use rand::thread_rng;
    use rand::Rng;

    use burnchains::*;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::*;
    use chainstate::stacks::db::test::*;
    use chainstate::stacks::db::*;
    use chainstate::stacks::miner::test::*;
    use chainstate::stacks::test::*;
    use chainstate::stacks::Error as chainstate_error;
    use chainstate::stacks::*;
    use core::mempool::*;
    use net::test::*;
    use util::db::Error as db_error;
    use util::db::*;
    use util::hash::*;
    use util::retry::*;

    use crate::types::chainstate::{BlockHeaderHash, StacksWorkScore};

    use super::*;

    pub fn make_empty_coinbase_block(mblock_key: &StacksPrivateKey) -> StacksBlock {
        let privk = StacksPrivateKey::from_hex(
            "59e4d5e18351d6027a37920efe53c2f1cbadc50dca7d77169b7291dff936ed6d01",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let proof_bytes = hex_bytes("9275df67a68c8745c0ff97b48201ee6db447f7c93b23ae24cdc2400f52fdb08a1a6ac7ec71bf9c9c76e96ee4675ebff60625af28718501047bfd87b810c2d2139b73c23bd69de66360953a642c2a330a").unwrap();
        let proof = VRFProof::from_bytes(&proof_bytes[..].to_vec()).unwrap();

        let mut tx_coinbase = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth,
            TransactionPayload::Coinbase(CoinbasePayload([0u8; 32])),
        );
        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);

        tx_signer.sign_origin(&privk).unwrap();

        let tx_coinbase_signed = tx_signer.get_tx().unwrap();
        let txs = vec![tx_coinbase_signed];

        let work_score = StacksWorkScore {
            burn: 123,
            work: 456,
        };

        let parent_header = StacksBlockHeader {
            version: 0x01,
            total_work: StacksWorkScore {
                burn: 234,
                work: 567,
            },
            proof: proof.clone(),
            parent_block: BlockHeaderHash([5u8; 32]),
            parent_microblock: BlockHeaderHash([6u8; 32]),
            parent_microblock_sequence: 4,
            tx_merkle_root: Sha512Trunc256Sum([7u8; 32]),
            state_index_root: TrieHash([8u8; 32]),
            microblock_pubkey_hash: Hash160([9u8; 20]),
        };

        let parent_microblock_header = StacksMicroblockHeader {
            version: 0x12,
            sequence: 0x34,
            prev_block: BlockHeaderHash([0x0au8; 32]),
            tx_merkle_root: Sha512Trunc256Sum([0x0bu8; 32]),
            signature: MessageSignature([0x0cu8; 65]),
        };

        let mblock_pubkey_hash =
            Hash160::from_node_public_key(&StacksPublicKey::from_private(mblock_key));
        let mut block = StacksBlock::from_parent(
            &parent_header,
            &parent_microblock_header,
            txs.clone(),
            &work_score,
            &proof,
            &TrieHash([2u8; 32]),
            &mblock_pubkey_hash,
        );
        block.header.version = 0x24;
        block
    }

    pub fn make_16k_block(mblock_key: &StacksPrivateKey) -> StacksBlock {
        let privk = StacksPrivateKey::from_hex(
            "59e4d5e18351d6027a37920efe53c2f1cbadc50dca7d77169b7291dff936ed6d01",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let proof_bytes = hex_bytes("9275df67a68c8745c0ff97b48201ee6db447f7c93b23ae24cdc2400f52fdb08a1a6ac7ec71bf9c9c76e96ee4675ebff60625af28718501047bfd87b810c2d2139b73c23bd69de66360953a642c2a330a").unwrap();
        let proof = VRFProof::from_bytes(&proof_bytes[..].to_vec()).unwrap();

        let mut tx_coinbase = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::Coinbase(CoinbasePayload([0u8; 32])),
        );
        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);

        tx_signer.sign_origin(&privk).unwrap();

        let tx_coinbase_signed = tx_signer.get_tx().unwrap();

        // 16k + 8 contract
        let contract_16k = {
            let mut parts = vec![];
            parts.push("(begin ".to_string());
            for i in 0..1024 {
                parts.push("(print \"abcdef\")".to_string()); // 16 bytes
            }
            parts.push(")".to_string());
            parts.join("")
        };

        let mut tx_big_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::new_smart_contract(
                &format!("hello-world-{}", &thread_rng().gen::<u32>()),
                &contract_16k.to_string(),
            )
            .unwrap(),
        );

        tx_big_contract.anchor_mode = TransactionAnchorMode::OnChainOnly;
        let mut tx_signer = StacksTransactionSigner::new(&tx_big_contract);
        tx_signer.sign_origin(&privk).unwrap();

        let tx_big_contract_signed = tx_signer.get_tx().unwrap();

        let txs = vec![tx_coinbase_signed, tx_big_contract_signed];

        let work_score = StacksWorkScore {
            burn: 123,
            work: 456,
        };

        let parent_header = StacksBlockHeader {
            version: 0x01,
            total_work: StacksWorkScore {
                burn: 234,
                work: 567,
            },
            proof: proof.clone(),
            parent_block: BlockHeaderHash([5u8; 32]),
            parent_microblock: BlockHeaderHash([6u8; 32]),
            parent_microblock_sequence: 4,
            tx_merkle_root: Sha512Trunc256Sum([7u8; 32]),
            state_index_root: TrieHash([8u8; 32]),
            microblock_pubkey_hash: Hash160([9u8; 20]),
        };

        let parent_microblock_header = StacksMicroblockHeader {
            version: 0x12,
            sequence: 0x34,
            prev_block: BlockHeaderHash([0x0au8; 32]),
            tx_merkle_root: Sha512Trunc256Sum([0x0bu8; 32]),
            signature: MessageSignature([0x0cu8; 65]),
        };

        let mblock_pubkey_hash =
            Hash160::from_node_public_key(&StacksPublicKey::from_private(mblock_key));
        let mut block = StacksBlock::from_parent(
            &parent_header,
            &parent_microblock_header,
            txs.clone(),
            &work_score,
            &proof,
            &TrieHash([2u8; 32]),
            &mblock_pubkey_hash,
        );
        block.header.version = 0x24;
        block
    }

    pub fn make_sample_microblock_stream_fork(
        privk: &StacksPrivateKey,
        base: &BlockHeaderHash,
        initial_seq: u16,
    ) -> Vec<StacksMicroblock> {
        let mut all_txs = vec![];
        let mut microblocks: Vec<StacksMicroblock> = vec![];

        let mut rng = thread_rng();
        for i in 0..49 {
            let random_bytes = rng.gen::<[u8; 8]>();
            let random_bytes_str = to_hex(&random_bytes);
            let auth = TransactionAuth::from_p2pkh(&privk).unwrap();

            // 16k + 8 contract
            let contract_16k = {
                let mut parts = vec![];
                parts.push("(begin ".to_string());
                for i in 0..1024 {
                    parts.push("(print \"abcdef\")".to_string()); // 16 bytes
                }
                parts.push(")".to_string());
                parts.join("")
            };

            let mut tx_big_contract = StacksTransaction::new(
                TransactionVersion::Testnet,
                auth.clone(),
                TransactionPayload::new_smart_contract(
                    &format!("hello-world-{}", &thread_rng().gen::<u32>()),
                    &contract_16k.to_string(),
                )
                .unwrap(),
            );

            tx_big_contract.anchor_mode = TransactionAnchorMode::OffChainOnly;
            let mut tx_signer = StacksTransactionSigner::new(&tx_big_contract);
            tx_signer.sign_origin(&privk).unwrap();

            let tx_big_contract_signed = tx_signer.get_tx().unwrap();
            all_txs.push(tx_big_contract_signed);
        }

        // make microblocks with 3 transactions each (or fewer)
        for i in 0..(all_txs.len() / 3) {
            let txs = vec![
                all_txs[3 * i].clone(),
                all_txs[3 * i + 1].clone(),
                all_txs[3 * i + 2].clone(),
            ];

            let txid_vecs = txs.iter().map(|tx| tx.txid().as_bytes().to_vec()).collect();

            let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);
            let tx_merkle_root = merkle_tree.root();

            let prev_block = if i == 0 {
                base.clone()
            } else {
                let l = microblocks.len();
                microblocks[l - 1].block_hash()
            };

            let header = StacksMicroblockHeader {
                version: 0x12,
                sequence: initial_seq + (i as u16),
                prev_block: prev_block,
                tx_merkle_root: tx_merkle_root,
                signature: MessageSignature([0u8; 65]),
            };

            let mut mblock = StacksMicroblock {
                header: header,
                txs: txs,
            };

            mblock.sign(privk).unwrap();
            microblocks.push(mblock);
        }

        microblocks
    }

    pub fn make_sample_microblock_stream(
        privk: &StacksPrivateKey,
        anchored_block_hash: &BlockHeaderHash,
    ) -> Vec<StacksMicroblock> {
        make_sample_microblock_stream_fork(privk, anchored_block_hash, 0)
    }

    fn resign_microblocks(
        microblocks: &mut Vec<StacksMicroblock>,
        privk: &StacksPrivateKey,
    ) -> BlockHeaderHash {
        for i in 0..microblocks.len() {
            microblocks[i].header.signature = MessageSignature([0u8; 65]);
            microblocks[i].sign(privk).unwrap();
            if i + 1 < microblocks.len() {
                microblocks[i + 1].header.prev_block = microblocks[i].block_hash();
            }
        }
        let l = microblocks.len();
        microblocks[l - 1].block_hash()
    }

    fn assert_block_staging_not_processed(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
    ) -> () {
        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_some());
        assert_eq!(
            StacksChainState::load_staging_block_data(
                &chainstate.db(),
                &chainstate.blocks_path,
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            *block
        );
        assert_eq!(
            StacksChainState::get_staging_block_status(
                &chainstate.db(),
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            false
        );

        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(consensus_hash, &block.block_hash());
        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_hash)
                .unwrap()
        );
    }

    fn assert_block_not_stored(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
    ) -> () {
        assert!(!StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap());
        assert_eq!(
            StacksChainState::load_staging_block_pubkey_hash(
                &chainstate.db(),
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            block.header.microblock_pubkey_hash
        );
    }

    fn assert_block_stored_rejected(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
    ) -> () {
        assert!(StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap());
        assert!(StacksChainState::load_block(
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_none());
        assert!(StacksChainState::load_block_header(
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_none());
        assert!(StacksChainState::load_staging_block_pubkey_hash(
            &chainstate.db(),
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_none());

        assert_eq!(
            StacksChainState::get_staging_block_status(
                &chainstate.db(),
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            true
        );
        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_none());

        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(consensus_hash, &block.block_hash());
        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_hash)
                .unwrap()
        );
    }

    fn assert_block_stored_not_staging(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
    ) -> () {
        assert!(StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap());
        assert!(StacksChainState::load_block(
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_some());
        assert_eq!(
            StacksChainState::load_block(
                &chainstate.blocks_path,
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            *block
        );
        assert_eq!(
            StacksChainState::load_block_header(
                &chainstate.blocks_path,
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            block.header
        );
        assert!(StacksChainState::load_staging_block_pubkey_hash(
            &chainstate.db(),
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_none());

        assert_eq!(
            StacksChainState::get_staging_block_status(
                &chainstate.db(),
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            true
        );
        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_none());

        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(consensus_hash, &block.block_hash());
        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_hash)
                .unwrap()
        );
    }

    pub fn store_staging_block(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
        parent_consensus_hash: &ConsensusHash,
        commit_burn: u64,
        sortition_burn: u64,
    ) {
        let blocks_path = chainstate.blocks_path.clone();
        let mut tx = chainstate.db_tx_begin().unwrap();
        StacksChainState::store_staging_block(
            &mut tx,
            &blocks_path,
            consensus_hash,
            block,
            parent_consensus_hash,
            commit_burn,
            sortition_burn,
            5,
        )
        .unwrap();
        tx.commit().unwrap();

        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(consensus_hash, &block.block_hash());
        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_hash)
                .unwrap()
        );
    }

    pub fn store_staging_microblock(
        chainstate: &mut StacksChainState,
        parent_consensus_hash: &ConsensusHash,
        parent_anchored_block_hash: &BlockHeaderHash,
        microblock: &StacksMicroblock,
    ) {
        let mut tx = chainstate.db_tx_begin().unwrap();
        StacksChainState::store_staging_microblock(
            &mut tx,
            parent_consensus_hash,
            parent_anchored_block_hash,
            microblock,
        )
        .unwrap();
        tx.commit().unwrap();

        let parent_index_block_hash = StacksBlockHeader::make_index_block_hash(
            parent_consensus_hash,
            parent_anchored_block_hash,
        );
        assert!(chainstate
            .has_microblocks_indexed(&parent_index_block_hash)
            .unwrap());
    }

    pub fn set_block_processed(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
        accept: bool,
    ) {
        let index_block_hash =
            StacksBlockHeader::make_index_block_hash(consensus_hash, anchored_block_hash);
        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_hash)
                .unwrap()
        );
        let blocks_path = chainstate.blocks_path.clone();

        let mut tx = chainstate.db_tx_begin().unwrap();
        StacksChainState::set_block_processed(
            &mut tx,
            None,
            &blocks_path,
            consensus_hash,
            anchored_block_hash,
            accept,
        )
        .unwrap();
        tx.commit().unwrap();

        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_hash)
                .unwrap()
        );
    }

    pub fn set_block_orphaned(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
    ) {
        let blocks_path = chainstate.blocks_path.clone();

        let mut tx = chainstate.db_tx_begin().unwrap();
        StacksChainState::set_block_orphaned(
            &mut tx,
            &blocks_path,
            consensus_hash,
            anchored_block_hash,
        )
        .unwrap();
        tx.commit().unwrap();
    }

    pub fn set_microblocks_processed(
        chainstate: &mut StacksChainState,
        child_consensus_hash: &ConsensusHash,
        child_anchored_block_hash: &BlockHeaderHash,
        tail_microblock_hash: &BlockHeaderHash,
    ) {
        let child_index_block_hash = StacksBlockHeader::make_index_block_hash(
            child_consensus_hash,
            child_anchored_block_hash,
        );
        let (parent_consensus_hash, parent_block_hash) =
            StacksChainState::get_parent_block_header_hashes(
                &chainstate.db(),
                &child_index_block_hash,
            )
            .unwrap()
            .unwrap();
        let parent_index_block_hash =
            StacksBlockHeader::make_index_block_hash(&parent_consensus_hash, &parent_block_hash);

        let parent_microblock_index_hash =
            StacksBlockHeader::make_index_block_hash(&parent_consensus_hash, &tail_microblock_hash);

        let mut tx = chainstate.db_tx_begin().unwrap();

        StacksChainState::set_microblocks_processed(
            &mut tx,
            child_consensus_hash,
            child_anchored_block_hash,
            &tail_microblock_hash,
        )
        .unwrap();
        tx.commit().unwrap();

        assert!(chainstate
            .has_microblocks_indexed(&parent_index_block_hash)
            .unwrap());
        assert!(StacksChainState::has_processed_microblocks_indexed(
            chainstate.db(),
            &parent_microblock_index_hash
        )
        .unwrap());
    }

    fn process_next_orphaned_staging_block(chainstate: &mut StacksChainState) -> bool {
        let blocks_path = chainstate.blocks_path.clone();
        let mut tx = chainstate.db_tx_begin().unwrap();
        let res =
            StacksChainState::process_next_orphaned_staging_block(&mut tx, &blocks_path).unwrap();
        tx.commit().unwrap();
        res
    }

    fn drop_staging_microblocks(
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        anchored_block_hash: &BlockHeaderHash,
        invalid_microblock: &BlockHeaderHash,
    ) {
        let mut tx = chainstate.db_tx_begin().unwrap();
        StacksChainState::drop_staging_microblocks(
            &mut tx,
            consensus_hash,
            anchored_block_hash,
            invalid_microblock,
        )
        .unwrap();
        tx.commit().unwrap();
    }

    #[test]
    fn stacks_db_block_load_store_empty() {
        let chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_block_load_store_empty");

        let path = StacksChainState::get_block_path(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        )
        .unwrap();
        assert!(fs::metadata(&path).is_err());
        assert!(!StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([2u8; 32])
        )
        .unwrap());

        StacksChainState::store_empty_block(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([2u8; 32]),
        )
        .unwrap();
        assert!(fs::metadata(&path).is_ok());

        // empty block is considered _not_ stored
        assert!(!StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([2u8; 32])
        )
        .unwrap());
        assert!(StacksChainState::load_block(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &BlockHeaderHash([2u8; 32])
        )
        .unwrap()
        .is_none());
    }

    #[test]
    fn stacks_db_block_load_store() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_block_load_store");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let mut block = make_empty_coinbase_block(&privk);

        // don't worry about freeing microblcok state yet
        block.header.parent_microblock_sequence = 0;
        block.header.parent_microblock = EMPTY_MICROBLOCK_PARENT_HASH.clone();

        let path = StacksChainState::get_block_path(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash(),
        )
        .unwrap();
        assert!(fs::metadata(&path).is_err());
        assert!(!StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap());

        assert!(!StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap());

        store_staging_block(
            &mut chainstate,
            &ConsensusHash([1u8; 20]),
            &block,
            &ConsensusHash([2u8; 20]),
            1,
            2,
        );

        set_block_processed(
            &mut chainstate,
            &ConsensusHash([1u8; 20]),
            &block.block_hash(),
            true,
        );

        assert!(StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap());

        assert!(StacksChainState::load_block(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap()
        .is_some());
        assert_eq!(
            StacksChainState::load_block(
                &chainstate.blocks_path,
                &ConsensusHash([1u8; 20]),
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            block
        );
        assert_eq!(
            StacksChainState::load_block_header(
                &chainstate.blocks_path,
                &ConsensusHash([1u8; 20]),
                &block.block_hash()
            )
            .unwrap()
            .unwrap(),
            block.header
        );

        StacksChainState::free_block_state(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.header,
        );

        // database determines that it's still there
        assert!(StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap());
        assert!(StacksChainState::load_block(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap()
        .is_none());

        set_block_processed(
            &mut chainstate,
            &ConsensusHash([1u8; 20]),
            &block.block_hash(),
            false,
        );

        // still technically stored -- we processed it
        assert!(StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap());

        let mut dbtx = chainstate.db_tx_begin().unwrap();
        StacksChainState::forget_orphaned_epoch_data(
            &mut dbtx,
            &ConsensusHash([1u8; 20]),
            &block.block_hash(),
        )
        .unwrap();
        dbtx.commit().unwrap();

        // *now* it's not there
        assert!(!StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap());

        assert!(StacksChainState::load_block(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap()
        .is_none());
        assert!(StacksChainState::load_block_header(
            &chainstate.blocks_path,
            &ConsensusHash([1u8; 20]),
            &block.block_hash()
        )
        .unwrap()
        .is_none());
    }

    #[test]
    fn stacks_db_staging_block_load_store_accept() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_block_load_store_accept",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);

        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([2u8; 20]),
            &block.block_hash()
        )
        .unwrap()
        .is_none());

        store_staging_block(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block,
            &ConsensusHash([1u8; 20]),
            1,
            2,
        );

        assert_block_staging_not_processed(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_not_stored(&mut chainstate, &ConsensusHash([2u8; 20]), &block);

        set_block_processed(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            true,
        );

        assert_block_stored_not_staging(&mut chainstate, &ConsensusHash([2u8; 20]), &block);

        // should be idempotent
        set_block_processed(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            true,
        );

        assert_block_stored_not_staging(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
    }

    #[test]
    fn stacks_db_staging_block_load_store_reject() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_block_load_store_reject",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);

        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([2u8; 20]),
            &block.block_hash()
        )
        .unwrap()
        .is_none());

        store_staging_block(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block,
            &ConsensusHash([1u8; 20]),
            1,
            2,
        );

        assert_block_staging_not_processed(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_not_stored(&mut chainstate, &ConsensusHash([2u8; 20]), &block);

        set_block_processed(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            false,
        );

        assert_block_stored_rejected(&mut chainstate, &ConsensusHash([2u8; 20]), &block);

        // should be idempotent
        set_block_processed(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            false,
        );

        assert_block_stored_rejected(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
    }

    #[test]
    fn stacks_db_load_store_microblock_stream() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_load_store_microblock_stream");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let microblocks = make_sample_microblock_stream(&privk, &block.block_hash());

        assert!(!StacksChainState::has_stored_block(
            &chainstate.db(),
            &chainstate.blocks_path,
            &ConsensusHash([2u8; 20]),
            &microblocks[0].block_hash()
        )
        .unwrap());

        assert!(StacksChainState::load_microblock_stream_fork(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks.last().as_ref().unwrap().block_hash(),
        )
        .unwrap()
        .is_none());

        for mblock in microblocks.iter() {
            store_staging_microblock(
                &mut chainstate,
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                mblock,
            );
        }

        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            microblocks
        );

        // not processed
        assert!(StacksChainState::load_processed_microblock_stream_fork(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks.last().as_ref().unwrap().block_hash(),
        )
        .unwrap()
        .is_none());
    }

    #[test]
    fn stacks_db_staging_microblock_stream_load_store_confirm_all() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_microblock_stream_load_store_confirm_all",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let microblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        let mut child_block = make_empty_coinbase_block(&privk);

        child_block.header.parent_block = block.block_hash();
        child_block.header.parent_microblock = microblocks.last().as_ref().unwrap().block_hash();
        child_block.header.parent_microblock_sequence =
            microblocks.last().as_ref().unwrap().header.sequence;

        assert!(StacksChainState::load_staging_microblock(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks[0].block_hash()
        )
        .unwrap()
        .is_none());

        assert!(StacksChainState::load_descendant_staging_microblock_stream(
            &chainstate.db(),
            &StacksBlockHeader::make_index_block_hash(
                &ConsensusHash([2u8; 20]),
                &block.block_hash()
            ),
            0,
            u16::max_value()
        )
        .unwrap()
        .is_none());

        store_staging_block(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block,
            &ConsensusHash([1u8; 20]),
            1,
            2,
        );
        for mb in microblocks.iter() {
            store_staging_microblock(
                &mut chainstate,
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                mb,
            );
        }
        store_staging_block(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block,
            &ConsensusHash([2u8; 20]),
            1,
            2,
        );

        // block should be stored to staging
        assert_block_staging_not_processed(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_staging_not_processed(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block,
        );

        // microblock stream should be stored to staging
        assert!(StacksChainState::load_staging_microblock(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks[0].block_hash()
        )
        .unwrap()
        .is_some());

        assert_eq!(
            StacksChainState::load_staging_microblock(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks[0].block_hash()
            )
            .unwrap()
            .unwrap()
            .try_into_microblock()
            .unwrap(),
            microblocks[0]
        );
        assert_eq!(
            StacksChainState::load_descendant_staging_microblock_stream(
                &chainstate.db(),
                &StacksBlockHeader::make_index_block_hash(
                    &ConsensusHash([2u8; 20]),
                    &block.block_hash()
                ),
                0,
                u16::max_value()
            )
            .unwrap()
            .unwrap(),
            microblocks
        );

        // block should _not_ be in the chunk store
        assert_block_not_stored(&mut chainstate, &ConsensusHash([2u8; 20]), &block);

        // microblocks present
        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            microblocks
        );

        // microblocks not processed yet
        assert!(StacksChainState::load_processed_microblock_stream_fork(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks.last().as_ref().unwrap().block_hash(),
        )
        .unwrap()
        .is_none());

        set_block_processed(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            true,
        );
        set_block_processed(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block.block_hash(),
            true,
        );
        set_microblocks_processed(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block.block_hash(),
            &microblocks.last().as_ref().unwrap().block_hash(),
        );

        // block should be stored to chunk store now
        assert_block_stored_not_staging(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_stored_not_staging(&mut chainstate, &ConsensusHash([3u8; 20]), &child_block);

        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            microblocks
        );

        // microblocks should be absent from staging
        for mb in microblocks.iter() {
            assert!(chainstate
                .get_microblock_status(
                    &ConsensusHash([2u8; 20]),
                    &block.block_hash(),
                    &mb.block_hash()
                )
                .unwrap()
                .is_some());
            assert_eq!(
                chainstate
                    .get_microblock_status(
                        &ConsensusHash([2u8; 20]),
                        &block.block_hash(),
                        &mb.block_hash()
                    )
                    .unwrap()
                    .unwrap(),
                true
            );
        }

        // but we should still load the full stream if asked
        assert!(StacksChainState::load_descendant_staging_microblock_stream(
            &chainstate.db(),
            &StacksBlockHeader::make_index_block_hash(
                &ConsensusHash([2u8; 20]),
                &block.block_hash()
            ),
            0,
            u16::max_value()
        )
        .unwrap()
        .is_some());
        assert_eq!(
            StacksChainState::load_descendant_staging_microblock_stream(
                &chainstate.db(),
                &StacksBlockHeader::make_index_block_hash(
                    &ConsensusHash([2u8; 20]),
                    &block.block_hash()
                ),
                0,
                u16::max_value()
            )
            .unwrap()
            .unwrap(),
            microblocks
        );
    }

    #[test]
    fn stacks_db_staging_microblock_stream_load_store_partial_confirm() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_microblock_stream_load_store_partial_confirm",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let microblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        let mut child_block = make_empty_coinbase_block(&privk);

        child_block.header.parent_block = block.block_hash();
        child_block.header.parent_microblock = microblocks.first().as_ref().unwrap().block_hash();
        child_block.header.parent_microblock_sequence =
            microblocks.first().as_ref().unwrap().header.sequence;

        assert!(StacksChainState::load_staging_microblock(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks[0].block_hash()
        )
        .unwrap()
        .is_none());
        assert!(StacksChainState::load_descendant_staging_microblock_stream(
            &chainstate.db(),
            &StacksBlockHeader::make_index_block_hash(
                &ConsensusHash([2u8; 20]),
                &block.block_hash()
            ),
            0,
            u16::max_value()
        )
        .unwrap()
        .is_none());

        store_staging_block(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block,
            &ConsensusHash([1u8; 20]),
            1,
            2,
        );
        for mb in microblocks.iter() {
            store_staging_microblock(
                &mut chainstate,
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                mb,
            );
        }
        store_staging_block(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block,
            &ConsensusHash([2u8; 20]),
            1,
            2,
        );

        // block should be stored to staging
        assert_block_staging_not_processed(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_staging_not_processed(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block,
        );
        assert_block_not_stored(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_not_stored(&mut chainstate, &ConsensusHash([3u8; 20]), &child_block);

        // microblock stream should be stored to staging
        assert!(StacksChainState::load_staging_microblock(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks[0].block_hash()
        )
        .unwrap()
        .is_some());
        assert_eq!(
            StacksChainState::load_staging_microblock(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks[0].block_hash()
            )
            .unwrap()
            .unwrap()
            .try_into_microblock()
            .unwrap(),
            microblocks[0]
        );
        assert_eq!(
            StacksChainState::load_descendant_staging_microblock_stream(
                &chainstate.db(),
                &StacksBlockHeader::make_index_block_hash(
                    &ConsensusHash([2u8; 20]),
                    &block.block_hash()
                ),
                0,
                u16::max_value()
            )
            .unwrap()
            .unwrap(),
            microblocks
        );
        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            microblocks
        );

        // not processed
        assert!(StacksChainState::load_processed_microblock_stream_fork(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks.last().as_ref().unwrap().block_hash(),
        )
        .unwrap()
        .is_none());

        // confirm the 0th microblock, but not the 1st or later.
        // do not confirm the block.
        set_block_processed(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            true,
        );
        set_block_processed(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block.block_hash(),
            true,
        );
        set_microblocks_processed(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block.block_hash(),
            &microblocks[0].block_hash(),
        );

        // block should be processed in staging, but the data should not be in the staging DB
        assert_block_stored_not_staging(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_stored_not_staging(&mut chainstate, &ConsensusHash([3u8; 20]), &child_block);

        // microblocks should not be in the chunk store, except for block 0 which was confirmed
        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            microblocks
        );

        assert_eq!(
            StacksChainState::load_processed_microblock_stream_fork(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks.first().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            vec![microblocks[0].clone()]
        );

        assert_eq!(
            StacksChainState::load_processed_microblock_stream_fork(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks[1].block_hash(),
            )
            .unwrap(),
            None
        );

        // microblocks should be present in staging, except for block 0
        for mb in microblocks.iter() {
            assert!(chainstate
                .get_microblock_status(
                    &ConsensusHash([2u8; 20]),
                    &block.block_hash(),
                    &mb.block_hash()
                )
                .unwrap()
                .is_some());

            if mb.header.sequence == 0 {
                assert_eq!(
                    chainstate
                        .get_microblock_status(
                            &ConsensusHash([2u8; 20]),
                            &block.block_hash(),
                            &mb.block_hash()
                        )
                        .unwrap()
                        .unwrap(),
                    true
                );
            } else {
                // not processed since seq=0 was the last block to be accepted
                assert_eq!(
                    chainstate
                        .get_microblock_status(
                            &ConsensusHash([2u8; 20]),
                            &block.block_hash(),
                            &mb.block_hash()
                        )
                        .unwrap()
                        .unwrap(),
                    false
                );
            }
        }

        // can load the entire stream still
        assert!(StacksChainState::load_descendant_staging_microblock_stream(
            &chainstate.db(),
            &StacksBlockHeader::make_index_block_hash(
                &ConsensusHash([2u8; 20]),
                &block.block_hash()
            ),
            0,
            u16::max_value()
        )
        .unwrap()
        .is_some());
        assert_eq!(
            StacksChainState::load_descendant_staging_microblock_stream(
                &chainstate.db(),
                &StacksBlockHeader::make_index_block_hash(
                    &ConsensusHash([2u8; 20]),
                    &block.block_hash()
                ),
                0,
                u16::max_value()
            )
            .unwrap()
            .unwrap(),
            microblocks
        );
    }

    #[test]
    fn stacks_db_staging_microblock_stream_load_continuous_streams() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_microblock_stream_load_continuous_streams",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let microblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        let mut child_block = make_empty_coinbase_block(&privk);

        child_block.header.parent_block = block.block_hash();
        child_block.header.parent_microblock = microblocks.first().as_ref().unwrap().block_hash();
        child_block.header.parent_microblock_sequence =
            microblocks.first().as_ref().unwrap().header.sequence;

        assert!(StacksChainState::load_staging_microblock(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks[0].block_hash()
        )
        .unwrap()
        .is_none());
        assert!(StacksChainState::load_descendant_staging_microblock_stream(
            &chainstate.db(),
            &StacksBlockHeader::make_index_block_hash(
                &ConsensusHash([2u8; 20]),
                &block.block_hash()
            ),
            0,
            u16::max_value()
        )
        .unwrap()
        .is_none());

        store_staging_block(
            &mut chainstate,
            &ConsensusHash([2u8; 20]),
            &block,
            &ConsensusHash([1u8; 20]),
            1,
            2,
        );

        // don't store the first microblock, but store the rest
        for (i, mb) in microblocks.iter().enumerate() {
            if i > 0 {
                store_staging_microblock(
                    &mut chainstate,
                    &ConsensusHash([2u8; 20]),
                    &block.block_hash(),
                    mb,
                );
            }
        }
        store_staging_block(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block,
            &ConsensusHash([2u8; 20]),
            1,
            2,
        );

        // block should be stored to staging
        assert_block_staging_not_processed(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_staging_not_processed(
            &mut chainstate,
            &ConsensusHash([3u8; 20]),
            &child_block,
        );
        assert_block_not_stored(&mut chainstate, &ConsensusHash([2u8; 20]), &block);
        assert_block_not_stored(&mut chainstate, &ConsensusHash([3u8; 20]), &child_block);

        // missing head
        assert!(StacksChainState::load_staging_microblock(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks[0].block_hash()
        )
        .unwrap()
        .is_none());

        // subsequent microblock stream should be stored to staging
        assert!(StacksChainState::load_staging_microblock(
            &chainstate.db(),
            &ConsensusHash([2u8; 20]),
            &block.block_hash(),
            &microblocks[1].block_hash()
        )
        .unwrap()
        .is_some());
        assert_eq!(
            StacksChainState::load_staging_microblock(
                &chainstate.db(),
                &ConsensusHash([2u8; 20]),
                &block.block_hash(),
                &microblocks[1].block_hash()
            )
            .unwrap()
            .unwrap()
            .try_into_microblock()
            .unwrap(),
            microblocks[1]
        );

        // can't load descendent stream because missing head
        assert!(StacksChainState::load_descendant_staging_microblock_stream(
            &chainstate.db(),
            &StacksBlockHeader::make_index_block_hash(
                &ConsensusHash([2u8; 20]),
                &block.block_hash()
            ),
            0,
            u16::max_value()
        )
        .unwrap()
        .is_none());
    }

    #[test]
    fn stacks_db_validate_parent_microblock_stream() {
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();
        let block = make_empty_coinbase_block(&privk);
        let microblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        let num_mblocks = microblocks.len();

        let proof_bytes = hex_bytes("9275df67a68c8745c0ff97b48201ee6db447f7c93b23ae24cdc2400f52fdb08a1a6ac7ec71bf9c9c76e96ee4675ebff60625af28718501047bfd87b810c2d2139b73c23bd69de66360953a642c2a330a").unwrap();
        let proof = VRFProof::from_bytes(&proof_bytes[..].to_vec()).unwrap();

        let child_block_header = StacksBlockHeader {
            version: 0x01,
            total_work: StacksWorkScore {
                burn: 234,
                work: 567,
            },
            proof: proof.clone(),
            parent_block: block.block_hash(),
            parent_microblock: microblocks[num_mblocks - 1].block_hash(),
            parent_microblock_sequence: microblocks[num_mblocks - 1].header.sequence,
            tx_merkle_root: Sha512Trunc256Sum([7u8; 32]),
            state_index_root: TrieHash([8u8; 32]),
            microblock_pubkey_hash: Hash160([9u8; 20]),
        };

        // contiguous, non-empty stream
        {
            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &child_block_header,
                &microblocks,
                true,
            );
            assert!(res.is_some());

            let (cutoff, poison_opt) = res.unwrap();
            assert!(poison_opt.is_none());
            assert_eq!(cutoff, num_mblocks);
        }

        // empty stream
        {
            let mut child_block_header_empty = child_block_header.clone();
            child_block_header_empty.parent_microblock = EMPTY_MICROBLOCK_PARENT_HASH.clone();
            child_block_header_empty.parent_microblock_sequence = 0;

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &child_block_header_empty,
                &vec![],
                true,
            );
            assert!(res.is_some());

            let (cutoff, poison_opt) = res.unwrap();
            assert!(poison_opt.is_none());
            assert_eq!(cutoff, 0);
        }

        // non-empty stream, but child drops all microblocks
        {
            let mut child_block_header_empty = child_block_header.clone();
            child_block_header_empty.parent_microblock = EMPTY_MICROBLOCK_PARENT_HASH.clone();
            child_block_header_empty.parent_microblock_sequence = 0;

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &child_block_header_empty,
                &microblocks,
                true,
            );
            assert!(res.is_some());

            let (cutoff, poison_opt) = res.unwrap();
            assert!(poison_opt.is_none());
            assert_eq!(cutoff, 0);
        }

        // non-empty stream, but child drops some microblocks
        {
            for i in 0..num_mblocks - 1 {
                let mut child_block_header_trunc = child_block_header.clone();
                child_block_header_trunc.parent_microblock = microblocks[i].block_hash();
                child_block_header_trunc.parent_microblock_sequence =
                    microblocks[i].header.sequence;

                let res = StacksChainState::validate_parent_microblock_stream(
                    &block.header,
                    &child_block_header_trunc,
                    &microblocks,
                    true,
                );
                assert!(res.is_some());

                let (cutoff, poison_opt) = res.unwrap();
                assert!(poison_opt.is_none());
                assert_eq!(cutoff, i + 1);
            }
        }

        // non-empty stream, but child does not identify any block as its parent
        {
            let mut child_block_header_broken = child_block_header.clone();
            child_block_header_broken.parent_microblock = BlockHeaderHash([1u8; 32]);
            child_block_header_broken.parent_microblock_sequence = 5;

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &child_block_header_broken,
                &microblocks,
                true,
            );
            assert!(res.is_none());
        }

        // non-empty stream, but missing first microblock
        {
            let mut broken_microblocks = vec![];
            for i in 1..num_mblocks {
                broken_microblocks.push(microblocks[i].clone());
            }

            let mut new_child_block_header = child_block_header.clone();
            new_child_block_header.parent_microblock =
                resign_microblocks(&mut broken_microblocks, &privk);

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &new_child_block_header,
                &broken_microblocks,
                true,
            );
            assert!(res.is_none());
        }

        // non-empty stream, but missing intermediate microblock
        {
            let mut broken_microblocks = vec![];
            let missing = num_mblocks / 2;
            for i in 0..num_mblocks {
                if i != missing {
                    broken_microblocks.push(microblocks[i].clone());
                }
            }

            let mut new_child_block_header = child_block_header.clone();
            new_child_block_header.parent_microblock =
                resign_microblocks(&mut broken_microblocks, &privk);

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &new_child_block_header,
                &broken_microblocks,
                true,
            );
            assert!(res.is_none());
        }

        // nonempty stream, but discontiguous first microblock (doesn't connect to parent block)
        {
            let mut broken_microblocks = microblocks.clone();
            broken_microblocks[0].header.prev_block = BlockHeaderHash([1u8; 32]);

            let mut new_child_block_header = child_block_header.clone();
            new_child_block_header.parent_microblock =
                resign_microblocks(&mut broken_microblocks, &privk);

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &new_child_block_header,
                &broken_microblocks,
                true,
            );
            assert!(res.is_none());
        }

        // nonempty stream, but discontiguous first microblock (wrong sequence)
        {
            let mut broken_microblocks = microblocks.clone();
            broken_microblocks[0].header.sequence = 1;

            let mut new_child_block_header = child_block_header.clone();
            new_child_block_header.parent_microblock =
                resign_microblocks(&mut broken_microblocks, &privk);

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &new_child_block_header,
                &broken_microblocks,
                true,
            );
            assert!(res.is_none());
        }

        // nonempty stream, but discontiguous hash chain
        {
            let mut broken_microblocks = microblocks.clone();

            let mut new_child_block_header = child_block_header.clone();

            for i in 0..broken_microblocks.len() {
                broken_microblocks[i].header.signature = MessageSignature([0u8; 65]);
                broken_microblocks[i].sign(&privk).unwrap();
                if i + 1 < broken_microblocks.len() {
                    if i != num_mblocks / 2 {
                        broken_microblocks[i + 1].header.prev_block =
                            broken_microblocks[i].block_hash();
                    } else {
                        broken_microblocks[i + 1].header.prev_block = BlockHeaderHash([1u8; 32]);
                    }
                }
            }
            let l = broken_microblocks.len();
            new_child_block_header.parent_microblock = broken_microblocks[l - 1].block_hash();

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &new_child_block_header,
                &broken_microblocks,
                true,
            );
            assert!(res.is_none());
        }

        // nonempty string, but bad signature
        {
            let mut broken_microblocks = microblocks.clone();
            broken_microblocks[num_mblocks / 2].header.signature = MessageSignature([1u8; 65]);

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &child_block_header,
                &broken_microblocks,
                true,
            );
            assert!(res.is_none());
        }

        // deliberate miner fork
        {
            let mut broken_microblocks = microblocks.clone();
            let mut forked_microblocks = vec![];

            let mut new_child_block_header = child_block_header.clone();
            let mut conflicting_microblock = microblocks[0].clone();

            for i in 0..broken_microblocks.len() {
                broken_microblocks[i].header.signature = MessageSignature([0u8; 65]);
                broken_microblocks[i].sign(&privk).unwrap();
                if i + 1 < broken_microblocks.len() {
                    broken_microblocks[i + 1].header.prev_block =
                        broken_microblocks[i].block_hash();
                }

                forked_microblocks.push(broken_microblocks[i].clone());
                if i == num_mblocks / 2 {
                    conflicting_microblock = broken_microblocks[i].clone();

                    let extra_tx = {
                        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
                        let tx_smart_contract = StacksTransaction::new(
                            TransactionVersion::Testnet,
                            auth.clone(),
                            TransactionPayload::new_smart_contract(
                                &"name-contract".to_string(),
                                &format!("conflicting smart contract {}", i),
                            )
                            .unwrap(),
                        );
                        let mut tx_signer = StacksTransactionSigner::new(&tx_smart_contract);
                        tx_signer.sign_origin(&privk).unwrap();
                        tx_signer.get_tx().unwrap()
                    };

                    conflicting_microblock.txs.push(extra_tx);

                    let txid_vecs = conflicting_microblock
                        .txs
                        .iter()
                        .map(|tx| tx.txid().as_bytes().to_vec())
                        .collect();

                    let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);

                    conflicting_microblock.header.tx_merkle_root = merkle_tree.root();

                    conflicting_microblock.sign(&privk).unwrap();
                    forked_microblocks.push(conflicting_microblock.clone());
                }
            }

            let l = broken_microblocks.len();
            new_child_block_header.parent_microblock = broken_microblocks[l - 1].block_hash();

            let res = StacksChainState::validate_parent_microblock_stream(
                &block.header,
                &child_block_header,
                &forked_microblocks,
                true,
            );
            assert!(res.is_some());

            let (cutoff, poison_opt) = res.unwrap();
            assert_eq!(cutoff, num_mblocks / 2);
            assert!(poison_opt.is_some());

            let poison = poison_opt.unwrap();
            match poison {
                TransactionPayload::PoisonMicroblock(ref h1, ref h2) => {
                    assert_eq!(*h2, forked_microblocks[num_mblocks / 2].header);
                    assert_eq!(*h1, conflicting_microblock.header);
                }
                _ => {
                    assert!(false);
                }
            }
        }
    }

    #[test]
    fn stacks_db_staging_block_load_store_accept_attachable() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_block_load_store_accept_attachable",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let mut block_1 = make_empty_coinbase_block(&privk);
        let mut block_2 = make_empty_coinbase_block(&privk);
        let mut block_3 = make_empty_coinbase_block(&privk);
        let mut block_4 = make_empty_coinbase_block(&privk);

        block_1.header.parent_block = FIRST_STACKS_BLOCK_HASH;
        block_2.header.parent_block = block_1.block_hash();
        block_3.header.parent_block = block_2.block_hash();
        block_4.header.parent_block = block_3.block_hash();

        let consensus_hashes = vec![
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
            ConsensusHash([5u8; 20]),
        ];

        let parent_consensus_hashes = vec![
            FIRST_BURNCHAIN_CONSENSUS_HASH,
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
        ];

        let blocks = &[&block_1, &block_2, &block_3, &block_4];

        // store each block
        for ((block, consensus_hash), parent_consensus_hash) in blocks
            .iter()
            .zip(&consensus_hashes)
            .zip(&parent_consensus_hashes)
        {
            assert!(StacksChainState::load_staging_block_data(
                &chainstate.db(),
                &chainstate.blocks_path,
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .is_none());
            store_staging_block(
                &mut chainstate,
                consensus_hash,
                block,
                parent_consensus_hash,
                1,
                2,
            );
            assert_block_staging_not_processed(&mut chainstate, consensus_hash, block);
        }

        // first block is attachable, but all the rest are not
        assert_eq!(
            StacksChainState::load_staging_block(
                &chainstate.db(),
                &chainstate.blocks_path,
                &consensus_hashes[0],
                &block_1.block_hash()
            )
            .unwrap()
            .unwrap()
            .attachable,
            true
        );

        for (block, consensus_hash) in blocks[1..].iter().zip(&consensus_hashes[1..]) {
            assert_eq!(
                StacksChainState::load_staging_block(
                    &chainstate.db(),
                    &chainstate.blocks_path,
                    consensus_hash,
                    &block.block_hash()
                )
                .unwrap()
                .unwrap()
                .attachable,
                false
            );
        }

        // process all blocks, and check that processing a parent makes the child attachable
        for (i, (block, consensus_hash)) in blocks.iter().zip(&consensus_hashes).enumerate() {
            // child block is not attachable
            if i + 1 < consensus_hashes.len() {
                let child_consensus_hash = &consensus_hashes[i + 1];
                let child_block = &blocks[i + 1];
                assert_eq!(
                    StacksChainState::load_staging_block(
                        &chainstate.db(),
                        &chainstate.blocks_path,
                        child_consensus_hash,
                        &child_block.block_hash()
                    )
                    .unwrap()
                    .unwrap()
                    .attachable,
                    false
                );
            }

            // block not stored yet
            assert_block_not_stored(&mut chainstate, consensus_hash, block);

            set_block_processed(&mut chainstate, consensus_hash, &block.block_hash(), true);

            // block is now stored
            assert_block_stored_not_staging(&mut chainstate, consensus_hash, block);

            // child block is attachable
            if i + 1 < consensus_hashes.len() {
                let child_consensus_hash = &consensus_hashes[i + 1];
                let child_block = &blocks[i + 1];
                assert_eq!(
                    StacksChainState::load_staging_block(
                        &chainstate.db(),
                        &chainstate.blocks_path,
                        child_consensus_hash,
                        &child_block.block_hash()
                    )
                    .unwrap()
                    .unwrap()
                    .attachable,
                    true
                );
            }
        }
    }

    #[test]
    fn stacks_db_staging_block_load_store_accept_attachable_reversed() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stx_db_staging_block_load_store_accept_attachable_r",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let mut block_1 = make_empty_coinbase_block(&privk);
        let mut block_2 = make_empty_coinbase_block(&privk);
        let mut block_3 = make_empty_coinbase_block(&privk);
        let mut block_4 = make_empty_coinbase_block(&privk);

        block_1.header.parent_block = FIRST_STACKS_BLOCK_HASH;
        block_2.header.parent_block = block_1.block_hash();
        block_3.header.parent_block = block_2.block_hash();
        block_4.header.parent_block = block_3.block_hash();

        let consensus_hashes = vec![
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
            ConsensusHash([5u8; 20]),
        ];

        let parent_consensus_hashes = vec![
            FIRST_BURNCHAIN_CONSENSUS_HASH,
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
        ];

        let blocks = &[&block_1, &block_2, &block_3, &block_4];

        // store each block, in reverse order!
        for ((block, consensus_hash), parent_consensus_hash) in blocks
            .iter()
            .zip(&consensus_hashes)
            .zip(&parent_consensus_hashes)
            .rev()
        {
            assert!(StacksChainState::load_staging_block_data(
                &chainstate.db(),
                &chainstate.blocks_path,
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .is_none());
            store_staging_block(
                &mut chainstate,
                consensus_hash,
                block,
                parent_consensus_hash,
                1,
                2,
            );
            assert_block_staging_not_processed(&mut chainstate, consensus_hash, block);
        }

        // first block is accepted, but all the rest are not
        assert_eq!(
            StacksChainState::load_staging_block(
                &chainstate.db(),
                &chainstate.blocks_path,
                &consensus_hashes[0],
                &block_1.block_hash()
            )
            .unwrap()
            .unwrap()
            .attachable,
            true
        );

        for (block, consensus_hash) in blocks[1..].iter().zip(&consensus_hashes[1..]) {
            assert_eq!(
                StacksChainState::load_staging_block(
                    &chainstate.db(),
                    &chainstate.blocks_path,
                    consensus_hash,
                    &block.block_hash()
                )
                .unwrap()
                .unwrap()
                .attachable,
                false
            );
        }

        // process all blocks, and check that processing a parent makes the child attachable
        for (i, (block, consensus_hash)) in blocks.iter().zip(&consensus_hashes).enumerate() {
            // child block is not attachable
            if i + 1 < consensus_hashes.len() {
                let child_consensus_hash = &consensus_hashes[i + 1];
                let child_block = &blocks[i + 1];
                assert_eq!(
                    StacksChainState::load_staging_block(
                        &chainstate.db(),
                        &chainstate.blocks_path,
                        child_consensus_hash,
                        &child_block.block_hash()
                    )
                    .unwrap()
                    .unwrap()
                    .attachable,
                    false
                );
            }

            // block not stored yet
            assert_block_not_stored(&mut chainstate, consensus_hash, block);

            set_block_processed(&mut chainstate, consensus_hash, &block.block_hash(), true);

            // block is now stored
            assert_block_stored_not_staging(&mut chainstate, consensus_hash, block);

            // child block is attachable
            if i + 1 < consensus_hashes.len() {
                let child_consensus_hash = &consensus_hashes[i + 1];
                let child_block = &blocks[i + 1];
                assert_eq!(
                    StacksChainState::load_staging_block(
                        &chainstate.db(),
                        &chainstate.blocks_path,
                        child_consensus_hash,
                        &child_block.block_hash()
                    )
                    .unwrap()
                    .unwrap()
                    .attachable,
                    true
                );
            }
        }
    }

    #[test]
    fn stacks_db_staging_block_load_store_accept_attachable_fork() {
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stx_db_staging_block_load_store_accept_attachable_f",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let mut block_1 = make_empty_coinbase_block(&privk);
        let mut block_2 = make_empty_coinbase_block(&privk);
        let mut block_3 = make_empty_coinbase_block(&privk);
        let mut block_4 = make_empty_coinbase_block(&privk);

        //            block_3 -- block_4
        // block_1 --/
        //           \
        //            block_2
        //
        // storing block_1 to staging renders block_2 and block_3 unattachable
        // processing and accepting block_1 renders both block_2 and block_3 attachable again

        block_1.header.parent_block = FIRST_STACKS_BLOCK_HASH;
        block_2.header.parent_block = block_1.block_hash();
        block_3.header.parent_block = block_1.block_hash();
        block_4.header.parent_block = block_3.block_hash();

        let consensus_hashes = vec![
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
            ConsensusHash([5u8; 20]),
        ];

        let parent_consensus_hashes = vec![
            FIRST_BURNCHAIN_CONSENSUS_HASH,
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
        ];

        let blocks = &[&block_1, &block_2, &block_3, &block_4];

        // store each block in reverse order, except for block_1
        for ((block, consensus_hash), parent_consensus_hash) in blocks[1..]
            .iter()
            .zip(&consensus_hashes[1..])
            .zip(&parent_consensus_hashes[1..])
            .rev()
        {
            assert!(StacksChainState::load_staging_block_data(
                &chainstate.db(),
                &chainstate.blocks_path,
                consensus_hash,
                &block.block_hash()
            )
            .unwrap()
            .is_none());
            store_staging_block(
                &mut chainstate,
                consensus_hash,
                block,
                parent_consensus_hash,
                1,
                2,
            );
            assert_block_staging_not_processed(&mut chainstate, consensus_hash, block);
        }

        // blocks 2, 3, and 4 are not attachable since block 1 isn't in staging_blocks
        for (block, consensus_hash) in [&block_2, &block_3, &block_4].iter().zip(&[
            &consensus_hashes[1],
            &consensus_hashes[2],
            &consensus_hashes[3],
        ]) {
            assert_eq!(
                StacksChainState::load_staging_block(
                    &chainstate.db(),
                    &chainstate.blocks_path,
                    consensus_hash,
                    &block.block_hash()
                )
                .unwrap()
                .unwrap()
                .attachable,
                false
            );
        }

        // store block 1
        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            &consensus_hashes[0],
            &block_1.block_hash()
        )
        .unwrap()
        .is_none());
        store_staging_block(
            &mut chainstate,
            &consensus_hashes[0],
            &block_1,
            &parent_consensus_hashes[0],
            1,
            2,
        );
        assert_block_staging_not_processed(&mut chainstate, &consensus_hashes[0], &block_1);

        // first block is attachable
        assert_eq!(
            StacksChainState::load_staging_block(
                &chainstate.db(),
                &chainstate.blocks_path,
                &consensus_hashes[0],
                &block_1.block_hash()
            )
            .unwrap()
            .unwrap()
            .attachable,
            true
        );

        // blocks 2 and 3 are not attachable
        for (block, consensus_hash) in [&block_2, &block_3]
            .iter()
            .zip(&[&consensus_hashes[1], &consensus_hashes[2]])
        {
            assert_eq!(
                StacksChainState::load_staging_block(
                    &chainstate.db(),
                    &chainstate.blocks_path,
                    consensus_hash,
                    &block.block_hash()
                )
                .unwrap()
                .unwrap()
                .attachable,
                false
            );
        }

        // process block 1, and confirm that it makes block 2 and 3 attachable
        assert_block_not_stored(&mut chainstate, &consensus_hashes[0], &block_1);
        set_block_processed(
            &mut chainstate,
            &consensus_hashes[0],
            &block_1.block_hash(),
            true,
        );
        assert_block_stored_not_staging(&mut chainstate, &consensus_hashes[0], &block_1);

        // now block 2 and 3 are attachable
        for (block, consensus_hash) in blocks[1..3].iter().zip(&consensus_hashes[1..3]) {
            assert_eq!(
                StacksChainState::load_staging_block(
                    &chainstate.db(),
                    &chainstate.blocks_path,
                    consensus_hash,
                    &block.block_hash()
                )
                .unwrap()
                .unwrap()
                .attachable,
                true
            );
        }

        // and block 4 is still not
        assert_eq!(
            StacksChainState::load_staging_block(
                &chainstate.db(),
                &chainstate.blocks_path,
                &consensus_hashes[3],
                &block_4.block_hash()
            )
            .unwrap()
            .unwrap()
            .attachable,
            false
        );
    }

    #[test]
    fn stacks_db_staging_microblocks_multiple_descendants() {
        // multiple anchored blocks build off of different microblock parents
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_microblocks_multiple_descendants",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block_1 = make_empty_coinbase_block(&privk);
        let mut block_2 = make_empty_coinbase_block(&privk);
        let mut block_3 = make_empty_coinbase_block(&privk);
        let mut block_4 = make_empty_coinbase_block(&privk);

        let mut mblocks = make_sample_microblock_stream(&privk, &block_1.block_hash());
        mblocks.truncate(3);

        //
        //
        // block_1 --> mblocks[0] --> mblocks[1] --> mblocks[2] --> block_4
        //             \              \
        //              block_2        block_3
        //

        block_2.header.parent_block = block_1.block_hash();
        block_3.header.parent_block = block_1.block_hash();
        block_4.header.parent_block = block_1.block_hash();

        block_2.header.parent_microblock = mblocks[0].block_hash();
        block_2.header.parent_microblock_sequence = mblocks[0].header.sequence;

        block_3.header.parent_microblock = mblocks[1].block_hash();
        block_3.header.parent_microblock_sequence = mblocks[1].header.sequence;

        block_4.header.parent_microblock = mblocks[2].block_hash();
        block_4.header.parent_microblock_sequence = mblocks[2].header.sequence;

        let consensus_hashes = vec![
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
            ConsensusHash([5u8; 20]),
        ];

        let parent_consensus_hash = ConsensusHash([1u8; 20]);

        let blocks = &[&block_1, &block_2, &block_3, &block_4];

        // store all microblocks to staging
        for mblock in mblocks.iter() {
            store_staging_microblock(
                &mut chainstate,
                &consensus_hashes[0],
                &blocks[0].block_hash(),
                mblock,
            );
        }

        // store block 1 to staging
        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            &consensus_hashes[0],
            &blocks[0].block_hash()
        )
        .unwrap()
        .is_none());
        store_staging_block(
            &mut chainstate,
            &consensus_hashes[0],
            &blocks[0],
            &parent_consensus_hash,
            1,
            2,
        );
        assert_block_staging_not_processed(&mut chainstate, &consensus_hashes[0], &blocks[0]);

        set_block_processed(
            &mut chainstate,
            &consensus_hashes[0],
            &blocks[0].block_hash(),
            true,
        );
        assert_block_stored_not_staging(&mut chainstate, &consensus_hashes[0], &blocks[0]);

        // process and store blocks 1 and N, as well as microblocks in-between
        let len = blocks.len();
        for i in 1..len {
            // this is what happens at the end of append_block()
            // store block to staging and process it
            assert!(StacksChainState::load_staging_block_data(
                &chainstate.db(),
                &chainstate.blocks_path,
                &consensus_hashes[i],
                &blocks[i].block_hash()
            )
            .unwrap()
            .is_none());
            store_staging_block(
                &mut chainstate,
                &consensus_hashes[i],
                &blocks[i],
                &consensus_hashes[0],
                1,
                2,
            );
            assert_block_staging_not_processed(&mut chainstate, &consensus_hashes[i], &blocks[i]);

            set_block_processed(
                &mut chainstate,
                &consensus_hashes[i],
                &blocks[i].block_hash(),
                true,
            );

            // set different parts of this stream as confirmed
            set_microblocks_processed(
                &mut chainstate,
                &consensus_hashes[i],
                &blocks[i].block_hash(),
                &blocks[i].header.parent_microblock,
            );

            assert_block_stored_not_staging(&mut chainstate, &consensus_hashes[i], &blocks[i]);

            let mblocks_confirmed = StacksChainState::load_processed_microblock_stream_fork(
                &chainstate.db(),
                &consensus_hashes[0],
                &blocks[0].block_hash(),
                &blocks[i].header.parent_microblock,
            )
            .unwrap()
            .unwrap();
            assert_eq!(mblocks_confirmed.as_slice(), &mblocks[0..i]);
        }
    }

    #[test]
    fn stacks_db_staging_blocks_orphaned() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_staging_blocks_orphaned");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block_1 = make_empty_coinbase_block(&privk);
        let block_2 = make_empty_coinbase_block(&privk);
        let block_3 = make_empty_coinbase_block(&privk);
        let block_4 = make_empty_coinbase_block(&privk);

        let mut blocks = vec![block_1, block_2, block_3, block_4];

        let mut microblocks = vec![];

        for i in 0..blocks.len() {
            // make a sample microblock stream for block i
            let mut mblocks = make_sample_microblock_stream(&privk, &blocks[i].block_hash());
            mblocks.truncate(3);

            if i + 1 < blocks.len() {
                blocks[i + 1].header.parent_block = blocks[i].block_hash();
                blocks[i + 1].header.parent_microblock = mblocks[2].block_hash();
                blocks[i + 1].header.parent_microblock_sequence = mblocks[2].header.sequence;
            }

            microblocks.push(mblocks);
        }

        let consensus_hashes = vec![
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
            ConsensusHash([5u8; 20]),
        ];

        let parent_consensus_hashes = vec![
            ConsensusHash([1u8; 20]),
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
        ];

        // store all microblocks to staging
        for ((block, consensus_hash), mblocks) in
            blocks.iter().zip(&consensus_hashes).zip(&microblocks)
        {
            for mblock in mblocks {
                store_staging_microblock(
                    &mut chainstate,
                    consensus_hash,
                    &block.block_hash(),
                    mblock,
                );
                assert!(StacksChainState::load_staging_microblock(
                    &chainstate.db(),
                    consensus_hash,
                    &block.block_hash(),
                    &mblock.block_hash()
                )
                .unwrap()
                .is_some());
            }
        }

        // store blocks to staging
        for i in 0..blocks.len() {
            assert!(StacksChainState::load_staging_block_data(
                &chainstate.db(),
                &chainstate.blocks_path,
                &consensus_hashes[i],
                &blocks[i].block_hash()
            )
            .unwrap()
            .is_none());
            store_staging_block(
                &mut chainstate,
                &consensus_hashes[i],
                &blocks[i],
                &parent_consensus_hashes[i],
                1,
                2,
            );
            assert_block_staging_not_processed(&mut chainstate, &consensus_hashes[i], &blocks[i]);
        }

        // reject block 1
        set_block_processed(
            &mut chainstate,
            &consensus_hashes[0],
            &blocks[0].block_hash(),
            false,
        );

        // destroy all descendants
        for i in 0..blocks.len() {
            // confirm that block i is deleted, as are its microblocks
            assert_block_stored_rejected(&mut chainstate, &consensus_hashes[i], &blocks[i]);

            // block i's microblocks should all be marked as processed, orphaned, and deleted
            for mblock in microblocks[i].iter() {
                assert!(StacksChainState::load_staging_microblock(
                    &chainstate.db(),
                    &consensus_hashes[i],
                    &blocks[i].block_hash(),
                    &mblock.block_hash()
                )
                .unwrap()
                .is_none());

                assert!(StacksChainState::load_staging_microblock_bytes(
                    &chainstate.db(),
                    &mblock.block_hash()
                )
                .unwrap()
                .is_none());
            }

            if i + 1 < blocks.len() {
                // block i+1 should be marked as an orphan, but its data should still be there
                assert!(StacksChainState::load_staging_block(
                    &chainstate.db(),
                    &chainstate.blocks_path,
                    &consensus_hashes[i + 1],
                    &blocks[i + 1].block_hash()
                )
                .unwrap()
                .is_none());
                assert!(
                    StacksChainState::load_block_bytes(
                        &chainstate.blocks_path,
                        &consensus_hashes[i + 1],
                        &blocks[i + 1].block_hash()
                    )
                    .unwrap()
                    .unwrap()
                    .len()
                        > 0
                );

                for mblock in microblocks[i + 1].iter() {
                    let staging_mblock = StacksChainState::load_staging_microblock(
                        &chainstate.db(),
                        &consensus_hashes[i + 1],
                        &blocks[i + 1].block_hash(),
                        &mblock.block_hash(),
                    )
                    .unwrap()
                    .unwrap();
                    assert!(!staging_mblock.processed);
                    assert!(!staging_mblock.orphaned);
                    assert!(staging_mblock.block_data.len() > 0);
                }
            }

            // process next orphan block (should be block i+1)
            let res = process_next_orphaned_staging_block(&mut chainstate);

            if i < blocks.len() - 1 {
                // have more to do
                assert!(res);
            } else {
                // should be done
                assert!(!res);
            }
        }
    }

    #[test]
    fn stacks_db_drop_staging_microblocks() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_drop_staging_microblocks_1");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let mut mblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        mblocks.truncate(3);

        let consensus_hash = ConsensusHash([2u8; 20]);
        let parent_consensus_hash = ConsensusHash([1u8; 20]);

        // store microblocks to staging
        for mblock in mblocks.iter() {
            store_staging_microblock(
                &mut chainstate,
                &consensus_hash,
                &block.block_hash(),
                mblock,
            );
            assert!(StacksChainState::load_staging_microblock(
                &chainstate.db(),
                &consensus_hash,
                &block.block_hash(),
                &mblock.block_hash()
            )
            .unwrap()
            .is_some());
        }

        // store block to staging
        assert!(StacksChainState::load_staging_block_data(
            &chainstate.db(),
            &chainstate.blocks_path,
            &consensus_hash,
            &block.block_hash()
        )
        .unwrap()
        .is_none());
        store_staging_block(
            &mut chainstate,
            &consensus_hash,
            &block,
            &parent_consensus_hash,
            1,
            2,
        );
        assert_block_staging_not_processed(&mut chainstate, &consensus_hash, &block);

        // drop microblocks
        let len = mblocks.len();
        for i in 0..len {
            drop_staging_microblocks(
                &mut chainstate,
                &consensus_hash,
                &block.block_hash(),
                &mblocks[len - i - 1].block_hash(),
            );
            if i < len - 1 {
                assert_eq!(
                    StacksChainState::load_descendant_staging_microblock_stream(
                        &chainstate.db(),
                        &StacksBlockHeader::make_index_block_hash(
                            &consensus_hash,
                            &block.block_hash()
                        ),
                        0,
                        u16::max_value()
                    )
                    .unwrap()
                    .unwrap()
                    .as_slice(),
                    &mblocks[0..len - i - 1]
                );
            } else {
                // last time we do this, there will be no more stream
                assert!(StacksChainState::load_descendant_staging_microblock_stream(
                    &chainstate.db(),
                    &StacksBlockHeader::make_index_block_hash(&consensus_hash, &block.block_hash()),
                    0,
                    u16::max_value()
                )
                .unwrap()
                .is_none());
            }
        }
    }

    #[test]
    fn stacks_db_has_blocks_and_microblocks() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_has_blocks_and_microblocks");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let mut mblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        mblocks.truncate(3);

        let mut child_block = make_empty_coinbase_block(&privk);

        child_block.header.parent_block = block.block_hash();
        child_block.header.parent_microblock = mblocks.last().as_ref().unwrap().block_hash();
        child_block.header.parent_microblock_sequence =
            mblocks.last().as_ref().unwrap().header.sequence;

        let consensus_hash = ConsensusHash([2u8; 20]);
        let parent_consensus_hash = ConsensusHash([1u8; 20]);
        let child_consensus_hash = ConsensusHash([3u8; 20]);

        let index_block_header =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &block.block_hash());
        assert!(
            !StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_header)
                .unwrap()
        );
        assert!(!chainstate
            .has_microblocks_indexed(&index_block_header)
            .unwrap());

        let child_index_block_header = StacksBlockHeader::make_index_block_hash(
            &child_consensus_hash,
            &child_block.block_hash(),
        );
        assert!(!StacksChainState::has_block_indexed(
            &chainstate.blocks_path,
            &child_index_block_header
        )
        .unwrap());
        assert!(!chainstate
            .has_microblocks_indexed(&child_index_block_header)
            .unwrap());

        assert_eq!(
            StacksChainState::stream_microblock_get_info(&chainstate.db(), &index_block_header)
                .unwrap()
                .len(),
            0
        );

        // store microblocks to staging
        for (i, mblock) in mblocks.iter().enumerate() {
            assert!(StacksChainState::stream_microblock_get_rowid(
                &chainstate.db(),
                &index_block_header,
                &mblock.header.block_hash(),
            )
            .unwrap()
            .is_none());

            store_staging_microblock(
                &mut chainstate,
                &consensus_hash,
                &block.block_hash(),
                mblock,
            );
            assert!(StacksChainState::load_staging_microblock(
                &chainstate.db(),
                &consensus_hash,
                &block.block_hash(),
                &mblock.block_hash()
            )
            .unwrap()
            .is_some());

            assert!(chainstate
                .has_microblocks_indexed(&index_block_header)
                .unwrap());
            assert!(StacksChainState::stream_microblock_get_rowid(
                &chainstate.db(),
                &index_block_header,
                &mblock.header.block_hash(),
            )
            .unwrap()
            .is_some());

            assert!(!StacksChainState::has_block_indexed(
                &chainstate.blocks_path,
                &index_block_header
            )
            .unwrap());

            let mblock_info =
                StacksChainState::stream_microblock_get_info(&chainstate.db(), &index_block_header)
                    .unwrap();
            assert_eq!(mblock_info.len(), i + 1);

            let last_mblock_info = mblock_info.last().unwrap();
            assert_eq!(last_mblock_info.consensus_hash, consensus_hash);
            assert_eq!(last_mblock_info.anchored_block_hash, block.block_hash());
            assert_eq!(last_mblock_info.microblock_hash, mblock.block_hash());
            assert_eq!(last_mblock_info.sequence, mblock.header.sequence);
            assert!(!last_mblock_info.processed);
            assert!(!last_mblock_info.orphaned);
            assert_eq!(last_mblock_info.block_data.len(), 0);
        }

        // store block to staging
        store_staging_block(
            &mut chainstate,
            &consensus_hash,
            &block,
            &parent_consensus_hash,
            1,
            2,
        );
        store_staging_block(
            &mut chainstate,
            &child_consensus_hash,
            &child_block,
            &consensus_hash,
            1,
            2,
        );

        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_header)
                .unwrap()
        );
        assert!(StacksChainState::has_block_indexed(
            &chainstate.blocks_path,
            &child_index_block_header
        )
        .unwrap());

        // accept it
        set_block_processed(&mut chainstate, &consensus_hash, &block.block_hash(), true);
        assert!(
            StacksChainState::has_block_indexed(&chainstate.blocks_path, &index_block_header)
                .unwrap()
        );
        set_block_processed(
            &mut chainstate,
            &child_consensus_hash,
            &child_block.block_hash(),
            true,
        );
        assert!(StacksChainState::has_block_indexed(
            &chainstate.blocks_path,
            &child_index_block_header
        )
        .unwrap());

        for i in 0..mblocks.len() {
            assert!(StacksChainState::stream_microblock_get_rowid(
                &chainstate.db(),
                &index_block_header,
                &mblocks[i].block_hash(),
            )
            .unwrap()
            .is_some());

            // set different parts of this stream as confirmed
            set_microblocks_processed(
                &mut chainstate,
                &child_consensus_hash,
                &child_block.block_hash(),
                &mblocks[i].block_hash(),
            );
            assert!(chainstate
                .has_microblocks_indexed(&index_block_header)
                .unwrap());

            let mblock_info =
                StacksChainState::stream_microblock_get_info(&chainstate.db(), &index_block_header)
                    .unwrap();
            assert_eq!(mblock_info.len(), mblocks.len());

            let this_mblock_info = &mblock_info[i];
            test_debug!("Pass {} (seq {})", &i, &this_mblock_info.sequence);

            assert_eq!(this_mblock_info.consensus_hash, consensus_hash);
            assert_eq!(this_mblock_info.anchored_block_hash, block.block_hash());
            assert_eq!(this_mblock_info.microblock_hash, mblocks[i].block_hash());
            assert_eq!(this_mblock_info.sequence, mblocks[i].header.sequence);
            assert!(this_mblock_info.processed);
            assert!(!this_mblock_info.orphaned);
            assert_eq!(this_mblock_info.block_data.len(), 0);
        }
    }

    fn stream_one_staging_microblock_to_vec(
        blocks_conn: &DBConn,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<Vec<u8>, chainstate_error> {
        let mut bytes = vec![];
        StacksChainState::stream_one_microblock(blocks_conn, &mut bytes, stream, count).map(|nr| {
            assert_eq!(bytes.len(), nr as usize);
            bytes
        })
    }

    fn stream_chunk_to_vec(
        blocks_path: &String,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<Vec<u8>, chainstate_error> {
        let mut bytes = vec![];
        StacksChainState::stream_data_from_chunk_store(blocks_path, &mut bytes, stream, count).map(
            |nr| {
                assert_eq!(bytes.len(), nr as usize);
                bytes
            },
        )
    }

    fn stream_unconfirmed_microblocks_to_vec(
        chainstate: &mut StacksChainState,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<Vec<u8>, chainstate_error> {
        let mut bytes = vec![];
        stream.stream_to(chainstate, &mut bytes, count).map(|nr| {
            assert_eq!(bytes.len(), nr as usize);
            bytes
        })
    }

    fn stream_confirmed_microblocks_to_vec(
        chainstate: &mut StacksChainState,
        stream: &mut BlockStreamData,
        count: u64,
    ) -> Result<Vec<u8>, chainstate_error> {
        let mut bytes = vec![];
        stream.stream_to(chainstate, &mut bytes, count).map(|nr| {
            assert_eq!(bytes.len(), nr as usize);
            bytes
        })
    }

    fn decode_microblock_stream(mblock_bytes: &Vec<u8>) -> Vec<StacksMicroblock> {
        // decode stream
        let mut mblock_ptr = mblock_bytes.as_slice();
        let mut mblocks = vec![];
        loop {
            test_debug!("decoded {}", mblocks.len());
            {
                let mut debug_reader = LogReader::from_reader(&mut mblock_ptr);
                let next_mblock = StacksMicroblock::consensus_deserialize(&mut debug_reader)
                    .map_err(|e| {
                        eprintln!("Failed to decode microblock {}: {:?}", mblocks.len(), &e);
                        eprintln!("Bytes consumed:");
                        for buf in debug_reader.log().iter() {
                            eprintln!("  {}", to_hex(buf));
                        }
                        assert!(false);
                        unreachable!();
                    })
                    .unwrap();
                mblocks.push(next_mblock);
            }
            if mblock_ptr.len() == 0 {
                break;
            }
        }
        mblocks
    }

    #[test]
    fn stacks_db_stream_blocks() {
        let mut chainstate = instantiate_chainstate(false, 0x80000000, "stacks_db_stream_blocks");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_16k_block(&privk);

        let consensus_hash = ConsensusHash([2u8; 20]);
        let parent_consensus_hash = ConsensusHash([1u8; 20]);
        let index_block_header =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &block.block_hash());

        // can't stream a non-existant block
        let mut stream = BlockStreamData::new_block(index_block_header.clone());
        assert!(stream_chunk_to_vec(&chainstate.blocks_path, &mut stream, 123).is_err());

        // stream unmodified
        let stream_2 = BlockStreamData::new_block(index_block_header.clone());
        assert_eq!(stream, stream_2);

        // store block to staging
        store_staging_block(
            &mut chainstate,
            &consensus_hash,
            &block,
            &parent_consensus_hash,
            1,
            2,
        );

        // stream it back
        let mut all_block_bytes = vec![];
        loop {
            let mut next_bytes =
                stream_chunk_to_vec(&chainstate.blocks_path, &mut stream, 16).unwrap();
            if next_bytes.len() == 0 {
                break;
            }
            test_debug!(
                "Got {} more bytes from staging; add to {} total",
                next_bytes.len(),
                all_block_bytes.len()
            );
            all_block_bytes.append(&mut next_bytes);
        }

        // should decode back into the block
        let staging_block = StacksBlock::consensus_deserialize(&mut &all_block_bytes[..]).unwrap();
        assert_eq!(staging_block, block);

        // accept it
        set_block_processed(&mut chainstate, &consensus_hash, &block.block_hash(), true);

        // can still stream it
        let mut stream = BlockStreamData::new_block(index_block_header.clone());

        // stream from chunk store
        let mut all_block_bytes = vec![];
        loop {
            let mut next_bytes =
                stream_chunk_to_vec(&chainstate.blocks_path, &mut stream, 16).unwrap();
            if next_bytes.len() == 0 {
                break;
            }
            test_debug!(
                "Got {} more bytes from chunkstore; add to {} total",
                next_bytes.len(),
                all_block_bytes.len()
            );
            all_block_bytes.append(&mut next_bytes);
        }

        // should decode back into the block
        let staging_block = StacksBlock::consensus_deserialize(&mut &all_block_bytes[..]).unwrap();
        assert_eq!(staging_block, block);
    }

    #[test]
    fn stacks_db_stream_staging_microblocks() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_stream_staging_microblocks");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let mut mblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        mblocks.truncate(15);

        let consensus_hash = ConsensusHash([2u8; 20]);
        let parent_consensus_hash = ConsensusHash([1u8; 20]);
        let index_block_header =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &block.block_hash());

        // can't stream a non-existant microblock
        let mut stream = BlockStreamData::new_block(index_block_header.clone());
        assert!(StacksChainState::stream_one_microblock(
            &chainstate.db(),
            &mut vec![],
            &mut stream,
            123
        )
        .is_err());
        assert!(stream.rowid.is_none());

        // store microblocks to staging and stream them back
        for (i, mblock) in mblocks.iter().enumerate() {
            store_staging_microblock(
                &mut chainstate,
                &consensus_hash,
                &block.block_hash(),
                mblock,
            );

            // read back all the data we have so far, block-by-block
            let mut staging_mblocks = vec![];
            for j in 0..(i + 1) {
                let mut next_mblock_bytes = vec![];
                let mut stream = BlockStreamData::new_microblock_unconfirmed(
                    &chainstate,
                    index_block_header.clone(),
                    j as u16,
                )
                .unwrap();
                loop {
                    let mut next_bytes =
                        stream_one_staging_microblock_to_vec(&chainstate.db(), &mut stream, 4096)
                            .unwrap();
                    if next_bytes.len() == 0 {
                        break;
                    }
                    test_debug!(
                        "Got {} more bytes from staging; add to {} total",
                        next_bytes.len(),
                        next_mblock_bytes.len()
                    );
                    next_mblock_bytes.append(&mut next_bytes);
                }
                test_debug!("Got {} total bytes", next_mblock_bytes.len());

                // should deserialize to a microblock
                let staging_mblock =
                    StacksMicroblock::consensus_deserialize(&mut &next_mblock_bytes[..]).unwrap();
                staging_mblocks.push(staging_mblock);
            }

            assert_eq!(staging_mblocks.len(), mblocks[0..(i + 1)].len());
            for j in 0..(i + 1) {
                test_debug!("check {}", j);
                assert_eq!(staging_mblocks[j], mblocks[j])
            }

            // can also read partial stream in one shot, from any seq
            for k in 0..(i + 1) {
                test_debug!("start at seq {}", k);
                let mut staging_mblock_bytes = vec![];
                let mut stream = BlockStreamData::new_microblock_unconfirmed(
                    &chainstate,
                    index_block_header.clone(),
                    k as u16,
                )
                .unwrap();
                loop {
                    let mut next_bytes =
                        stream_unconfirmed_microblocks_to_vec(&mut chainstate, &mut stream, 4096)
                            .unwrap();
                    if next_bytes.len() == 0 {
                        break;
                    }
                    test_debug!(
                        "Got {} more bytes from staging; add to {} total",
                        next_bytes.len(),
                        staging_mblock_bytes.len()
                    );
                    staging_mblock_bytes.append(&mut next_bytes);
                }

                test_debug!("Got {} total bytes", staging_mblock_bytes.len());

                // decode stream
                let staging_mblocks = decode_microblock_stream(&staging_mblock_bytes);

                assert_eq!(staging_mblocks.len(), mblocks[k..(i + 1)].len());
                for j in 0..staging_mblocks.len() {
                    test_debug!("check {}", j);
                    assert_eq!(staging_mblocks[j], mblocks[k + j])
                }
            }
        }
    }

    #[test]
    fn stacks_db_stream_confirmed_microblocks() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_stream_confirmed_microblocks");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block = make_empty_coinbase_block(&privk);
        let mut mblocks = make_sample_microblock_stream(&privk, &block.block_hash());
        mblocks.truncate(5);

        let mut child_block = make_empty_coinbase_block(&privk);
        child_block.header.parent_block = block.block_hash();
        child_block.header.parent_microblock = mblocks.last().as_ref().unwrap().block_hash();
        child_block.header.parent_microblock_sequence =
            mblocks.last().as_ref().unwrap().header.sequence;

        let consensus_hash = ConsensusHash([2u8; 20]);
        let parent_consensus_hash = ConsensusHash([1u8; 20]);
        let child_consensus_hash = ConsensusHash([3u8; 20]);

        let index_block_header =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &block.block_hash());

        // store microblocks to staging
        for (i, mblock) in mblocks.iter().enumerate() {
            store_staging_microblock(
                &mut chainstate,
                &consensus_hash,
                &block.block_hash(),
                mblock,
            );
        }

        // store block to staging
        store_staging_block(
            &mut chainstate,
            &consensus_hash,
            &block,
            &parent_consensus_hash,
            1,
            2,
        );

        // store child block to staging
        store_staging_block(
            &mut chainstate,
            &child_consensus_hash,
            &child_block,
            &consensus_hash,
            1,
            2,
        );

        // accept it
        set_block_processed(&mut chainstate, &consensus_hash, &block.block_hash(), true);
        set_block_processed(
            &mut chainstate,
            &child_consensus_hash,
            &child_block.block_hash(),
            true,
        );

        for i in 0..mblocks.len() {
            // set different parts of this stream as confirmed
            set_microblocks_processed(
                &mut chainstate,
                &child_consensus_hash,
                &child_block.block_hash(),
                &mblocks[i].block_hash(),
            );

            // verify that we can stream everything
            let microblock_index_header =
                StacksBlockHeader::make_index_block_hash(&consensus_hash, &mblocks[i].block_hash());
            let mut stream = BlockStreamData::new_microblock_confirmed(
                &chainstate,
                microblock_index_header.clone(),
            )
            .unwrap();

            let mut confirmed_mblock_bytes = vec![];
            loop {
                let mut next_bytes =
                    stream_confirmed_microblocks_to_vec(&mut chainstate, &mut stream, 16).unwrap();
                if next_bytes.len() == 0 {
                    break;
                }
                test_debug!(
                    "Got {} more bytes from staging; add to {} total",
                    next_bytes.len(),
                    confirmed_mblock_bytes.len()
                );
                confirmed_mblock_bytes.append(&mut next_bytes);
            }

            // decode stream (should be length-prefixed)
            let mut confirmed_mblocks =
                Vec::<StacksMicroblock>::consensus_deserialize(&mut &confirmed_mblock_bytes[..])
                    .unwrap();

            confirmed_mblocks.reverse();

            assert_eq!(confirmed_mblocks.len(), mblocks[0..(i + 1)].len());
            for j in 0..(i + 1) {
                test_debug!("check {}", j);
                assert_eq!(confirmed_mblocks[j], mblocks[j])
            }
        }
    }

    #[test]
    fn stacks_db_get_blocks_inventory() {
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_get_blocks_inventory");

        let mut blocks: Vec<StacksBlock> = vec![];
        let mut privks = vec![];
        let mut microblocks = vec![];
        let mut consensus_hashes = vec![];
        let mut parent_consensus_hashes = vec![];

        for i in 0..32 {
            test_debug!("Making block {}", i);
            let privk = StacksPrivateKey::new();
            let block = make_empty_coinbase_block(&privk);

            blocks.push(block);
            privks.push(privk);

            let bhh = ConsensusHash([((i + 1) as u8); 20]);
            consensus_hashes.push(bhh);

            let parent_bhh = ConsensusHash([(i as u8); 20]);
            parent_consensus_hashes.push(parent_bhh);
        }

        for i in 0..blocks.len() {
            test_debug!("Making microblock stream {}", i);
            // make a sample microblock stream for block i
            let mut mblocks = make_sample_microblock_stream(&privks[i], &blocks[i].block_hash());
            mblocks.truncate(3);

            if i + 1 < blocks.len() {
                blocks[i + 1].header.parent_block = blocks[i].block_hash();
                blocks[i + 1].header.parent_microblock = mblocks[2].block_hash();
                blocks[i + 1].header.parent_microblock_sequence = mblocks[2].header.sequence;
            }

            microblocks.push(mblocks);
        }

        let block_hashes: Vec<BlockHeaderHash> =
            blocks.iter().map(|ref b| b.block_hash()).collect();
        let header_hashes_all: Vec<(ConsensusHash, Option<BlockHeaderHash>)> = consensus_hashes
            .iter()
            .zip(block_hashes.iter())
            .map(|(ref burn, ref block)| ((*burn).clone(), Some((*block).clone())))
            .collect();

        // nothing is stored, so our inventory should be empty
        let block_inv_all = chainstate.get_blocks_inventory(&header_hashes_all).unwrap();

        assert_eq!(block_inv_all.bitlen as usize, block_hashes.len());
        for i in 0..blocks.len() {
            assert!(!block_inv_all.has_ith_block(i as u16));
            assert!(!block_inv_all.has_ith_microblock_stream(i as u16));
        }

        // store all microblocks to staging
        for (i, ((block, consensus_hash), mblocks)) in blocks
            .iter()
            .zip(&consensus_hashes)
            .zip(&microblocks)
            .enumerate()
        {
            test_debug!("Store microblock stream {} to staging", i);
            for mblock in mblocks.iter() {
                test_debug!("Store microblock {}", &mblock.block_hash());
                store_staging_microblock(
                    &mut chainstate,
                    consensus_hash,
                    &block.block_hash(),
                    mblock,
                );
            }
        }

        // no anchored blocks are stored, so our block inventory should _still_ be empty
        let block_inv_all = chainstate.get_blocks_inventory(&header_hashes_all).unwrap();

        assert_eq!(block_inv_all.bitlen as usize, block_hashes.len());
        for i in 0..blocks.len() {
            assert!(!block_inv_all.has_ith_block(i as u16));
            assert!(!block_inv_all.has_ith_microblock_stream(i as u16)); // because anchord blocks are missing, microblocks won't be reported either
        }

        // store blocks to staging
        for i in 0..blocks.len() {
            test_debug!("Store block {} to staging", i);
            assert!(StacksChainState::load_staging_block_data(
                &chainstate.db(),
                &chainstate.blocks_path,
                &consensus_hashes[i],
                &blocks[i].block_hash()
            )
            .unwrap()
            .is_none());

            store_staging_block(
                &mut chainstate,
                &consensus_hashes[i],
                &blocks[i],
                &parent_consensus_hashes[i],
                1,
                2,
            );
            assert_block_staging_not_processed(&mut chainstate, &consensus_hashes[i], &blocks[i]);

            // some anchored blocks are stored (to staging)
            let block_inv_all = chainstate.get_blocks_inventory(&header_hashes_all).unwrap();
            assert_eq!(block_inv_all.bitlen as usize, block_hashes.len());
            for j in 0..(i + 1) {
                assert!(
                    block_inv_all.has_ith_block(j as u16),
                    format!(
                        "Missing block {} from bitvec {}",
                        j,
                        to_hex(&block_inv_all.block_bitvec)
                    )
                );

                // microblocks not stored yet, so they should be marked absent
                assert!(
                    !block_inv_all.has_ith_microblock_stream(j as u16),
                    format!(
                        "Have microblock {} from bitvec {}",
                        j,
                        to_hex(&block_inv_all.microblocks_bitvec)
                    )
                );
            }
            for j in i + 1..blocks.len() {
                assert!(!block_inv_all.has_ith_block(j as u16));
                assert!(!block_inv_all.has_ith_microblock_stream(j as u16));
            }
        }

        // confirm blocks and microblocks
        for i in 0..blocks.len() {
            test_debug!("Confirm block {} and its microblock stream", i);

            set_block_processed(
                &mut chainstate,
                &consensus_hashes[i],
                &block_hashes[i],
                true,
            );

            // have block, but stream is still empty
            let block_inv_all = chainstate.get_blocks_inventory(&header_hashes_all).unwrap();
            assert!(!block_inv_all.has_ith_microblock_stream((i + 1) as u16));

            if i < blocks.len() - 1 {
                for k in 0..3 {
                    set_microblocks_processed(
                        &mut chainstate,
                        &consensus_hashes[i + 1],
                        &block_hashes[i + 1],
                        &microblocks[i][k].block_hash(),
                    );

                    let block_inv_all =
                        chainstate.get_blocks_inventory(&header_hashes_all).unwrap();
                    test_debug!("Inv: {:?}", &block_inv_all);
                    for j in 0..blocks.len() {
                        // still have all the blocks
                        assert!(block_inv_all.has_ith_block(j as u16));

                        // all prior microblock streams remain present
                        test_debug!("Test microblock bit {} ({})", j, i);
                        if j == 0 {
                            assert!(!block_inv_all.has_ith_microblock_stream(j as u16));
                        } else if j <= i + 1 {
                            if k == 2 || j < i + 1 {
                                // all blocks prior to i+1 confirmed a microblock stream, except for
                                // the first.
                                // If k == 2, then block i+1 confirmed its stream fully.
                                assert!(block_inv_all.has_ith_microblock_stream(j as u16));
                            } else {
                                // only some microblocks processed in stream (k != 2 && j == i + 1)
                                assert!(!block_inv_all.has_ith_microblock_stream(j as u16));
                            }
                        } else {
                            assert!(!block_inv_all.has_ith_microblock_stream(j as u16));
                        }
                    }
                }
            }
        }

        // mark blocks as empty.  Should also orphan its descendant microblock stream
        for i in 0..blocks.len() {
            test_debug!("Mark block {} as invalid", i);
            set_block_orphaned(
                &mut chainstate,
                &consensus_hashes[i],
                &blocks[i].block_hash(),
            );

            // some anchored blocks are stored (to staging)
            let block_inv_all = chainstate.get_blocks_inventory(&header_hashes_all).unwrap();
            test_debug!("Blocks inv: {:?}", &block_inv_all);

            assert_eq!(block_inv_all.bitlen as usize, block_hashes.len());
            for j in 1..(i + 1) {
                test_debug!("Test bit {} ({})", j, i);
                assert!(
                    !block_inv_all.has_ith_block(j as u16),
                    format!(
                        "Have orphaned block {} from bitvec {}",
                        j,
                        to_hex(&block_inv_all.block_bitvec)
                    )
                );
                assert!(
                    !block_inv_all.has_ith_microblock_stream(j as u16),
                    format!(
                        "Still have microblock {} from bitvec {}",
                        j,
                        to_hex(&block_inv_all.microblocks_bitvec)
                    )
                );
            }
            for j in (i + 1)..blocks.len() {
                assert!(block_inv_all.has_ith_block(j as u16));
                assert!(block_inv_all.has_ith_microblock_stream(j as u16));
            }
        }
    }

    #[test]
    fn test_get_parent_block_header() {
        let peer_config = TestPeerConfig::new("test_get_parent_block_header", 21313, 21314);
        let mut peer = TestPeer::new(peer_config);

        let chainstate_path = peer.chainstate_path.clone();

        let num_blocks = 10;
        let first_stacks_block_height = {
            let sn =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();
            sn.block_height
        };

        let mut last_block_ch: Option<ConsensusHash> = None;
        let mut last_parent_opt: Option<StacksBlock> = None;
        for tenure_id in 0..num_blocks {
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            assert_eq!(
                tip.block_height,
                first_stacks_block_height + (tenure_id as u64)
            );

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    last_parent_opt = parent_opt.cloned();
                    let parent_tip = match parent_opt {
                        None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
                        Some(block) => {
                            let ic = sortdb.index_conn();
                            let snapshot =
                                SortitionDB::get_block_snapshot_for_winning_stacks_block(
                                    &ic,
                                    &tip.sortition_id,
                                    &block.block_hash(),
                                )
                                .unwrap()
                                .unwrap(); // succeeds because we don't fork
                            StacksChainState::get_anchored_block_header_info(
                                chainstate.db(),
                                &snapshot.consensus_hash,
                                &snapshot.winning_stacks_block_hash,
                            )
                            .unwrap()
                            .unwrap()
                        }
                    };

                    let mut mempool = MemPoolDB::open(false, 0x80000000, &chainstate_path).unwrap();
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let anchored_block = StacksBlockBuilder::build_anchored_block(
                        chainstate,
                        &sortdb.index_conn(),
                        &mut mempool,
                        &parent_tip,
                        tip.total_burn,
                        vrf_proof,
                        Hash160([tenure_id as u8; 20]),
                        &coinbase_tx,
                        ExecutionCost::max_value(),
                        None,
                    )
                    .unwrap();
                    (anchored_block.0, vec![])
                },
            );

            let (_, burn_header_hash, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());

            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let blocks_path = peer.chainstate().blocks_path.clone();

            if tenure_id == 0 {
                let parent_header_opt = StacksChainState::load_parent_block_header(
                    &peer.sortdb.as_ref().unwrap().index_conn(),
                    &blocks_path,
                    &consensus_hash,
                    &stacks_block.block_hash(),
                );
                assert!(parent_header_opt.is_err());
            } else {
                let parent_header_opt = StacksChainState::load_parent_block_header(
                    &peer.sortdb.as_ref().unwrap().index_conn(),
                    &blocks_path,
                    &consensus_hash,
                    &stacks_block.block_hash(),
                )
                .unwrap();
                let (parent_header, parent_ch) = parent_header_opt.unwrap();

                assert_eq!(last_parent_opt.as_ref().unwrap().header, parent_header);
                assert_eq!(parent_ch, last_block_ch.clone().unwrap());

                let chain_tip_index_hash = parent_header.index_block_hash(&parent_ch);
                let upper_bound_header =
                    StacksChainState::get_stacks_block_header_info_by_index_block_hash(
                        peer.chainstate().db(),
                        &chain_tip_index_hash,
                    )
                    .unwrap()
                    .unwrap();
                let ancestors = StacksChainState::get_ancestors_headers(
                    peer.chainstate().db(),
                    upper_bound_header,
                    0,
                )
                .unwrap();
                // Test that the segment returned by get_ancestors_headers (from genesis to chain tip) grows when the chain is growing
                assert_eq!(tenure_id, ancestors.len() - 1);
            }

            last_block_ch = Some(consensus_hash.clone());
        }
    }

    #[test]
    fn stacks_db_staging_microblocks_fork() {
        // multiple anchored blocks build off of a forked microblock stream
        let mut chainstate =
            instantiate_chainstate(false, 0x80000000, "stacks_db_staging_microblocks_fork");
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block_1 = make_empty_coinbase_block(&privk);

        let mut mblocks_1 = make_sample_microblock_stream(&privk, &block_1.block_hash());
        mblocks_1.truncate(3);

        let mut mblocks_2 = make_sample_microblock_stream(&privk, &block_1.block_hash());
        mblocks_2.truncate(3);

        let mut block_2 = make_empty_coinbase_block(&privk);
        let mut block_3 = make_empty_coinbase_block(&privk);

        block_2.header.parent_block = block_1.block_hash();
        block_3.header.parent_block = block_1.block_hash();

        block_2.header.parent_microblock = mblocks_1[2].block_hash();
        block_2.header.parent_microblock_sequence = mblocks_2[2].header.sequence;

        block_3.header.parent_microblock = mblocks_2[2].block_hash();
        block_3.header.parent_microblock_sequence = mblocks_2[2].header.sequence;

        let consensus_hashes = vec![
            ConsensusHash([2u8; 20]),
            ConsensusHash([3u8; 20]),
            ConsensusHash([4u8; 20]),
        ];

        let parent_consensus_hash = ConsensusHash([1u8; 20]);

        // store both microblock forks to staging
        for mblock in mblocks_1.iter() {
            store_staging_microblock(
                &mut chainstate,
                &consensus_hashes[0],
                &block_1.block_hash(),
                mblock,
            );
        }

        for mblock in mblocks_2.iter() {
            store_staging_microblock(
                &mut chainstate,
                &consensus_hashes[0],
                &block_1.block_hash(),
                mblock,
            );
        }

        store_staging_block(
            &mut chainstate,
            &consensus_hashes[0],
            &block_1,
            &parent_consensus_hash,
            1,
            2,
        );

        store_staging_block(
            &mut chainstate,
            &consensus_hashes[1],
            &block_2,
            &consensus_hashes[0],
            1,
            2,
        );

        store_staging_block(
            &mut chainstate,
            &consensus_hashes[2],
            &block_3,
            &consensus_hashes[0],
            1,
            2,
        );

        set_block_processed(
            &mut chainstate,
            &consensus_hashes[0],
            &block_1.block_hash(),
            true,
        );
        set_block_processed(
            &mut chainstate,
            &consensus_hashes[1],
            &block_2.block_hash(),
            true,
        );
        set_block_processed(
            &mut chainstate,
            &consensus_hashes[2],
            &block_3.block_hash(),
            true,
        );

        set_microblocks_processed(
            &mut chainstate,
            &consensus_hashes[1],
            &block_2.block_hash(),
            &mblocks_1[2].block_hash(),
        );

        set_microblocks_processed(
            &mut chainstate,
            &consensus_hashes[2],
            &block_3.block_hash(),
            &mblocks_2[2].block_hash(),
        );

        // both streams should be present
        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &consensus_hashes[0],
                &block_1.block_hash(),
                &mblocks_1.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            mblocks_1
        );

        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &consensus_hashes[0],
                &block_1.block_hash(),
                &mblocks_2.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            mblocks_2
        );

        // loading a descendant stream should fail to load any microblocks, since the fork is at
        // seq 0
        assert_eq!(
            StacksChainState::load_descendant_staging_microblock_stream(
                &chainstate.db(),
                &StacksBlockHeader::make_index_block_hash(
                    &consensus_hashes[0],
                    &block_1.block_hash()
                ),
                0,
                u16::MAX
            )
            .unwrap()
            .unwrap(),
            vec![]
        );
    }

    #[test]
    fn stacks_db_staging_microblocks_multiple_forks() {
        // multiple anchored blocks build off of a microblock stream that gets forked multiple
        // times
        let mut chainstate = instantiate_chainstate(
            false,
            0x80000000,
            "stacks_db_staging_microblocks_multiple_fork",
        );
        let privk = StacksPrivateKey::from_hex(
            "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
        )
        .unwrap();

        let block_1 = make_empty_coinbase_block(&privk);
        let mut blocks = vec![];

        let mut mblocks = make_sample_microblock_stream(&privk, &block_1.block_hash());
        mblocks.truncate(5);

        let mut mblocks_branches = vec![];
        let mut consensus_hashes = vec![ConsensusHash([2u8; 20])];

        for i in 1..4 {
            let mut mblocks_branch = make_sample_microblock_stream_fork(
                &privk,
                &mblocks[i].block_hash(),
                mblocks[i].header.sequence + 1,
            );
            mblocks_branch.truncate(3);

            let mut block = make_empty_coinbase_block(&privk);
            block.header.parent_block = block_1.block_hash();
            block.header.parent_microblock = mblocks_branch[2].block_hash();
            block.header.parent_microblock_sequence = mblocks_branch[2].header.sequence;

            mblocks_branches.push(mblocks_branch);
            blocks.push(block);
            consensus_hashes.push(ConsensusHash([(i + 2) as u8; 20]));
        }

        let parent_consensus_hash = ConsensusHash([1u8; 20]);

        // store everything
        store_staging_block(
            &mut chainstate,
            &consensus_hashes[0],
            &block_1,
            &parent_consensus_hash,
            1,
            2,
        );

        for (i, block) in blocks.iter().enumerate() {
            store_staging_block(
                &mut chainstate,
                &consensus_hashes[i + 1],
                &block,
                &consensus_hashes[0],
                1,
                2,
            );
        }

        // store both microblock forks to staging
        for mblock in mblocks.iter() {
            store_staging_microblock(
                &mut chainstate,
                &consensus_hashes[0],
                &block_1.block_hash(),
                mblock,
            );
        }

        for mblock_branch in mblocks_branches.iter() {
            for mblock in mblock_branch {
                store_staging_microblock(
                    &mut chainstate,
                    &consensus_hashes[0],
                    &block_1.block_hash(),
                    mblock,
                );
            }
        }

        set_block_processed(
            &mut chainstate,
            &consensus_hashes[0],
            &block_1.block_hash(),
            true,
        );
        for (i, block) in blocks.iter().enumerate() {
            set_block_processed(
                &mut chainstate,
                &consensus_hashes[i + 1],
                &block.block_hash(),
                true,
            );
        }

        for (i, mblock_branch) in mblocks_branches.iter().enumerate() {
            set_microblocks_processed(
                &mut chainstate,
                &consensus_hashes[i + 1],
                &blocks[i].block_hash(),
                &mblock_branch[2].block_hash(),
            );
        }

        // all streams should be present
        assert_eq!(
            StacksChainState::load_microblock_stream_fork(
                &chainstate.db(),
                &consensus_hashes[0],
                &block_1.block_hash(),
                &mblocks.last().as_ref().unwrap().block_hash(),
            )
            .unwrap()
            .unwrap(),
            mblocks
        );

        for (i, mblock_branch) in mblocks_branches.iter().enumerate() {
            let mut expected_mblocks = vec![];
            for j in 0..((mblock_branch[0].header.sequence) as usize) {
                expected_mblocks.push(mblocks[j].clone());
            }
            expected_mblocks.append(&mut mblock_branch.clone());

            assert_eq!(
                StacksChainState::load_microblock_stream_fork(
                    &chainstate.db(),
                    &consensus_hashes[0],
                    &block_1.block_hash(),
                    &mblock_branch.last().as_ref().unwrap().block_hash()
                )
                .unwrap()
                .unwrap(),
                expected_mblocks
            );
        }

        // loading a descendant stream should fail to load any microblocks, since the fork is at
        // seq 1
        assert_eq!(
            StacksChainState::load_descendant_staging_microblock_stream(
                &chainstate.db(),
                &StacksBlockHeader::make_index_block_hash(
                    &consensus_hashes[0],
                    &block_1.block_hash()
                ),
                0,
                u16::MAX
            )
            .unwrap()
            .unwrap(),
            mblocks[0..2].to_vec()
        );
    }

    // TODO(test): test multiple anchored blocks confirming the same microblock stream (in the same
    // place, and different places, with/without orphans)
    // TODO(test): process_next_staging_block
    // TODO(test): test resource limits -- shouldn't be able to load microblock streams that are too big
}
