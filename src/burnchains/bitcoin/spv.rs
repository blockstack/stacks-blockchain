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
use std::collections::VecDeque;
use std::fs;
use std::io::{Read, Seek, SeekFrom, Write};
use std::ops::Deref;

use deps::bitcoin::blockdata::block::{BlockHeader, LoneBlockHeader};
use deps::bitcoin::blockdata::constants::genesis_block;
use deps::bitcoin::network::constants::Network;
use deps::bitcoin::network::encodable::VarInt;
use deps::bitcoin::network::message as btc_message;
use deps::bitcoin::network::serialize::{deserialize, serialize, BitcoinHash};
use deps::bitcoin::util::hash::Sha256dHash;

use util::uint::Uint256;

use burnchains::bitcoin::indexer::BitcoinIndexer;
use burnchains::bitcoin::messages::BitcoinMessageHandler;
use burnchains::bitcoin::BitcoinNetworkType;
use burnchains::bitcoin::Error as btc_error;
use burnchains::bitcoin::PeerMessage;

use rusqlite::types::{FromSql, FromSqlError, FromSqlResult, ToSql, ToSqlOutput, ValueRef};
use rusqlite::Row;
use rusqlite::Transaction;
use rusqlite::{Connection, OpenFlags, NO_PARAMS};

use util::db::{
    query_row, query_rows, tx_begin_immediate, tx_busy_handler, u64_to_sql, DBConn, DBTx,
    Error as db_error, FromColumn, FromRow,
};
use util::get_epoch_time_secs;
use util::hash::{hex_bytes, to_hex};
use util::log;

const BLOCK_HEADER_SIZE: u64 = 81;

const BITCOIN_GENESIS_BLOCK_HASH_MAINNET: &'static str =
    "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f";
const BITCOIN_GENESIS_BLOCK_MERKLE_ROOT_MAINNET: &'static str =
    "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b";

const BITCOIN_GENESIS_BLOCK_HASH_TESTNET: &'static str =
    "000000000933ea01ad0ee984209779baaec3ced90fa3f408719526f8d77f4943";

const BITCOIN_GENESIS_BLOCK_HASH_REGTEST: &'static str =
    "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206";

pub const BLOCK_DIFFICULTY_CHUNK_SIZE: u64 = 2016;
const BLOCK_DIFFICULTY_INTERVAL: u32 = 14 * 24 * 60 * 60; // two weeks, in seconds

pub const SPV_DB_VERSION: &'static str = "1";

const SPV_INITIAL_SCHEMA: &[&'static str] = &[
    r#"
    CREATE TABLE headers(
        version INTEGER NOT NULL,
        prev_blockhash TEXT NOT NULL,
        merkle_root TEXT NOT NULL,
        time INTEGER NOT NULL,
        bits INTEGER NOT NULL,
        nonce INTEGER NOT NULL,
        height INTEGER PRIMARY KEY NOT NULL     -- not part of BlockHeader, but used by us internally
    );
    "#,
    "CREATE TABLE db_config(version TEXT NOT NULL);",
];

pub struct SpvClient {
    pub headers_path: String,
    pub start_block_height: u64,
    pub end_block_height: Option<u64>,
    pub cur_block_height: u64,
    pub network_id: BitcoinNetworkType,
    readwrite: bool,
    reverse_order: bool,
    headers_db: DBConn,
}

impl FromSql for Sha256dHash {
    fn column_result(value: ValueRef) -> FromSqlResult<Sha256dHash> {
        let hex_str = value.as_str()?;
        let hash = Sha256dHash::from_hex(hex_str).map_err(|_e| FromSqlError::InvalidType)?;
        Ok(hash)
    }
}

impl FromColumn<Sha256dHash> for Sha256dHash {
    fn from_column(row: &Row, column_name: &str) -> Result<Sha256dHash, db_error> {
        Ok(row.get_unwrap::<_, Self>(column_name))
    }
}

impl ToSql for Sha256dHash {
    fn to_sql(&self) -> rusqlite::Result<ToSqlOutput> {
        let hex_str = self.be_hex_string();
        Ok(hex_str.into())
    }
}

impl FromRow<BlockHeader> for BlockHeader {
    fn from_row<'a>(row: &'a Row) -> Result<BlockHeader, db_error> {
        let version: u32 = row.get_unwrap("version");
        let prev_blockhash: Sha256dHash = Sha256dHash::from_column(row, "prev_blockhash")?;
        let merkle_root: Sha256dHash = Sha256dHash::from_column(row, "merkle_root")?;
        let time: u32 = row.get_unwrap("time");
        let bits: u32 = row.get_unwrap("bits");
        let nonce: u32 = row.get_unwrap("nonce");

        Ok(BlockHeader {
            version,
            prev_blockhash,
            merkle_root,
            time,
            bits,
            nonce,
        })
    }
}

impl SpvClient {
    pub fn new(
        headers_path: &str,
        start_block: u64,
        end_block: Option<u64>,
        network_id: BitcoinNetworkType,
        readwrite: bool,
        reverse_order: bool,
    ) -> Result<SpvClient, btc_error> {
        let conn = SpvClient::db_open(headers_path, readwrite)?;
        let mut client = SpvClient {
            headers_path: headers_path.to_owned(),
            start_block_height: start_block,
            end_block_height: end_block,
            cur_block_height: start_block,
            network_id: network_id,
            readwrite: readwrite,
            reverse_order: reverse_order,
            headers_db: conn,
        };

        if readwrite {
            client.init_block_headers()?;
        }

        Ok(client)
    }

    pub fn conn(&self) -> &DBConn {
        &self.headers_db
    }

    pub fn tx_begin<'a>(&'a mut self) -> Result<DBTx<'a>, btc_error> {
        if !self.readwrite {
            return Err(db_error::ReadOnly.into());
        }

        let tx = tx_begin_immediate(&mut self.headers_db)?;

        Ok(tx)
    }

    fn db_instantiate(conn: &mut DBConn) -> Result<(), btc_error> {
        let tx = tx_begin_immediate(conn)?;

        for row_text in SPV_INITIAL_SCHEMA {
            tx.execute_batch(row_text).map_err(db_error::SqliteError)?;
        }

        tx.execute(
            "INSERT INTO db_config (version) VALUES (?1)",
            &[&SPV_DB_VERSION],
        )
        .map_err(db_error::SqliteError)?;

        tx.commit().map_err(db_error::SqliteError)?;
        Ok(())
    }

    fn db_open(headers_path: &str, readwrite: bool) -> Result<DBConn, btc_error> {
        let mut create_flag = false;
        let open_flags = if fs::metadata(headers_path).is_err() {
            // need to create
            if readwrite {
                create_flag = true;
                OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
            } else {
                return Err(btc_error::DBError(db_error::NoDBError));
            }
        } else {
            // can just open
            if readwrite {
                OpenFlags::SQLITE_OPEN_READ_WRITE
            } else {
                OpenFlags::SQLITE_OPEN_READ_ONLY
            }
        };

        let mut conn =
            Connection::open_with_flags(headers_path, open_flags).map_err(db_error::SqliteError)?;

        conn.busy_handler(Some(tx_busy_handler))
            .map_err(db_error::SqliteError)?;

        if create_flag {
            SpvClient::db_instantiate(&mut conn)?;
        }

        Ok(conn)
    }

    // are headers ready and available?
    pub fn is_initialized(&self) -> Result<(), btc_error> {
        fs::metadata(&self.headers_path)
            .map_err(btc_error::FilesystemError)
            .and_then(|_m| Ok(()))
    }

    /// Get the block range to scan
    pub fn set_scan_range(&mut self, start_block: u64, end_block: Option<u64>) -> () {
        self.start_block_height = start_block;
        self.end_block_height = end_block;
        self.cur_block_height = start_block;
    }

    /// go get all the headers.
    /// keep trying forever.
    pub fn run(&mut self, indexer: &mut BitcoinIndexer) -> Result<(), btc_error> {
        indexer.peer_communicate(self, true)
    }

    /// Validate a headers message we requested
    /// * must have at least one header
    /// * headers must be contiguous
    fn validate_header_integrity(
        start_height: u64,
        headers: &Vec<LoneBlockHeader>,
    ) -> Result<(), btc_error> {
        if headers.len() == 0 {
            return Ok(());
        }

        for i in 0..headers.len() {
            if headers[i].tx_count != VarInt(0) {
                warn!("Non-zero tx count on header offset {}", i);
                return Err(btc_error::InvalidReply);
            }
        }

        for i in 1..headers.len() {
            let prev_header = &headers[i - 1];
            let cur_header = &headers[i];

            if cur_header.header.prev_blockhash != prev_header.header.bitcoin_hash() {
                warn!(
                    "Bad SPV header for block {}: header prev_blockhash {} != prev_header hash {}",
                    start_height + (i as u64),
                    cur_header.header.prev_blockhash,
                    prev_header.header.bitcoin_hash()
                );
                return Err(btc_error::NoncontiguousHeader);
            }
        }

        return Ok(());
    }

    /// Verify that the given headers have the correct amount of work to be appended to our
    /// local header chain.  Checks the difficulty between [interval, interval+1]
    fn validate_header_work(
        &self,
        interval_start: u64,
        interval_end: u64,
    ) -> Result<(), btc_error> {
        debug!(
            "Validate PoW between blocks {}-{}",
            interval_start * BLOCK_DIFFICULTY_CHUNK_SIZE,
            interval_end * BLOCK_DIFFICULTY_CHUNK_SIZE
        );
        assert!(interval_start <= interval_end);
        if interval_start == 0 {
            return Ok(());
        }

        for i in interval_start..interval_end {
            let mut headers = VecDeque::new();
            for block_height in
                (i * BLOCK_DIFFICULTY_CHUNK_SIZE)..((i + 1) * BLOCK_DIFFICULTY_CHUNK_SIZE)
            {
                let header_i = match self.read_block_header(block_height)? {
                    None => return Ok(()),
                    Some(res) => res.header,
                };

                let (bits, difficulty) =
                    match self.get_target(block_height, &header_i, &headers, i)? {
                        Some(x) => x,
                        None => {
                            // out of headers
                            return Ok(());
                        }
                    };

                if header_i.bits != bits {
                    error!("bits mismatch at block {} of {} (offset {} interval {} of {}-{}): {:08x} != {:08x}",
                            block_height, self.headers_path, block_height % BLOCK_DIFFICULTY_CHUNK_SIZE, i, interval_start, interval_end, header_i.bits, bits);
                    return Err(btc_error::InvalidPoW);
                }
                let header_hash = header_i.bitcoin_hash().into_le();
                if difficulty <= header_hash {
                    error!(
                        "block {} hash {} has less work than difficulty {} in {}",
                        block_height,
                        header_i.bitcoin_hash(),
                        difficulty,
                        self.headers_path
                    );
                    return Err(btc_error::InvalidPoW);
                }

                headers.push_front(header_i);
            }
        }
        return Ok(());
    }

    /// Report how many block headers (+ 1) we have downloaded to the given path.
    pub fn get_headers_height(&self) -> Result<u64, btc_error> {
        let max = self.get_highest_header_height()?;
        Ok(max + 1)
    }

    /// Report the highest heigth of the last header we got
    pub fn get_highest_header_height(&self) -> Result<u64, btc_error> {
        match query_row::<u64, _>(
            &self.headers_db,
            "SELECT MAX(height) FROM headers",
            NO_PARAMS,
        )? {
            Some(max) => Ok(max),
            None => Ok(0),
        }
    }

    /// Read the block header at a particular height
    /// Returns None if the requested block height is beyond the end of the headers file
    pub fn read_block_header(
        &self,
        block_height: u64,
    ) -> Result<Option<LoneBlockHeader>, btc_error> {
        let header_opt: Option<BlockHeader> = query_row(
            &self.headers_db,
            "SELECT * FROM headers WHERE height = ?1",
            &[&u64_to_sql(block_height)?],
        )?;
        Ok(header_opt.map(|h| LoneBlockHeader {
            header: h,
            tx_count: VarInt(0),
        }))
    }

    /// Get a range of block headers from a file.
    /// If the range falls of the end of the headers file, then the returned array will be
    /// truncated to not include them (note that this method can return an empty list of the
    /// start_block is off the end of the file).
    /// If the range does _not_ include start_block, then this method returns an empty array (even
    /// if there are headers in the range).
    pub fn read_block_headers(
        &self,
        start_block: u64,
        end_block: u64,
    ) -> Result<Vec<LoneBlockHeader>, btc_error> {
        let mut headers = vec![];

        let sql_query = "SELECT * FROM headers WHERE height >= ?1 AND height < ?2 ORDER BY height";
        let sql_args: &[&dyn ToSql] = &[&u64_to_sql(start_block)?, &u64_to_sql(end_block)?];

        let mut stmt = self
            .headers_db
            .prepare(sql_query)
            .map_err(|e| btc_error::DBError(db_error::SqliteError(e)))?;

        let mut rows = stmt
            .query(sql_args)
            .map_err(|e| btc_error::DBError(db_error::SqliteError(e)))?;

        // gather, but make sure we get _all_ headers
        let mut next_height = start_block;
        while let Some(row) = rows
            .next()
            .map_err(|e| btc_error::DBError(db_error::SqliteError(e)))?
        {
            let height: u64 = u64::from_column(&row, "height")?;
            if height != next_height {
                break;
            }
            next_height += 1;

            let next_header = BlockHeader::from_row(&row)?;
            headers.push(LoneBlockHeader {
                header: next_header,
                tx_count: VarInt(0),
            });
        }

        Ok(headers)
    }

    /// Insert a block header
    fn insert_block_header<'a>(
        tx: &mut DBTx<'a>,
        header: BlockHeader,
        height: u64,
    ) -> Result<(), btc_error> {
        let sql = "INSERT OR REPLACE INTO headers 
        (version, prev_blockhash, merkle_root, time, bits, nonce, height)
        VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)";
        let args: &[&dyn ToSql] = &[
            &header.version,
            &header.prev_blockhash,
            &header.merkle_root,
            &header.time,
            &header.bits,
            &header.nonce,
            &u64_to_sql(height)?,
        ];
        tx.execute(sql, args)
            .map_err(|e| btc_error::DBError(db_error::SqliteError(e)))
            .and_then(|_x| Ok(()))
    }

    /// Initialize the block headers file with the genesis block hash
    fn init_block_headers(&mut self) -> Result<(), btc_error> {
        assert!(self.readwrite, "SPV header DB is open read-only");
        let (genesis_block, genesis_block_hash_str) = match self.network_id {
            BitcoinNetworkType::Mainnet => (
                genesis_block(Network::Bitcoin),
                BITCOIN_GENESIS_BLOCK_HASH_MAINNET,
            ),
            BitcoinNetworkType::Testnet => (
                genesis_block(Network::Testnet),
                BITCOIN_GENESIS_BLOCK_HASH_TESTNET,
            ),
            BitcoinNetworkType::Regtest => (
                genesis_block(Network::Regtest),
                BITCOIN_GENESIS_BLOCK_HASH_REGTEST,
            ),
        };

        // sanity check
        let genesis_block_hash =
            Sha256dHash::from_hex(genesis_block_hash_str).map_err(btc_error::HashError)?;
        if genesis_block.header.bitcoin_hash() != genesis_block_hash {
            error!(
                "Failed passing genesis block sanity check ({} != {})",
                genesis_block.header.bitcoin_hash(),
                genesis_block_hash
            );
            panic!();
        }

        let mut tx = self.tx_begin()?;
        SpvClient::insert_block_header(&mut tx, genesis_block.header, 0)?;
        tx.commit().map_err(db_error::SqliteError)?;

        debug!("Initialized block headers at {}", self.headers_path);
        return Ok(());
    }

    /// Handle a Headers message
    /// -- validate them
    /// -- store them
    /// Can error if there has been a reorg, or if the headers don't correspond to headers we asked
    /// for.
    fn handle_headers(
        &mut self,
        insert_height: u64,
        block_headers: Vec<LoneBlockHeader>,
    ) -> Result<(), btc_error> {
        assert!(self.readwrite, "SPV header DB is open read-only");

        let num_headers = block_headers.len();
        let first_header_hash = block_headers[0].header.bitcoin_hash();
        let last_header_hash = block_headers[block_headers.len() - 1].header.bitcoin_hash();

        if !self.reverse_order {
            // fetching headers in ascending order
            self.insert_block_headers_after(insert_height, block_headers)
                .map_err(|e| {
                    error!("Failed to insert block headers: {:?}", &e);
                    e
                })?;

            // check work
            let chain_tip = self.get_headers_height()?;
            self.validate_header_work(
                (chain_tip - 1) / BLOCK_DIFFICULTY_CHUNK_SIZE,
                chain_tip / BLOCK_DIFFICULTY_CHUNK_SIZE + 1,
            )
            .map_err(|e| {
                error!(
                    "Received headers with bad target, difficulty, or continuity: {:?}",
                    &e
                );
                e
            })?;
        } else {
            // fetching headers in descending order
            self.insert_block_headers_before(insert_height, block_headers)
                .map_err(|e| {
                    error!("Failed to insert block headers: {:?}", &e);
                    e
                })?;

            // check work
            let interval_start = if insert_height % BLOCK_DIFFICULTY_CHUNK_SIZE == 0 {
                insert_height / BLOCK_DIFFICULTY_CHUNK_SIZE
            } else {
                insert_height / BLOCK_DIFFICULTY_CHUNK_SIZE + 1
            };

            self.validate_header_work(interval_start, interval_start + 1)
                .map_err(|e| {
                    error!(
                        "Received headers with bad target, difficulty, or continuity: {:?}",
                        &e
                    );
                    e
                })?;
        }

        if num_headers > 0 {
            debug!(
                "Handled {} Headers: {}-{}",
                num_headers, first_header_hash, last_header_hash
            );
        } else {
            debug!("Handled empty header reply");
        }

        return Ok(());
    }

    /// Write a run of continuous headers to a particular location.
    /// Does _not_ check for continuity!
    pub fn write_block_headers(
        &mut self,
        height: u64,
        headers: Vec<LoneBlockHeader>,
    ) -> Result<(), btc_error> {
        assert!(self.readwrite, "SPV header DB is open read-only");
        debug!(
            "Write {} headers at {} at {}",
            headers.len(),
            &self.headers_path,
            height
        );
        let mut tx = self.tx_begin()?;
        for (i, header) in headers.into_iter().enumerate() {
            SpvClient::insert_block_header(&mut tx, header.header, height + (i as u64))?;
        }
        tx.commit()
            .map_err(|e| btc_error::DBError(db_error::SqliteError(e)))?;
        Ok(())
    }

    /// Insert block headers into the headers DB.
    /// Verify that the first header's parent exists and connects with this header chain, and verify that
    /// the headers are themselves contiguous.
    /// start_height refers to the _parent block_ of the given header stream.
    pub fn insert_block_headers_after(
        &mut self,
        start_height: u64,
        block_headers: Vec<LoneBlockHeader>,
    ) -> Result<(), btc_error> {
        assert!(self.readwrite, "SPV header DB is open read-only");

        if block_headers.len() == 0 {
            // no-op
            return Ok(());
        }

        debug!(
            "Insert {} headers to {} after block {}",
            block_headers.len(),
            &self.headers_path,
            start_height
        );

        SpvClient::validate_header_integrity(start_height, &block_headers).map_err(|e| {
            error!("Received invalid headers: {:?}", &e);
            e
        })?;

        let parent_header = match self.read_block_header(start_height)? {
            Some(header) => header,
            None => {
                warn!(
                    "No header for block {} -- cannot insert {} headers into {}",
                    start_height,
                    block_headers.len(),
                    self.headers_path
                );
                return Err(btc_error::NoncontiguousHeader);
            }
        };

        // contiguous?
        if block_headers[0].header.prev_blockhash != parent_header.header.bitcoin_hash() {
            warn!("Received discontiguous headers at height {}: we have parent {:?} ({}), but were given {:?} ({})",
                  start_height, &parent_header.header, parent_header.header.bitcoin_hash(), &block_headers[0].header, &block_headers[0].header.bitcoin_hash());
            return Err(btc_error::NoncontiguousHeader);
        }

        // store them
        self.write_block_headers(start_height + 1, block_headers)
    }

    /// Insert block headers into the headers DB.
    /// If the last header's child exists, verify that it connects with the given header chain.
    /// start_height refers to the _parent block_ of the given header stream
    pub fn insert_block_headers_before(
        &mut self,
        start_height: u64,
        block_headers: Vec<LoneBlockHeader>,
    ) -> Result<(), btc_error> {
        assert!(self.readwrite, "SPV header DB is open read-only");
        if block_headers.len() == 0 {
            // no-op
            return Ok(());
        }

        let end_height = start_height + (block_headers.len() as u64);

        debug!(
            "Insert {} headers to {} in range {}-{}",
            block_headers.len(),
            &self.headers_path,
            start_height,
            end_height
        );

        SpvClient::validate_header_integrity(start_height, &block_headers).map_err(|e| {
            error!("Received invalid headers: {:?}", &e);
            e
        })?;

        match self.read_block_header(end_height)? {
            Some(child_header) => {
                // contiguous?
                let last = block_headers.len() - 1;
                if block_headers[last].header.bitcoin_hash() != child_header.header.prev_blockhash {
                    warn!("Received discontiguous headers at height {}: we have child {:?} ({}), but were given {:?} ({})", 
                          end_height, &child_header, child_header.header.bitcoin_hash(), &block_headers[last], &block_headers[last].header.bitcoin_hash());
                    return Err(btc_error::NoncontiguousHeader);
                }
            }
            None => {
                // if we're inserting headers in reverse order, we're not guaranteed to have the
                // child.
                debug!(
                    "No header for child block {}, so will not validate continuity",
                    end_height
                );
            }
        }

        match self.read_block_header(start_height)? {
            Some(parent_header) => {
                // contiguous?
                if block_headers[0].header.prev_blockhash != parent_header.header.bitcoin_hash() {
                    warn!("Received discontiguous headers at height {}: we have parent {:?} ({}), but were given {:?} ({})",
                          start_height, &parent_header.header, parent_header.header.bitcoin_hash(), &block_headers[0].header, &block_headers[0].header.bitcoin_hash());
                    return Err(btc_error::NoncontiguousHeader);
                }
            }
            None => {
                debug!(
                    "No header for parent block {}, so will not validate continuity",
                    start_height - 1
                );
            }
        }

        // store them
        self.write_block_headers(start_height + 1, block_headers)
    }

    /// Drop headers after a block height (i.e. due to a reorg).
    /// The headers at new_max_height are kept.
    pub fn drop_headers(&mut self, new_max_height: u64) -> Result<(), btc_error> {
        assert!(self.readwrite, "SPV header DB is open read-only");

        debug!(
            "Drop all headers after block {} in {}",
            new_max_height, self.headers_path
        );

        let tx = self.tx_begin()?;
        tx.execute(
            "DELETE FROM headers WHERE height > ?1",
            &[&u64_to_sql(new_max_height)?],
        )
        .map_err(db_error::SqliteError)?;
        tx.commit()
            .map_err(|e| btc_error::DBError(db_error::SqliteError(e)))?;
        Ok(())
    }

    /// Determine the target difficult over a given difficulty adjustment interval
    /// the `interval` parameter is the difficulty interval -- a 2016-block interval.
    /// Returns (new bits, new target)
    pub fn get_target(
        &self,
        current_header_height: u64,
        current_header: &BlockHeader,
        headers_in_range: &VecDeque<BlockHeader>,
        interval: u64,
    ) -> Result<Option<(u32, Uint256)>, btc_error> {
        if interval == 0 {
            panic!(
                "Invalid argument: interval must be positive (got {})",
                interval
            );
        }

        // In Regtest mode there's no difficulty adjustment active.
        // it uses the highest possible difficulty -- represents nBits = 0x207fffff
        if self.network_id == BitcoinNetworkType::Regtest {
            return Ok(Some((
                0x207fffff,
                Uint256([
                    0x0000000000000000,
                    0x0000000000000000,
                    0x0000000000000000,
                    0x7fffffff00000000,
                ]),
            )));
        }

        let max_target = Uint256([
            0x0000000000000000,
            0x0000000000000000,
            0x0000000000000000,
            0x00000000ffff0000,
        ]);
        let max_target_bits = BlockHeader::compact_target_from_u256(&max_target);

        let parent_header = if headers_in_range.len() > 0 {
            headers_in_range[0]
        } else {
            match self.read_block_header(current_header_height - 1)? {
                Some(res) => res.header,
                None => return Ok(None),
            }
        };

        if current_header_height % BLOCK_DIFFICULTY_CHUNK_SIZE != 0
            && self.network_id == BitcoinNetworkType::Testnet
        {
            // In Testnet mode, if the new block's timestamp is more than 2* 10 minutes
            // then allow mining of a min-difficulty block.
            if current_header.time > parent_header.time + 10 * 60 * 2 {
                return Ok(Some((max_target_bits, max_target)));
            }

            // Otherwise return the last non-special-min-difficulty-rules-block
            for ancestor in headers_in_range {
                if ancestor.bits != max_target_bits {
                    let target = ancestor.target();
                    return Ok(Some((ancestor.bits, target)));
                }
            }
        }

        let first_header =
            match self.read_block_header((interval - 1) * BLOCK_DIFFICULTY_CHUNK_SIZE)? {
                Some(res) => res.header,
                None => return Ok(None),
            };

        let last_header =
            match self.read_block_header(interval * BLOCK_DIFFICULTY_CHUNK_SIZE - 1)? {
                Some(res) => res.header,
                None => return Ok(None),
            };

        // find actual timespan as being clamped between +/- 4x of the target timespan
        let mut actual_timespan = (last_header.time - first_header.time) as u64;
        let target_timespan = BLOCK_DIFFICULTY_INTERVAL as u64;
        if actual_timespan < (target_timespan / 4) {
            actual_timespan = target_timespan / 4;
        }
        if actual_timespan > (target_timespan * 4) {
            actual_timespan = target_timespan * 4;
        }

        let last_target = last_header.target();
        let new_target =
            last_target * Uint256::from_u64(actual_timespan) / Uint256::from_u64(target_timespan);
        let target = cmp::min(new_target, max_target);

        let bits = BlockHeader::compact_target_from_u256(&target);

        Ok(Some((bits, target)))
    }

    /// Ask for the next batch of headers (note that this will return the maximal size of headers)
    pub fn send_next_getheaders(
        &mut self,
        indexer: &mut BitcoinIndexer,
        block_height: u64,
    ) -> Result<(), btc_error> {
        // ask for the next batch
        let block_header = match self.read_block_header(block_height) {
            Ok(Some(header)) => header,
            Ok(None) => {
                debug!(
                    "No header found for block {} in {}",
                    block_height, &self.headers_path
                );
                return Err(btc_error::MissingHeader);
            }
            Err(e) => {
                warn!(
                    "Failed to read block header at height {} in {}: {:?}",
                    block_height, &self.headers_path, &e
                );
                return Err(e);
            }
        };
        indexer.send_getheaders(block_header.header.bitcoin_hash())
    }
}

impl BitcoinMessageHandler for SpvClient {
    /// Trait message handler
    /// initiate the conversation with the bitcoin peer
    fn begin_session(&mut self, indexer: &mut BitcoinIndexer) -> Result<bool, btc_error> {
        let start_height = self.cur_block_height;
        self.end_block_height = Some(indexer.runtime.block_height);

        if indexer.runtime.block_height <= start_height {
            debug!("Have all headers up to {}", start_height);
            return Ok(false);
        }

        debug!(
            "Get headers {}-{} to {}",
            self.cur_block_height,
            self.end_block_height.unwrap(),
            self.headers_path
        );

        indexer.runtime.last_getheaders_send_time = get_epoch_time_secs();
        self.send_next_getheaders(indexer, start_height)
            .and_then(|_r| Ok(true))
    }

    /// Trait message handler
    /// Take headers, validate them, and ask for more
    fn handle_message(
        &mut self,
        indexer: &mut BitcoinIndexer,
        msg: PeerMessage,
    ) -> Result<bool, btc_error> {
        assert!(self.end_block_height.is_some());

        let end_block_height = self.end_block_height.unwrap();

        match msg {
            btc_message::NetworkMessage::Headers(mut block_headers) => {
                if self.cur_block_height >= end_block_height {
                    // done
                    return Ok(false);
                }

                // only handle headers we asked for
                if end_block_height - self.cur_block_height < block_headers.len() as u64 {
                    debug!(
                        "Truncate received headers from block range {}-{} to range {}-{}",
                        self.cur_block_height,
                        end_block_height,
                        self.cur_block_height,
                        self.cur_block_height + (block_headers.len() as u64) - end_block_height
                    );
                    block_headers.truncate((end_block_height - self.cur_block_height) as usize);
                }

                let insert_height = self.cur_block_height;
                let num_headers = block_headers.len();

                self.handle_headers(insert_height, block_headers)?;
                self.cur_block_height += num_headers as u64;

                // ask for the next batch
                let block_height = self.get_highest_header_height()?;
                assert!(block_height > 0, "BUG: uninitialized SPV headers DB");

                // clear timeout
                indexer.runtime.last_getheaders_send_time = 0;

                // if syncing requires to request more than one batch of 2000 headers,
                // we'll provide some progress in the logs
                let total = end_block_height - self.start_block_height;
                let batch_size = 2000;
                if total > batch_size {
                    let progress =
                        (block_height - self.start_block_height) as f32 / total as f32 * 100.;
                    info!(
                        "Syncing Bitcoin headers: {:.1}% ({} out of {})",
                        progress, block_height, total
                    );
                } else {
                    debug!(
                        "Request headers for blocks {} - {} in range {} - {}",
                        block_height,
                        block_height + batch_size,
                        self.start_block_height,
                        end_block_height
                    );
                }
                self.send_next_getheaders(indexer, block_height)
                    .and_then(|_| Ok(true))
            }
            x => Err(btc_error::UnhandledMessage(x)),
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use burnchains::bitcoin::Error as btc_error;
    use burnchains::bitcoin::*;

    use std::fs::*;

    use deps::bitcoin::blockdata::block::{BlockHeader, LoneBlockHeader};
    use deps::bitcoin::network::serialize::{deserialize, serialize, BitcoinHash};
    use deps::bitcoin::util::hash::Sha256dHash;

    use util::log;

    use std::env;

    fn get_genesis_regtest_header() -> LoneBlockHeader {
        let genesis_regtest_header = LoneBlockHeader {
            header: BlockHeader {
                bits: 545259519,
                merkle_root: Sha256dHash::from_hex(
                    "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b",
                )
                .unwrap(),
                nonce: 2,
                prev_blockhash: Sha256dHash::from_hex(
                    "0000000000000000000000000000000000000000000000000000000000000000",
                )
                .unwrap(),
                time: 1296688602,
                version: 1,
            },
            tx_count: VarInt(0),
        };
        genesis_regtest_header
    }

    #[test]
    fn test_spv_mainnet_genesis_header() {
        let genesis_prev_blockhash = Sha256dHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let genesis_merkle_root =
            Sha256dHash::from_hex(BITCOIN_GENESIS_BLOCK_MERKLE_ROOT_MAINNET).unwrap();
        let genesis_block_hash = Sha256dHash::from_hex(BITCOIN_GENESIS_BLOCK_HASH_MAINNET).unwrap();

        let genesis_header = LoneBlockHeader {
            header: BlockHeader {
                version: 1,
                prev_blockhash: genesis_prev_blockhash,
                merkle_root: genesis_merkle_root,
                time: 1231006505,
                bits: 0x1d00ffff,
                nonce: 2083236893,
            },
            tx_count: VarInt(0),
        };

        test_debug!("\n");
        test_debug!("genesis prev blockhash = {}", genesis_prev_blockhash);
        test_debug!("genesis merkle root = {}", genesis_merkle_root);
        test_debug!("genesis block hash = {}", genesis_block_hash);

        assert_eq!(genesis_header.header.bitcoin_hash(), genesis_block_hash);
    }

    #[test]
    fn test_spv_load_store_header() {
        if fs::metadata("/tmp/test-spv-load_store_header.dat").is_ok() {
            fs::remove_file("/tmp/test-spv-load_store_header.dat").unwrap();
        }

        let genesis_regtest_header = get_genesis_regtest_header();

        let first_regtest_header = LoneBlockHeader {
            header: BlockHeader {
                bits: 545259519,
                merkle_root: Sha256dHash::from_hex(
                    "20bee96458517fc5082a9720ce6207b5742f2b18e4e0a7e7373342725d80f88c",
                )
                .unwrap(),
                nonce: 2,
                prev_blockhash: Sha256dHash::from_hex(
                    "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
                )
                .unwrap(),
                time: 1587626881,
                version: 0x20000000,
            },
            tx_count: VarInt(0),
        };

        let mut spv_client = SpvClient::new(
            "/tmp/test-spv-load_store_header.dat",
            0,
            None,
            BitcoinNetworkType::Regtest,
            true,
            false,
        )
        .unwrap();
        assert_eq!(spv_client.get_headers_height().unwrap(), 1);
        assert_eq!(
            spv_client.read_block_header(0).unwrap().unwrap(),
            genesis_regtest_header
        );

        {
            let mut tx = spv_client.tx_begin().unwrap();
            SpvClient::insert_block_header(&mut tx, first_regtest_header.header.clone(), 1)
                .unwrap();
            tx.commit().unwrap();
        }

        assert_eq!(spv_client.get_headers_height().unwrap(), 2);
        assert_eq!(
            spv_client.read_block_header(0).unwrap().unwrap(),
            genesis_regtest_header
        );
        assert_eq!(
            spv_client.read_block_headers(0, 1).unwrap(),
            vec![genesis_regtest_header.clone()]
        );
        assert_eq!(
            spv_client.read_block_header(1).unwrap().unwrap(),
            first_regtest_header
        );
        assert_eq!(
            spv_client.read_block_headers(1, 2).unwrap(),
            vec![first_regtest_header.clone()]
        );
        assert_eq!(
            spv_client.read_block_headers(0, 10).unwrap(),
            vec![genesis_regtest_header, first_regtest_header]
        );
    }

    #[test]
    fn test_spv_store_headers_after() {
        if fs::metadata("/tmp/test-spv-store_headers_after.dat").is_ok() {
            fs::remove_file("/tmp/test-spv-store_headers_after.dat").unwrap();
        }
        let genesis_regtest_header = get_genesis_regtest_header();
        let headers = vec![
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "20bee96458517fc5082a9720ce6207b5742f2b18e4e0a7e7373342725d80f88c",
                    )
                    .unwrap(),
                    nonce: 2,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
                    )
                    .unwrap(),
                    time: 1587626881,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "39d1a6f1ee7a5903797f92ec89e4c58549013f38114186fc2eb6e5218cb2d0ac",
                    )
                    .unwrap(),
                    nonce: 1,
                    prev_blockhash: Sha256dHash::from_hex(
                        "606d31daaaa5919f3720d8440dd99d31f2a4e4189c65879f19ae43268425e74b",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "a7e04ed25f589938eb5627abb7b5913dd77b8955bcdf72d7f111d0a71e346e47",
                    )
                    .unwrap(),
                    nonce: 4,
                    prev_blockhash: Sha256dHash::from_hex(
                        "2fa2f451ac27f0e5cd3760ba6cdf34ef46adb76a44d96bc0f3bf3e713dd955f0",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
        ];

        let mut spv_client = SpvClient::new(
            "/tmp/test-spv-store_headers_after.dat",
            0,
            None,
            BitcoinNetworkType::Regtest,
            true,
            false,
        )
        .unwrap();
        spv_client
            .insert_block_headers_after(0, headers.clone())
            .unwrap();

        assert_eq!(spv_client.read_block_headers(1, 10).unwrap(), headers);

        // should fail
        if let Err(btc_error::NoncontiguousHeader) =
            spv_client.insert_block_headers_after(1, headers.clone())
        {
        } else {
            assert!(false);
        }

        // should fail
        if let Err(btc_error::NoncontiguousHeader) =
            spv_client.insert_block_headers_after(9, headers.clone())
        {
        } else {
            assert!(false);
        }

        spv_client.drop_headers(1).unwrap();
        assert_eq!(
            spv_client.read_block_headers(0, 10).unwrap(),
            vec![genesis_regtest_header, headers[0].clone()]
        );
    }

    #[test]
    fn test_spv_store_headers_before() {
        if fs::metadata("/tmp/test-spv-store_headers_before.dat").is_ok() {
            fs::remove_file("/tmp/test-spv-store_headers_before.dat").unwrap();
        }
        let genesis_regtest_header = get_genesis_regtest_header();
        let headers = vec![
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "20bee96458517fc5082a9720ce6207b5742f2b18e4e0a7e7373342725d80f88c",
                    )
                    .unwrap(),
                    nonce: 2,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
                    )
                    .unwrap(),
                    time: 1587626881,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "39d1a6f1ee7a5903797f92ec89e4c58549013f38114186fc2eb6e5218cb2d0ac",
                    )
                    .unwrap(),
                    nonce: 1,
                    prev_blockhash: Sha256dHash::from_hex(
                        "606d31daaaa5919f3720d8440dd99d31f2a4e4189c65879f19ae43268425e74b",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "a7e04ed25f589938eb5627abb7b5913dd77b8955bcdf72d7f111d0a71e346e47",
                    )
                    .unwrap(),
                    nonce: 4,
                    prev_blockhash: Sha256dHash::from_hex(
                        "2fa2f451ac27f0e5cd3760ba6cdf34ef46adb76a44d96bc0f3bf3e713dd955f0",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
        ];

        let mut spv_client = SpvClient::new(
            "/tmp/test-spv-store_headers_before.dat",
            0,
            None,
            BitcoinNetworkType::Regtest,
            true,
            true,
        )
        .unwrap();
        spv_client
            .insert_block_headers_before(1, headers[1..].to_vec())
            .unwrap();

        assert_eq!(
            spv_client.read_block_headers(2, 10).unwrap(),
            headers[1..].to_vec()
        );
        assert_eq!(
            spv_client.read_block_headers(0, 10).unwrap(),
            vec![genesis_regtest_header.clone()]
        ); // gap
        assert_eq!(spv_client.read_block_headers(1, 10).unwrap(), vec![]); // gap

        spv_client
            .insert_block_headers_before(0, headers[0..1].to_vec())
            .unwrap();
        assert_eq!(spv_client.read_block_headers(1, 10).unwrap(), headers);

        let mut all_headers = vec![genesis_regtest_header.clone()];
        all_headers.append(&mut headers.clone());

        assert_eq!(spv_client.read_block_headers(0, 10).unwrap(), all_headers);

        // should fail
        if let Err(btc_error::NoncontiguousHeader) =
            spv_client.insert_block_headers_before(2, headers.clone())
        {
        } else {
            assert!(false);
        }

        // should fail
        if let Err(btc_error::NoncontiguousHeader) =
            spv_client.insert_block_headers_before(1, headers.clone())
        {
        } else {
            assert!(false);
        }

        // should succeed
        spv_client
            .insert_block_headers_before(9, headers.clone())
            .unwrap();
    }

    #[test]
    fn test_spv_check_pow() {
        if !env::var("BLOCKSTACK_SPV_HEADERS_DB").is_ok() {
            eprintln!("Skipping test_spv_check_pow -- no BLOCKSTACK_SPV_HEADERS_DB envar set");
            return;
        }
        let db_path = env::var("BLOCKSTACK_SPV_HEADERS_DB").unwrap();
        let spv_client =
            SpvClient::new(&db_path, 0, None, BitcoinNetworkType::Mainnet, false, false).unwrap();

        for i in 99..100 {
            spv_client.validate_header_work(i, i + 1).unwrap();
        }
    }
}
