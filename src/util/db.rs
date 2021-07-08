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

use chainstate::stacks::index::storage::TrieStorageConnection;
use std::convert::TryInto;
use std::error;
use std::fmt;
use std::fs;
use std::io;
use std::io::Error as IOError;
use std::ops::Deref;
use std::ops::DerefMut;
use std::path::PathBuf;

use util::hash::to_hex;
use util::sleep_ms;

use types::chainstate::BlockHeaderHash;
use vm::types::QualifiedContractIdentifier;

use rusqlite::types::{
    FromSql, FromSqlError, FromSqlResult, ToSql, ToSqlOutput, Value as RusqliteValue,
    ValueRef as RusqliteValueRef,
};
use rusqlite::Connection;
use rusqlite::Error as sqlite_error;
use rusqlite::Row;
use rusqlite::Transaction;
use rusqlite::TransactionBehavior;
use rusqlite::NO_PARAMS;

use crate::types::chainstate::MARFValue;
use crate::types::proof::TrieHash;
use chainstate::stacks::index::marf::MarfConnection;
use chainstate::stacks::index::marf::MarfTransaction;
use chainstate::stacks::index::marf::MARF;
use chainstate::stacks::index::storage::TrieStorageTransaction;
use chainstate::stacks::index::Error as MARFError;
use chainstate::stacks::index::MarfTrieId;

use rand::thread_rng;
use rand::Rng;
use rand::RngCore;

use serde_json::Error as serde_error;

pub type DBConn = rusqlite::Connection;
pub type DBTx<'a> = rusqlite::Transaction<'a>;

#[derive(Debug)]
pub enum Error {
    /// Not implemented
    NotImplemented,
    /// Database doesn't exist
    NoDBError,
    /// Read-only and tried to write
    ReadOnly,
    /// Type error -- can't represent the given data in the database
    TypeError,
    /// Database is corrupt -- we got data that shouldn't be there, or didn't get data when we
    /// should have
    Corruption,
    /// Serialization error -- can't serialize data
    SerializationError(serde_error),
    /// Parse error -- failed to load data we stored directly
    ParseError,
    /// Operation would overflow
    Overflow,
    /// Data not found
    NotFoundError,
    /// Data already exists
    ExistsError,
    /// Data corresponds to a non-canonical PoX sortition
    InvalidPoxSortition,
    /// Sqlite3 error
    SqliteError(sqlite_error),
    /// I/O error
    IOError(IOError),
    /// MARF index error
    IndexError(MARFError),
    /// Other error
    Other(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::NotImplemented => write!(f, "Not implemented"),
            Error::NoDBError => write!(f, "Database does not exist"),
            Error::ReadOnly => write!(f, "Database is opened read-only"),
            Error::TypeError => write!(f, "Invalid or unrepresentable database type"),
            Error::Corruption => write!(f, "Database is corrupt"),
            Error::SerializationError(ref e) => fmt::Display::fmt(e, f),
            Error::ParseError => write!(f, "Parse error"),
            Error::Overflow => write!(f, "Numeric overflow"),
            Error::NotFoundError => write!(f, "Not found"),
            Error::ExistsError => write!(f, "Already exists"),
            Error::InvalidPoxSortition => write!(f, "Invalid PoX sortition"),
            Error::IOError(ref e) => fmt::Display::fmt(e, f),
            Error::SqliteError(ref e) => fmt::Display::fmt(e, f),
            Error::IndexError(ref e) => fmt::Display::fmt(e, f),
            Error::Other(ref s) => fmt::Display::fmt(s, f),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Error::NotImplemented => None,
            Error::NoDBError => None,
            Error::ReadOnly => None,
            Error::TypeError => None,
            Error::Corruption => None,
            Error::SerializationError(ref e) => Some(e),
            Error::ParseError => None,
            Error::Overflow => None,
            Error::NotFoundError => None,
            Error::ExistsError => None,
            Error::InvalidPoxSortition => None,
            Error::SqliteError(ref e) => Some(e),
            Error::IOError(ref e) => Some(e),
            Error::IndexError(ref e) => Some(e),
            Error::Other(ref _s) => None,
        }
    }
}

impl From<sqlite_error> for Error {
    fn from(e: sqlite_error) -> Error {
        Error::SqliteError(e)
    }
}

impl From<MARFError> for Error {
    fn from(e: MARFError) -> Error {
        Error::IndexError(e)
    }
}

pub trait FromRow<T> {
    fn from_row<'a>(row: &'a Row) -> Result<T, Error>;
}

pub trait FromColumn<T> {
    fn from_column<'a>(row: &'a Row, column_name: &str) -> Result<T, Error>;
}

impl FromRow<u64> for u64 {
    fn from_row<'a>(row: &'a Row) -> Result<u64, Error> {
        let x: i64 = row.get_unwrap(0);
        if x < 0 {
            return Err(Error::ParseError);
        }
        Ok(x as u64)
    }
}

impl FromColumn<u64> for u64 {
    fn from_column<'a>(row: &'a Row, column_name: &str) -> Result<u64, Error> {
        let x: i64 = row.get_unwrap(column_name);
        if x < 0 {
            return Err(Error::ParseError);
        }
        Ok(x as u64)
    }
}

impl FromRow<i64> for i64 {
    fn from_row<'a>(row: &'a Row) -> Result<i64, Error> {
        let x: i64 = row.get_unwrap(0);
        Ok(x)
    }
}

impl FromColumn<i64> for i64 {
    fn from_column<'a>(row: &'a Row, column_name: &str) -> Result<i64, Error> {
        let x: i64 = row.get_unwrap(column_name);
        Ok(x)
    }
}

impl FromColumn<QualifiedContractIdentifier> for QualifiedContractIdentifier {
    fn from_column<'a>(
        row: &'a Row,
        column_name: &str,
    ) -> Result<QualifiedContractIdentifier, Error> {
        let value: String = row.get_unwrap(column_name);
        QualifiedContractIdentifier::parse(&value).map_err(|_| Error::ParseError)
    }
}

impl FromRow<bool> for bool {
    fn from_row<'a>(row: &'a Row) -> Result<bool, Error> {
        let x: bool = row.get_unwrap(0);
        Ok(x)
    }
}

pub fn u64_to_sql(x: u64) -> Result<i64, Error> {
    if x > (i64::max_value() as u64) {
        return Err(Error::ParseError);
    }
    Ok(x as i64)
}

pub fn opt_u64_to_sql(x: Option<u64>) -> Result<Option<i64>, Error> {
    match x {
        Some(x) => match u64_to_sql(x) {
            Ok(x) => Ok(Some(x)),
            Err(e) => Err(e),
        },
        None => Ok(None),
    }
}

macro_rules! impl_byte_array_from_column {
    ($thing:ident) => {
        impl rusqlite::types::FromSql for $thing {
            fn column_result(
                value: rusqlite::types::ValueRef,
            ) -> rusqlite::types::FromSqlResult<Self> {
                let hex_str = value.as_str()?;
                let byte_str = ::util::hash::hex_bytes(hex_str)
                    .map_err(|_e| rusqlite::types::FromSqlError::InvalidType)?;
                let inst = $thing::from_bytes(&byte_str)
                    .ok_or(rusqlite::types::FromSqlError::InvalidType)?;
                Ok(inst)
            }
        }

        impl ::util::db::FromColumn<$thing> for $thing {
            fn from_column(
                row: &rusqlite::Row,
                column_name: &str,
            ) -> Result<Self, ::util::db::Error> {
                Ok(row.get_unwrap::<_, Self>(column_name))
            }
        }

        impl rusqlite::types::ToSql for $thing {
            fn to_sql(&self) -> rusqlite::Result<rusqlite::types::ToSqlOutput> {
                let hex_str = self.to_hex();
                Ok(hex_str.into())
            }
        }
    };
}

/// boilerplate code for querying rows
pub fn query_rows<T, P>(conn: &Connection, sql_query: &str, sql_args: P) -> Result<Vec<T>, Error>
where
    P: IntoIterator,
    P::Item: ToSql,
    T: FromRow<T>,
{
    let mut stmt = conn.prepare(sql_query)?;
    let result = stmt.query_and_then(sql_args, |row| T::from_row(row))?;

    result.collect()
}

/// boilerplate code for querying a single row
///   if more than 1 row is returned, excess rows are ignored.
pub fn query_row<T, P>(conn: &Connection, sql_query: &str, sql_args: P) -> Result<Option<T>, Error>
where
    P: IntoIterator,
    P::Item: ToSql,
    T: FromRow<T>,
{
    let query_result = conn.query_row_and_then(sql_query, sql_args, |row| T::from_row(row));
    match query_result {
        Ok(x) => Ok(Some(x)),
        Err(Error::SqliteError(sqlite_error::QueryReturnedNoRows)) => Ok(None),
        Err(e) => Err(e),
    }
}

/// boilerplate code for querying a single row
///   if more than 1 row is returned, panic
pub fn query_expect_row<T, P>(
    conn: &Connection,
    sql_query: &str,
    sql_args: P,
) -> Result<Option<T>, Error>
where
    P: IntoIterator,
    P::Item: ToSql,
    T: FromRow<T>,
{
    let mut stmt = conn.prepare(sql_query)?;
    let mut result = stmt.query_and_then(sql_args, |row| T::from_row(row))?;
    let mut return_value = None;
    if let Some(value) = result.next() {
        return_value = Some(value?);
    }
    assert!(
        result.next().is_none(),
        "FATAL: Multiple values returned for query that expected a single result:\n {}",
        sql_query
    );
    Ok(return_value)
}

pub fn query_row_panic<T, P, F>(
    conn: &Connection,
    sql_query: &str,
    sql_args: P,
    panic_message: F,
) -> Result<Option<T>, Error>
where
    P: IntoIterator,
    P::Item: ToSql,
    T: FromRow<T>,
    F: FnOnce() -> String,
{
    let mut stmt = conn.prepare(sql_query)?;
    let mut result = stmt.query_and_then(sql_args, |row| T::from_row(row))?;
    let mut return_value = None;
    if let Some(value) = result.next() {
        return_value = Some(value?);
    }
    if result.next().is_some() {
        panic!("{}", &panic_message());
    }
    Ok(return_value)
}

/// boilerplate code for querying a column out of a sequence of rows
pub fn query_row_columns<T, P>(
    conn: &Connection,
    sql_query: &str,
    sql_args: P,
    column_name: &str,
) -> Result<Vec<T>, Error>
where
    P: IntoIterator,
    P::Item: ToSql,
    T: FromColumn<T>,
{
    let mut stmt = conn.prepare(sql_query)?;

    let mut rows = stmt.query(sql_args)?;

    // gather
    let mut row_data = vec![];
    while let Some(row) = rows.next().map_err(|e| Error::SqliteError(e))? {
        let next_row = T::from_column(&row, column_name)?;
        row_data.push(next_row);
    }

    Ok(row_data)
}

/// Boilerplate for querying a single integer (first and only item of the query must be an int)
pub fn query_int<P>(conn: &Connection, sql_query: &str, sql_args: P) -> Result<i64, Error>
where
    P: IntoIterator,
    P::Item: ToSql,
{
    let mut stmt = conn.prepare(sql_query)?;

    let mut rows = stmt.query(sql_args)?;

    let mut row_data = vec![];
    while let Some(row) = rows.next().map_err(|e| Error::SqliteError(e))? {
        if row_data.len() > 0 {
            return Err(Error::Overflow);
        }
        let i: i64 = row.get_unwrap(0);
        row_data.push(i);
    }

    if row_data.len() == 0 {
        return Err(Error::NotFoundError);
    }

    Ok(row_data[0])
}

pub fn query_count<P>(conn: &Connection, sql_query: &str, sql_args: P) -> Result<i64, Error>
where
    P: IntoIterator,
    P::Item: ToSql,
{
    query_int(conn, sql_query, sql_args)
}

/// Run a PRAGMA statement.  This can't always be done via execute(), because it may return a result (and
/// rusqlite does not like this).
pub fn sql_pragma(conn: &Connection, pragma_stmt: &str) -> Result<(), Error> {
    conn.query_row_and_then(pragma_stmt, NO_PARAMS, |_row| Ok(()))
}

/// Set up an on-disk database with a MARF index if they don't exist yet.
/// Either way, returns (db path, MARF path)
pub fn db_mkdirs(path_str: &str) -> Result<(String, String), Error> {
    let mut path = PathBuf::from(path_str);
    match fs::metadata(path_str) {
        Ok(md) => {
            if !md.is_dir() {
                error!("Not a directory: {:?}", path);
                return Err(Error::ExistsError);
            }
        }
        Err(e) => {
            if e.kind() != io::ErrorKind::NotFound {
                return Err(Error::IOError(e));
            }
            fs::create_dir_all(path_str).map_err(Error::IOError)?;
        }
    }

    path.push("marf.sqlite");
    let marf_path = path.to_str().ok_or_else(|| Error::ParseError)?.to_string();

    path.pop();
    path.push("data.sqlite");
    let data_path = path.to_str().ok_or_else(|| Error::ParseError)?.to_string();

    Ok((data_path, marf_path))
}

/// Read-only connection to a MARF-indexed DB
pub struct IndexDBConn<'a, C, T: MarfTrieId> {
    pub index: &'a MARF<T>,
    pub context: C,
}

impl<'a, C, T: MarfTrieId> IndexDBConn<'a, C, T> {
    pub fn new(index: &'a MARF<T>, context: C) -> IndexDBConn<'a, C, T> {
        IndexDBConn { index, context }
    }

    /// Get the ancestor block hash of a block of a given height, given a descendent block hash.
    pub fn get_ancestor_block_hash(
        &self,
        block_height: u64,
        tip_block_hash: &T,
    ) -> Result<Option<T>, Error> {
        get_ancestor_block_hash(self.index, block_height, tip_block_hash)
    }

    /// Get the height of an ancestor block, if it is indeed the ancestor.
    pub fn get_ancestor_block_height(
        &self,
        ancestor_block_hash: &T,
        tip_block_hash: &T,
    ) -> Result<Option<u64>, Error> {
        get_ancestor_block_height(self.index, ancestor_block_hash, tip_block_hash)
    }

    /// Get a value from the fork index
    pub fn get_indexed(&self, header_hash: &T, key: &str) -> Result<Option<String>, Error> {
        let mut ro_index = self.index.reopen_readonly()?;
        get_indexed(&mut ro_index, header_hash, key)
    }

    pub fn conn(&self) -> &DBConn {
        self.index.sqlite_conn()
    }
}

impl<'a, C, T: MarfTrieId> Deref for IndexDBConn<'a, C, T> {
    type Target = DBConn;
    fn deref(&self) -> &DBConn {
        self.conn()
    }
}

pub struct IndexDBTx<'a, C: Clone, T: MarfTrieId> {
    _index: Option<MarfTransaction<'a, T>>,
    pub context: C,
    block_linkage: Option<(T, T)>,
}

impl<'a, C: Clone, T: MarfTrieId> Deref for IndexDBTx<'a, C, T> {
    type Target = DBTx<'a>;
    fn deref(&self) -> &DBTx<'a> {
        self.tx()
    }
}

impl<'a, C: Clone, T: MarfTrieId> DerefMut for IndexDBTx<'a, C, T> {
    fn deref_mut(&mut self) -> &mut DBTx<'a> {
        self.tx_mut()
    }
}

pub fn tx_busy_handler(run_count: i32) -> bool {
    let mut sleep_count = 10;
    if run_count > 0 {
        sleep_count = 2u64.saturating_pow(run_count as u32);
    }
    sleep_count = sleep_count.saturating_add(thread_rng().gen::<u64>() % sleep_count);

    if sleep_count > 5000 {
        sleep_count = 5000;
    }

    debug!(
        "Database is locked; sleeping {}ms and trying again",
        &sleep_count
    );

    sleep_ms(sleep_count);
    true
}

/// Begin an immediate-mode transaction, and handle busy errors with exponential backoff.
/// Handling busy errors when the tx begins is preferable to doing it when the tx commits, since
/// then we don't have to worry about any extra rollback logic.
pub fn tx_begin_immediate<'a>(conn: &'a mut Connection) -> Result<DBTx<'a>, Error> {
    conn.busy_handler(Some(tx_busy_handler))?;
    let tx = Transaction::new(conn, TransactionBehavior::Immediate)?;
    Ok(tx)
}

/// Get the ancestor block hash of a block of a given height, given a descendent block hash.
pub fn get_ancestor_block_hash<T: MarfTrieId>(
    index: &MARF<T>,
    block_height: u64,
    tip_block_hash: &T,
) -> Result<Option<T>, Error> {
    assert!(block_height < u32::max_value() as u64);
    let mut read_only = index.reopen_readonly()?;
    let bh = read_only.get_block_at_height(block_height as u32, tip_block_hash)?;
    Ok(bh)
}

/// Get the height of an ancestor block, if it is indeed the ancestor.
pub fn get_ancestor_block_height<T: MarfTrieId>(
    index: &MARF<T>,
    ancestor_block_hash: &T,
    tip_block_hash: &T,
) -> Result<Option<u64>, Error> {
    let mut read_only = index.reopen_readonly()?;
    let height_opt = read_only
        .get_block_height(ancestor_block_hash, tip_block_hash)?
        .map(|height| height as u64);
    Ok(height_opt)
}

/// Load some index data
fn load_indexed(conn: &DBConn, marf_value: &MARFValue) -> Result<Option<String>, Error> {
    let mut stmt = conn
        .prepare("SELECT value FROM __fork_storage WHERE value_hash = ?1 LIMIT 2")
        .map_err(Error::SqliteError)?;
    let mut rows = stmt
        .query(&[&marf_value.to_hex() as &dyn ToSql])
        .map_err(Error::SqliteError)?;
    let mut value = None;

    while let Some(row) = rows.next().expect("FATAL: Failed to read row from Sqlite") {
        let value_str: String = row.get_unwrap(0);
        if value.is_some() {
            // should be impossible
            panic!(
                "FATAL: two or more values for {}",
                &to_hex(&marf_value.to_vec())
            );
        }
        value = Some(value_str);
    }

    Ok(value)
}

/// Get a value from the fork index
fn get_indexed<T: MarfTrieId, M: MarfConnection<T>>(
    index: &mut M,
    header_hash: &T,
    key: &str,
) -> Result<Option<String>, Error> {
    match index.get(header_hash, key) {
        Ok(Some(marf_value)) => {
            let value = load_indexed(index.sqlite_conn(), &marf_value)?
                .expect(&format!("FATAL: corrupt index: key '{}' from {} is present in the index but missing a value in the DB", &key, &header_hash));
            Ok(Some(value))
        }
        Ok(None) => Ok(None),
        Err(MARFError::NotFoundError) => Ok(None),
        Err(e) => {
            error!(
                "Failed to fetch '{}' off of {}: {:?}",
                key, &header_hash, &e
            );
            Err(Error::Corruption)
        }
    }
}

impl<'a, C: Clone, T: MarfTrieId> IndexDBTx<'a, C, T> {
    pub fn new(index: &'a mut MARF<T>, context: C) -> IndexDBTx<'a, C, T> {
        let tx = index
            .begin_tx()
            .expect("BUG: failure to begin MARF transaction");
        IndexDBTx {
            _index: Some(tx),
            block_linkage: None,
            context: context,
        }
    }

    pub fn index(&self) -> &MarfTransaction<'a, T> {
        self._index
            .as_ref()
            .expect("BUG: MarfTransaction lost, but IndexDBTx still exists")
    }

    fn index_mut(&mut self) -> &mut MarfTransaction<'a, T> {
        self._index
            .as_mut()
            .expect("BUG: MarfTransaction lost, but IndexDBTx still exists")
    }

    pub fn tx(&self) -> &DBTx<'a> {
        self.index().sqlite_tx()
    }

    pub fn tx_mut(&mut self) -> &mut DBTx<'a> {
        self.index_mut().sqlite_tx_mut()
    }

    pub fn instantiate_index(&mut self) -> Result<(), Error> {
        self.tx()
            .execute(
                r#"
        -- fork-specific key/value storage, indexed via a MARF.
        -- each row is guaranteed to be unique
        CREATE TABLE IF NOT EXISTS __fork_storage(
            value_hash TEXT NOT NULL,
            value TEXT NOT NULL,

            PRIMARY KEY(value_hash)
        );
        "#,
                NO_PARAMS,
            )
            .map_err(Error::SqliteError)?;
        Ok(())
    }

    /// Get the ancestor block hash of a block of a given height, given a descendent block hash.
    pub fn get_ancestor_block_hash(
        &mut self,
        block_height: u64,
        tip_block_hash: &T,
    ) -> Result<Option<T>, Error> {
        self.index_mut()
            .get_block_at_height(
                block_height.try_into().expect("Height > u32::max()"),
                tip_block_hash,
            )
            .map_err(Error::from)
    }

    /// Get the height of an ancestor block, if it is indeed the ancestor.
    pub fn get_ancestor_block_height(
        &mut self,
        ancestor_block_hash: &T,
        tip_block_hash: &T,
    ) -> Result<Option<u64>, Error> {
        let height_opt = self
            .index_mut()
            .get_block_height(ancestor_block_hash, tip_block_hash)?
            .map(|height| height as u64);
        Ok(height_opt)
    }

    /// Store some data to the index storage.
    fn store_indexed(&mut self, value: &String) -> Result<MARFValue, Error> {
        let marf_value = MARFValue::from_value(value);
        self.tx().execute(
            "INSERT OR REPLACE INTO __fork_storage (value_hash, value) VALUES (?1, ?2)",
            &[&to_hex(&marf_value.to_vec()), value],
        )?;
        Ok(marf_value)
    }

    /// Get a value from the fork index
    pub fn get_indexed(&mut self, header_hash: &T, key: &str) -> Result<Option<String>, Error> {
        get_indexed(self.index_mut(), header_hash, key)
    }

    pub fn put_indexed_begin(
        &mut self,
        parent_header_hash: &T,
        header_hash: &T,
    ) -> Result<(), Error> {
        match self.block_linkage {
            None => {
                self.index_mut().begin(parent_header_hash, header_hash)?;
                self.block_linkage = Some((parent_header_hash.clone(), header_hash.clone()));
                Ok(())
            }
            Some(_) => panic!("Tried to put_indexed_begin twice!"),
        }
    }

    /// Put all keys and values in a single MARF transaction.
    /// No other MARF transactions will be permitted in the lifetime of this transaction.
    pub fn put_indexed_all(
        &mut self,
        keys: &Vec<String>,
        values: &Vec<String>,
    ) -> Result<TrieHash, Error> {
        assert_eq!(keys.len(), values.len());
        assert!(self.block_linkage.is_some());

        let mut marf_values = Vec::with_capacity(values.len());
        for i in 0..values.len() {
            let marf_value = self.store_indexed(&values[i])?;
            marf_values.push(marf_value);
        }

        self.index_mut().insert_batch(&keys, marf_values)?;
        let root_hash = self.index_mut().get_root_hash()?;
        Ok(root_hash)
    }

    /// Commit the tx
    pub fn commit(mut self) -> Result<(), Error> {
        self.block_linkage = None;
        debug!("Indexed-commit: MARF index");
        let index_tx = self
            ._index
            .take()
            .expect("BUG: MarfTransaction lost, but IndexDBTx still exists");
        index_tx.commit()?;
        Ok(())
    }

    /// Get the root hash
    pub fn get_root_hash_at(&mut self, bhh: &T) -> Result<TrieHash, Error> {
        let root_hash = self.index_mut().get_root_hash_at(bhh)?;
        Ok(root_hash)
    }
}

impl<'a, C: Clone, T: MarfTrieId> Drop for IndexDBTx<'a, C, T> {
    fn drop(&mut self) {
        if let Some((ref parent, ref child)) = self.block_linkage {
            let index_tx = self
                ._index
                .take()
                .expect("BUG: MarfTransaction lost, but IndexDBTx still exists");
            debug!("Dropping MARF linkage ({},{})", parent, child);
            index_tx.drop_current();
        }
    }
}
