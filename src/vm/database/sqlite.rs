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

use rusqlite::types::{FromSql, ToSql};
use rusqlite::{
    Connection, Error as SqliteError, ErrorCode as SqliteErrorCode, OptionalExtension, Row,
    Savepoint, NO_PARAMS,
};

use crate::types::chainstate::StacksBlockId;

use util::db::{sql_pragma, tx_busy_handler};

use vm::contracts::Contract;
use vm::errors::{
    Error, IncomparableError, InterpreterError, InterpreterResult as Result, RuntimeErrorType,
};

const SQL_FAIL_MESSAGE: &str = "PANIC: SQL Failure in Smart Contract VM.";

pub struct SqliteConnection {
    conn: Connection,
}

fn sqlite_put(conn: &Connection, key: &str, value: &str) {
    let params: [&dyn ToSql; 2] = [&key, &value];
    match conn.execute(
        "REPLACE INTO data_table (key, value) VALUES (?, ?)",
        &params,
    ) {
        Ok(_) => {}
        Err(e) => {
            error!("Failed to insert/replace ({},{}): {:?}", key, value, &e);
            panic!("{}", SQL_FAIL_MESSAGE);
        }
    };
}

fn sqlite_get(conn: &Connection, key: &str) -> Option<String> {
    trace!("sqlite_get {}", key);
    let params: [&dyn ToSql; 1] = [&key];
    let res = match conn
        .query_row(
            "SELECT value FROM data_table WHERE key = ?",
            &params,
            |row| row.get(0),
        )
        .optional()
    {
        Ok(x) => x,
        Err(e) => {
            error!("Failed to query '{}': {:?}", key, &e);
            panic!("{}", SQL_FAIL_MESSAGE);
        }
    };

    trace!("sqlite_get {}: {:?}", key, &res);
    res
}

fn sqlite_has_entry(conn: &Connection, key: &str) -> bool {
    sqlite_get(conn, key).is_some()
}

impl SqliteConnection {
    pub fn put(conn: &Connection, key: &str, value: &str) {
        sqlite_put(conn, key, value)
    }

    pub fn get(conn: &Connection, key: &str) -> Option<String> {
        sqlite_get(conn, key)
    }

    pub fn insert_metadata(
        conn: &Connection,
        bhh: &StacksBlockId,
        contract_hash: &str,
        key: &str,
        value: &str,
    ) {
        let key = format!("clr-meta::{}::{}", contract_hash, key);
        let params: [&dyn ToSql; 3] = [&bhh, &key, &value];

        if let Err(e) = conn.execute(
            "INSERT INTO metadata_table (blockhash, key, value) VALUES (?, ?, ?)",
            &params,
        ) {
            error!(
                "Failed to insert ({},{},{}): {:?}",
                &bhh,
                &key,
                &value.to_string(),
                &e
            );
            panic!("{}", SQL_FAIL_MESSAGE);
        }
    }

    pub fn commit_metadata_to(conn: &Connection, from: &StacksBlockId, to: &StacksBlockId) {
        let params = [to, from];
        if let Err(e) = conn.execute(
            "UPDATE metadata_table SET blockhash = ? WHERE blockhash = ?",
            &params,
        ) {
            error!("Failed to update {} to {}: {:?}", &from, &to, &e);
            panic!("{}", SQL_FAIL_MESSAGE);
        }
    }

    pub fn drop_metadata(conn: &Connection, from: &StacksBlockId) {
        if let Err(e) = conn.execute("DELETE FROM metadata_table WHERE blockhash = ?", &[from]) {
            error!("Failed to drop metadata from {}: {:?}", &from, &e);
            panic!("{}", SQL_FAIL_MESSAGE);
        }
    }

    pub fn get_metadata(
        conn: &Connection,
        bhh: &StacksBlockId,
        contract_hash: &str,
        key: &str,
    ) -> Option<String> {
        let key = format!("clr-meta::{}::{}", contract_hash, key);
        let params: [&dyn ToSql; 2] = [&bhh, &key];

        match conn
            .query_row(
                "SELECT value FROM metadata_table WHERE blockhash = ? AND key = ?",
                &params,
                |row| row.get(0),
            )
            .optional()
        {
            Ok(x) => x,
            Err(e) => {
                error!("Failed to query ({},{}): {:?}", &bhh, &key, &e);
                panic!("{}", SQL_FAIL_MESSAGE);
            }
        }
    }

    pub fn has_entry(conn: &Connection, key: &str) -> bool {
        sqlite_has_entry(conn, key)
    }
}

impl SqliteConnection {
    pub fn initialize_conn(conn: &Connection) -> Result<()> {
        conn.query_row("PRAGMA journal_mode = WAL;", NO_PARAMS, |_row| Ok(()))
            .map_err(|x| InterpreterError::SqliteError(IncomparableError { err: x }))?;

        conn.execute(
            "CREATE TABLE IF NOT EXISTS data_table
                      (key TEXT PRIMARY KEY, value TEXT)",
            NO_PARAMS,
        )
        .map_err(|x| InterpreterError::SqliteError(IncomparableError { err: x }))?;

        conn.execute(
            "CREATE TABLE IF NOT EXISTS metadata_table
                      (key TEXT NOT NULL, blockhash TEXT, value TEXT,
                       UNIQUE (key, blockhash))",
            NO_PARAMS,
        )
        .map_err(|x| InterpreterError::SqliteError(IncomparableError { err: x }))?;

        Self::check_schema(conn)?;

        Ok(())
    }
    pub fn memory() -> Result<Connection> {
        let contract_db = SqliteConnection::inner_open(":memory:")?;
        SqliteConnection::initialize_conn(&contract_db)?;
        Ok(contract_db)
    }
    pub fn open(filename: &str) -> Result<Connection> {
        let contract_db = SqliteConnection::inner_open(filename)?;
        SqliteConnection::check_schema(&contract_db)?;
        Ok(contract_db)
    }
    pub fn check_schema(conn: &Connection) -> Result<()> {
        let sql = "SELECT sql FROM sqlite_master WHERE name=?";
        let _: String = conn
            .query_row(sql, &["data_table"], |row| row.get(0))
            .map_err(|x| InterpreterError::SqliteError(IncomparableError { err: x }))?;
        let _: String = conn
            .query_row(sql, &["metadata_table"], |row| row.get(0))
            .map_err(|x| InterpreterError::SqliteError(IncomparableError { err: x }))?;
        Ok(())
    }

    pub fn inner_open(filename: &str) -> Result<Connection> {
        let conn = Connection::open(filename)
            .map_err(|x| InterpreterError::SqliteError(IncomparableError { err: x }))?;

        conn.busy_handler(Some(tx_busy_handler))
            .map_err(|x| InterpreterError::SqliteError(IncomparableError { err: x }))?;

        Ok(conn)
    }
}
