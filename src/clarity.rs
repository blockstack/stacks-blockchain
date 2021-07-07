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

use std::convert::TryInto;
use std::env;
use std::fs;
use std::io;
use std::io::{Read, Write};
use std::iter::Iterator;
use std::path::PathBuf;
use std::process;

use rand::Rng;
use rusqlite::types::ToSql;
use rusqlite::Row;
use rusqlite::Transaction;
use rusqlite::{Connection, OpenFlags, NO_PARAMS};

use address::c32::c32_address;
use chainstate::stacks::index::{storage::TrieFileStorage, MarfTrieId};
use util::db::FromColumn;
use util::hash::{bytes_to_hex, Sha512Trunc256Sum};

use util::log;
use vm::ContractName;

use vm::analysis;
use vm::analysis::contract_interface_builder::build_contract_interface;
use vm::analysis::{errors::CheckError, errors::CheckResult, AnalysisDatabase, ContractAnalysis};
use vm::ast::build_ast;
use vm::contexts::{AssetMap, OwnedEnvironment};
use vm::costs::ExecutionCost;
use vm::costs::LimitedCostTracker;
use vm::database::{
    BurnStateDB, ClarityDatabase, HeadersDB, STXBalance, SqliteConnection, NULL_BURN_STATE_DB,
    NULL_HEADER_DB,
};
use vm::errors::{Error, InterpreterResult, RuntimeErrorType};
use vm::types::{PrincipalData, QualifiedContractIdentifier};
use vm::{execute as vm_execute, SymbolicExpression, SymbolicExpressionType, Value};

use burnchains::PoxConstants;
use burnchains::Txid;

use chainstate::stacks::boot::{STACKS_BOOT_CODE_MAINNET, STACKS_BOOT_CODE_TESTNET};
use util::boot::{boot_code_addr, boot_code_id};

use core::BLOCK_LIMIT_MAINNET;
use core::HELIUM_BLOCK_LIMIT;

use serde::Serialize;
use serde_json::json;
use util::strings::StacksString;

use codec::StacksMessageCodec;

use std::convert::TryFrom;

use crate::clarity_vm::database::marf::MarfedKV;
use crate::clarity_vm::database::marf::WritableMarfStore;
use crate::clarity_vm::database::MemoryBackingStore;
use crate::types::chainstate::BlockHeaderHash;
use crate::types::chainstate::BurnchainHeaderHash;
use crate::types::chainstate::StacksAddress;
use crate::types::chainstate::StacksBlockId;
use crate::types::chainstate::VRFSeed;
use crate::types::proof::ClarityMarfTrieId;

#[cfg(test)]
macro_rules! panic_test {
    () => {
        panic!()
    };
}
#[cfg(not(test))]
macro_rules! panic_test {
    () => {
        process::exit(1)
    };
}

#[cfg_attr(tarpaulin, skip)]
fn print_usage(invoked_by: &str) {
    eprintln!(
        "Usage: {} [command]
where command is one of:

  initialize         to initialize a local VM state database.
  check              to typecheck a potential contract definition.
  launch             to launch a initialize a new contract in the local state database.
  eval               to evaluate (in read-only mode) a program in a given contract context.
  eval_at_chaintip   like `eval`, but does not advance to a new block.
  eval_at_block      like `eval_at_chaintip`, but accepts a index-block-hash to evaluate at,
                     must be passed eval string via stdin.
  eval_raw           to typecheck and evaluate an expression without a contract or database context.
  repl               to typecheck and evaluate expressions in a stdin/stdout loop.
  execute            to execute a public function of a defined contract.
  generate_address   to generate a random Stacks public address for testing purposes.
",
        invoked_by
    );
    panic_test!()
}

#[cfg_attr(tarpaulin, skip)]
fn friendly_expect<A, B: std::fmt::Display>(input: Result<A, B>, msg: &str) -> A {
    input.unwrap_or_else(|e| {
        eprintln!("{}\nCaused by: {}", msg, e);
        panic_test!();
    })
}

#[cfg_attr(tarpaulin, skip)]
fn friendly_expect_opt<A>(input: Option<A>, msg: &str) -> A {
    input.unwrap_or_else(|| {
        eprintln!("{}", msg);
        panic_test!();
    })
}

struct EvalInput {
    marf_kv: MarfedKV,
    contract_identifier: QualifiedContractIdentifier,
    content: String,
}

fn parse(
    contract_identifier: &QualifiedContractIdentifier,
    source_code: &str,
) -> Result<Vec<SymbolicExpression>, Error> {
    let ast = build_ast(contract_identifier, source_code, &mut ())
        .map_err(|e| RuntimeErrorType::ASTError(e))?;
    Ok(ast.expressions)
}

trait ClarityStorage {
    fn get_clarity_db<'a>(
        &'a mut self,
        headers_db: &'a dyn HeadersDB,
        burn_db: &'a dyn BurnStateDB,
    ) -> ClarityDatabase<'a>;
    fn get_analysis_db<'a>(&'a mut self) -> AnalysisDatabase<'a>;
}

impl ClarityStorage for WritableMarfStore<'_> {
    fn get_clarity_db<'a>(
        &'a mut self,
        headers_db: &'a dyn HeadersDB,
        burn_db: &'a dyn BurnStateDB,
    ) -> ClarityDatabase<'a> {
        self.as_clarity_db(headers_db, burn_db)
    }

    fn get_analysis_db<'a>(&'a mut self) -> AnalysisDatabase<'a> {
        self.as_analysis_db()
    }
}

impl ClarityStorage for MemoryBackingStore {
    fn get_clarity_db<'a>(
        &'a mut self,
        _headers_db: &'a dyn HeadersDB,
        _burn_db: &'a dyn BurnStateDB,
    ) -> ClarityDatabase<'a> {
        self.as_clarity_db()
    }

    fn get_analysis_db<'a>(&'a mut self) -> AnalysisDatabase<'a> {
        self.as_analysis_db()
    }
}

fn run_analysis_free<C: ClarityStorage>(
    contract_identifier: &QualifiedContractIdentifier,
    expressions: &mut [SymbolicExpression],
    marf_kv: &mut C,
    save_contract: bool,
) -> Result<ContractAnalysis, (CheckError, LimitedCostTracker)> {
    analysis::run_analysis(
        contract_identifier,
        expressions,
        &mut marf_kv.get_analysis_db(),
        save_contract,
        LimitedCostTracker::new_free(),
    )
}

fn run_analysis<C: ClarityStorage>(
    contract_identifier: &QualifiedContractIdentifier,
    expressions: &mut [SymbolicExpression],
    header_db: &CLIHeadersDB,
    marf_kv: &mut C,
    save_contract: bool,
) -> Result<ContractAnalysis, (CheckError, LimitedCostTracker)> {
    let mainnet = header_db.is_mainnet();
    let cost_track = LimitedCostTracker::new(
        mainnet,
        if mainnet {
            BLOCK_LIMIT_MAINNET.clone()
        } else {
            HELIUM_BLOCK_LIMIT.clone()
        },
        &mut marf_kv.get_clarity_db(header_db, &NULL_BURN_STATE_DB),
    )
    .unwrap();
    analysis::run_analysis(
        contract_identifier,
        expressions,
        &mut marf_kv.get_analysis_db(),
        save_contract,
        cost_track,
    )
}

fn create_or_open_db(path: &String) -> Connection {
    let open_flags = if path == ":memory:" {
        OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
    } else {
        match fs::metadata(path) {
            Err(e) => {
                if e.kind() == io::ErrorKind::NotFound {
                    // need to create
                    if let Some(dirp) = PathBuf::from(path).parent() {
                        fs::create_dir_all(dirp).unwrap_or_else(|e| {
                            eprintln!("Failed to create {:?}: {:?}", dirp, &e);
                            panic_test!();
                        });
                    }
                    OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE
                } else {
                    panic!("FATAL: could not stat {}", path);
                }
            }
            Ok(_md) => {
                // can just open
                OpenFlags::SQLITE_OPEN_READ_WRITE
            }
        }
    };

    let conn = friendly_expect(
        Connection::open_with_flags(path, open_flags),
        &format!("FATAL: failed to open '{}'", path),
    );
    conn
}

fn get_cli_chain_tip(conn: &Connection) -> StacksBlockId {
    let mut stmt = friendly_expect(
        conn.prepare("SELECT block_hash FROM cli_chain_tips ORDER BY id DESC LIMIT 1"),
        "FATAL: could not prepare query",
    );
    let mut rows = friendly_expect(stmt.query(NO_PARAMS), "FATAL: could not fetch rows");
    let mut hash_opt = None;
    while let Some(row) = rows.next().expect("FATAL: could not read block hash") {
        let bhh = friendly_expect(
            StacksBlockId::from_column(&row, "block_hash"),
            "FATAL: could not parse block hash",
        );
        hash_opt = Some(bhh);
    }
    match hash_opt {
        Some(bhh) => bhh,
        None => StacksBlockId::sentinel(),
    }
}

fn get_cli_block_height(conn: &Connection, block_id: &StacksBlockId) -> Option<u64> {
    let mut stmt = friendly_expect(
        conn.prepare("SELECT id FROM cli_chain_tips WHERE block_hash = ?1"),
        "FATAL: could not prepare query",
    );
    let mut rows = friendly_expect(stmt.query(&[block_id]), "FATAL: could not fetch rows");
    let mut row_opt = None;

    while let Some(row) = rows.next().expect("FATAL: could not read block hash") {
        let rowid = friendly_expect(
            u64::from_column(&row, "id"),
            "FATAL: could not parse row ID",
        );
        row_opt = Some(rowid);
        break;
    }

    row_opt
}

fn get_cli_db_path(db_path: &str) -> String {
    if db_path == ":memory:" {
        return db_path.to_string();
    }

    let mut cli_db_path_buf = PathBuf::from(db_path);
    cli_db_path_buf.push("cli.sqlite");
    let cli_db_path = cli_db_path_buf
        .to_str()
        .expect(&format!(
            "FATAL: failed to convert '{}' to a string",
            db_path
        ))
        .to_string();
    cli_db_path
}

// This function is pretty weird! But it helps cut down on
//   repeating a lot of block initialization for the simulation commands.
fn in_block<F, R>(
    mut headers_db: CLIHeadersDB,
    mut marf_kv: MarfedKV,
    f: F,
) -> (CLIHeadersDB, MarfedKV, R)
where
    F: FnOnce(CLIHeadersDB, WritableMarfStore) -> (CLIHeadersDB, WritableMarfStore, R),
{
    // need to load the last block
    let (from, to) = headers_db.advance_cli_chain_tip();
    let (headers_return, result) = {
        let marf_tx = marf_kv.begin(&from, &to);
        let (headers_return, marf_return, result) = f(headers_db, marf_tx);
        marf_return.commit_to(&to);
        (headers_return, result)
    };
    (headers_return, marf_kv, result)
}

// like in_block, but does _not_ advance the chain tip.  Used for read-only queries against the
// chain tip itself.
fn at_chaintip<F, R>(db_path: &String, mut marf_kv: MarfedKV, f: F) -> R
where
    F: FnOnce(WritableMarfStore) -> (WritableMarfStore, R),
{
    // store CLI data alongside the MARF database state
    let cli_db_path = get_cli_db_path(db_path);
    let cli_db_conn = create_or_open_db(&cli_db_path);
    let from = get_cli_chain_tip(&cli_db_conn);
    let to = StacksBlockId([2u8; 32]); // 0x0202020202 ... (pattern not used anywhere else)

    let marf_tx = marf_kv.begin(&from, &to);
    let (marf_return, result) = f(marf_tx);
    marf_return.rollback_block();
    result
}

fn at_block<F, R>(blockhash: &str, mut marf_kv: MarfedKV, f: F) -> R
where
    F: FnOnce(WritableMarfStore) -> (WritableMarfStore, R),
{
    // store CLI data alongside the MARF database state
    let from = StacksBlockId::from_hex(blockhash)
        .expect(&format!("FATAL: failed to parse inputted blockhash"));
    let to = StacksBlockId([2u8; 32]); // 0x0202020202 ... (pattern not used anywhere else)

    let marf_tx = marf_kv.begin(&from, &to);
    let (marf_return, result) = f(marf_tx);
    marf_return.rollback_block();
    result
}

fn with_env_costs<F, R>(
    mainnet: bool,
    header_db: &CLIHeadersDB,
    marf: &mut WritableMarfStore,
    f: F,
) -> (R, ExecutionCost)
where
    F: FnOnce(&mut OwnedEnvironment) -> R,
{
    let mut db = marf.as_clarity_db(header_db, &NULL_BURN_STATE_DB);
    let cost_track = LimitedCostTracker::new(
        mainnet,
        if mainnet {
            BLOCK_LIMIT_MAINNET.clone()
        } else {
            HELIUM_BLOCK_LIMIT.clone()
        },
        &mut db,
    )
    .unwrap();
    let mut vm_env = OwnedEnvironment::new_cost_limited(mainnet, db, cost_track);
    let result = f(&mut vm_env);
    let cost = vm_env.get_cost_total();
    (result, cost)
}

struct CLIHeadersDB {
    db_path: String,
    conn: Connection,
}

impl CLIHeadersDB {
    fn instantiate(&mut self, mainnet: bool) {
        let cli_db_path = self.get_cli_db_path();
        let tx = friendly_expect(
            self.conn.transaction(),
            &format!("FATAL: failed to begin transaction on '{}'", cli_db_path),
        );

        friendly_expect(
            tx.execute(
                "CREATE TABLE IF NOT EXISTS cli_chain_tips(id INTEGER PRIMARY KEY AUTOINCREMENT, block_hash TEXT UNIQUE NOT NULL);",
                NO_PARAMS
            ),
            &format!("FATAL: failed to create 'cli_chain_tips' table"),
        );

        friendly_expect(
            tx.execute(
                "CREATE TABLE IF NOT EXISTS cli_config(testnet BOOLEAN NOT NULL);",
                NO_PARAMS,
            ),
            &format!("FATAL: failed to create 'cli_config' table"),
        );

        if !mainnet {
            friendly_expect(
                tx.execute("INSERT INTO cli_config (testnet) VALUES (?1)", &[&true]),
                &format!("FATAL: failed to set testnet flag"),
            );
        }

        friendly_expect(
            tx.commit(),
            &format!("FATAL: failed to instantiate CLI DB at {:?}", &cli_db_path),
        );
    }

    /// Create or open a new CLI DB at db_path.  If it already exists, then this method is a no-op.
    pub fn new(db_path: &str, mainnet: bool) -> CLIHeadersDB {
        let instantiate = db_path == ":memory:" || fs::metadata(&db_path).is_err();

        let cli_db_path = get_cli_db_path(db_path);
        let conn = create_or_open_db(&cli_db_path);
        let mut db = CLIHeadersDB {
            db_path: db_path.to_string(),
            conn: conn,
        };

        if instantiate {
            db.instantiate(mainnet);
        }
        db
    }

    /// Open an CLI DB at db_path. Returns Err() if it doesn't exist.
    /// Normally this would be Option<..>, but since this gets used with friendly_expect,
    /// using a Result<..> is necessary.
    pub fn resume(db_path: &str) -> Result<CLIHeadersDB, String> {
        let cli_db_path = get_cli_db_path(db_path);
        if let Err(e) = fs::metadata(&cli_db_path) {
            return Err(format!("Failed to access {:?}: {:?}", &cli_db_path, &e));
        }
        let conn = create_or_open_db(&cli_db_path);
        let db = CLIHeadersDB {
            db_path: db_path.to_string(),
            conn: conn,
        };

        Ok(db)
    }

    /// Make a new CLI DB in memory.
    pub fn new_memory(mainnet: bool) -> CLIHeadersDB {
        let db = CLIHeadersDB::new(":memory:", mainnet);
        db
    }

    fn get_cli_db_path(&self) -> String {
        get_cli_db_path(&self.db_path)
    }

    pub fn conn(&self) -> &Connection {
        &self.conn
    }

    pub fn is_mainnet(&self) -> bool {
        let mut stmt = friendly_expect(
            self.conn.prepare("SELECT testnet FROM cli_config LIMIT 1"),
            "FATAL: could not prepare query",
        );
        let mut rows = friendly_expect(stmt.query(NO_PARAMS), "FATAL: could not fetch rows");
        let mut mainnet = true;
        while let Some(row) = rows.next().expect("FATAL: could not read config row") {
            let testnet: bool = row.get_unwrap("testnet");
            mainnet = !testnet;
        }
        mainnet
    }

    pub fn advance_cli_chain_tip(&mut self) -> (StacksBlockId, StacksBlockId) {
        let tx = friendly_expect(
            self.conn.transaction(),
            &format!("FATAL: failed to begin transaction on '{}'", &self.db_path),
        );

        let parent_block_hash = get_cli_chain_tip(&tx);

        let random_bytes = rand::thread_rng().gen::<[u8; 32]>();
        let next_block_hash = friendly_expect_opt(
            StacksBlockId::from_bytes(&random_bytes),
            "Failed to generate random block header.",
        );

        friendly_expect(
            tx.execute(
                "INSERT INTO cli_chain_tips (block_hash) VALUES (?1)",
                &[&next_block_hash],
            ),
            &format!(
                "FATAL: failed to store next block hash in '{}'",
                &self.db_path
            ),
        );

        friendly_expect(
            tx.commit(),
            &format!(
                "FATAL: failed to commit new chain tip to '{}'",
                &self.db_path
            ),
        );

        (parent_block_hash, next_block_hash)
    }
}

impl HeadersDB for CLIHeadersDB {
    fn get_burn_header_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
    ) -> Option<BurnchainHeaderHash> {
        // mock it
        let conn = self.conn();
        if let Some(_) = get_cli_block_height(&conn, id_bhh) {
            let hash_bytes = Sha512Trunc256Sum::from_data(&id_bhh.0);
            Some(BurnchainHeaderHash(hash_bytes.0))
        } else {
            None
        }
    }

    fn get_vrf_seed_for_block(&self, id_bhh: &StacksBlockId) -> Option<VRFSeed> {
        let conn = self.conn();
        if let Some(_) = get_cli_block_height(&conn, id_bhh) {
            // mock it, but make it unique
            let hash_bytes = Sha512Trunc256Sum::from_data(&id_bhh.0);
            let hash_bytes_2 = Sha512Trunc256Sum::from_data(&hash_bytes.0);
            Some(VRFSeed(hash_bytes_2.0))
        } else {
            None
        }
    }

    fn get_stacks_block_header_hash_for_block(
        &self,
        id_bhh: &StacksBlockId,
    ) -> Option<BlockHeaderHash> {
        let conn = self.conn();
        if let Some(_) = get_cli_block_height(&conn, id_bhh) {
            // mock it, but make it unique
            let hash_bytes = Sha512Trunc256Sum::from_data(&id_bhh.0);
            let hash_bytes_2 = Sha512Trunc256Sum::from_data(&hash_bytes.0);
            let hash_bytes_3 = Sha512Trunc256Sum::from_data(&hash_bytes_2.0);
            Some(BlockHeaderHash(hash_bytes_3.0))
        } else {
            None
        }
    }
    fn get_burn_block_time_for_block(&self, id_bhh: &StacksBlockId) -> Option<u64> {
        let conn = self.conn();
        if let Some(height) = get_cli_block_height(&conn, id_bhh) {
            Some((height * 600 + 1231006505) as u64)
        } else {
            None
        }
    }
    fn get_burn_block_height_for_block(&self, id_bhh: &StacksBlockId) -> Option<u32> {
        let conn = self.conn();
        if let Some(height) = get_cli_block_height(&conn, id_bhh) {
            Some(height as u32)
        } else {
            None
        }
    }
    fn get_miner_address(&self, _id_bhh: &StacksBlockId) -> Option<StacksAddress> {
        None
    }
}

fn get_eval_input(invoked_by: &str, args: &[String]) -> EvalInput {
    if args.len() < 3 || args.len() > 4 {
        eprintln!(
            "Usage: {} {} [--costs] [contract-identifier] (program.clar) [vm-state.db]",
            invoked_by, args[0]
        );
        panic_test!();
    }

    let vm_filename = if args.len() == 3 { &args[2] } else { &args[3] };

    let content: String = {
        if args.len() == 3 {
            let mut buffer = String::new();
            friendly_expect(
                io::stdin().read_to_string(&mut buffer),
                "Error reading from stdin.",
            );
            buffer
        } else {
            friendly_expect(
                fs::read_to_string(&args[2]),
                &format!("Error reading file: {}", args[2]),
            )
        }
    };

    let contract_identifier = friendly_expect(
        QualifiedContractIdentifier::parse(&args[1]),
        "Failed to parse contract identifier.",
    );

    let marf_kv = friendly_expect(
        MarfedKV::open(vm_filename, None),
        "Failed to open VM database.",
    );
    // return (marf_kv, contract_identifier, vm_filename, content);
    return EvalInput {
        marf_kv,
        contract_identifier,
        content,
    };
}

#[derive(Serialize, Deserialize)]
struct InitialAllocation {
    principal: String,
    amount: u64,
}

fn consume_arg(
    args: &mut Vec<String>,
    argnames: &[&str],
    has_optarg: bool,
) -> Result<Option<String>, String> {
    if let Some(ref switch) = args
        .iter()
        .find(|ref arg| argnames.iter().find(|ref argname| argname == arg).is_some())
    {
        let idx = args
            .iter()
            .position(|ref arg| arg == switch)
            .expect("BUG: did not find the thing that was just found");
        let argval = if has_optarg {
            // following argument is the argument value
            if idx + 1 < args.len() {
                Some(args[idx + 1].clone())
            } else {
                // invalid usage -- expected argument
                return Err("Expected argument".to_string());
            }
        } else {
            // only care about presence of this option
            Some("".to_string())
        };

        args.remove(idx);
        if has_optarg {
            // also clear the argument
            args.remove(idx);
        }
        Ok(argval)
    } else {
        // not found
        Ok(None)
    }
}

fn install_boot_code<C: ClarityStorage>(header_db: &CLIHeadersDB, marf: &mut C) {
    let mainnet = header_db.is_mainnet();
    let boot_code = if mainnet {
        *STACKS_BOOT_CODE_MAINNET
    } else {
        *STACKS_BOOT_CODE_TESTNET
    };

    for (boot_code_name, boot_code_contract) in boot_code.iter() {
        let contract_identifier = QualifiedContractIdentifier::new(
            boot_code_addr(mainnet).into(),
            ContractName::try_from(boot_code_name.to_string()).unwrap(),
        );
        let contract_content = *boot_code_contract;

        debug!(
            "Instantiate boot code contract '{}' ({} bytes)...",
            &contract_identifier,
            boot_code_contract.len()
        );

        let mut ast = friendly_expect(
            parse(&contract_identifier, &contract_content),
            "Failed to parse program.",
        );

        let analysis_result = run_analysis_free(&contract_identifier, &mut ast, marf, true);
        match analysis_result {
            Ok(_) => {
                let db = marf.get_clarity_db(header_db, &NULL_BURN_STATE_DB);
                let mut vm_env = OwnedEnvironment::new_free(mainnet, db);
                vm_env
                    .initialize_contract(contract_identifier, &contract_content)
                    .unwrap();
            }
            Err(_) => {
                panic!("failed to instantiate boot contract");
            }
        };
    }

    // set up PoX
    let pox_contract = boot_code_id("pox", mainnet);
    let sender = PrincipalData::from(pox_contract.clone());
    let pox_params = if mainnet {
        PoxConstants::mainnet_default()
    } else {
        PoxConstants::testnet_default()
    };

    let params = vec![
        SymbolicExpression::atom_value(Value::UInt(0)), // first burnchain block height
        SymbolicExpression::atom_value(Value::UInt(pox_params.prepare_length as u128)),
        SymbolicExpression::atom_value(Value::UInt(pox_params.reward_cycle_length as u128)),
        SymbolicExpression::atom_value(Value::UInt(pox_params.pox_rejection_fraction as u128)),
    ];

    let db = marf.get_clarity_db(header_db, &NULL_BURN_STATE_DB);
    let mut vm_env = OwnedEnvironment::new_free(mainnet, db);
    vm_env
        .execute_transaction(
            sender,
            pox_contract,
            "set-burnchain-parameters",
            params.as_slice(),
        )
        .unwrap();
}

pub fn add_costs(result: &mut serde_json::Value, costs: bool, runtime: ExecutionCost) {
    if costs {
        result["costs"] = serde_json::to_value(runtime).unwrap();
    }
}

pub fn add_assets(result: &mut serde_json::Value, assets: bool, asset_map: AssetMap) {
    if assets {
        result["assets"] = asset_map.to_json();
    }
}

pub fn add_serialized_output(result: &mut serde_json::Value, value: Value) {
    let result_raw = {
        let bytes = (&value).serialize_to_vec();
        bytes_to_hex(&bytes)
    };
    result["output_serialized"] = serde_json::to_value(result_raw.as_str()).unwrap();
}

/// Returns (process-exit-code, Option<json-output>)
pub fn invoke_command(invoked_by: &str, args: &[String]) -> (i32, Option<serde_json::Value>) {
    if args.len() < 1 {
        print_usage(invoked_by);
        return (1, None);
    }

    match args[0].as_ref() {
        "initialize" => {
            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();

            let mainnet = if let Ok(Some(_)) = consume_arg(&mut argv, &["--testnet"], false) {
                false
            } else {
                true
            };

            let (db_name, allocations) = if argv.len() == 3 {
                let filename = &argv[1];
                let json_in = if filename == "-" {
                    let mut buffer = String::new();
                    friendly_expect(
                        io::stdin().read_to_string(&mut buffer),
                        "Error reading from stdin.",
                    );
                    buffer
                } else {
                    friendly_expect(
                        fs::read_to_string(filename),
                        &format!("Error reading file: {}", filename),
                    )
                };
                let allocations: Vec<InitialAllocation> =
                    friendly_expect(serde_json::from_str(&json_in), "Failure parsing JSON");

                let allocations: Vec<_> = allocations
                    .into_iter()
                    .map(|a| {
                        (
                            friendly_expect(
                                PrincipalData::parse(&a.principal),
                                "Failed to parse principal in JSON",
                            ),
                            a.amount,
                        )
                    })
                    .collect();

                (&argv[2], allocations)
            } else if argv.len() == 2 {
                (&argv[1], Vec::new())
            } else {
                eprintln!(
                    "Usage: {} {} [--testnet] (initial-allocations.json) [vm-state.db]",
                    invoked_by, argv[0]
                );
                eprintln!("   initial-allocations.json is a JSON array of {{ principal: \"ST...\", amount: 100 }} like objects.");
                eprintln!("   if the provided filename is `-`, the JSON is read from stdin.");
                eprintln!("   If --testnet is given, then testnet bootcode and block-limits are used instead of mainnet.");
                panic_test!();
            };

            debug!("Initialize {}", &db_name);
            let mut header_db = CLIHeadersDB::new(&db_name, mainnet);
            let mut marf_kv =
                friendly_expect(MarfedKV::open(db_name, None), "Failed to open VM database.");

            // install bootcode
            let state = in_block(header_db, marf_kv, |header_db, mut marf| {
                install_boot_code(&header_db, &mut marf);
                (header_db, marf, ())
            });

            header_db = state.0;
            marf_kv = state.1;

            // set initial balances
            in_block(header_db, marf_kv, |header_db, mut kv| {
                {
                    let mut db = kv.as_clarity_db(&header_db, &NULL_BURN_STATE_DB);
                    db.begin();
                    for (principal, amount) in allocations.iter() {
                        let balance = STXBalance::initial(*amount as u128);
                        let total_balance = balance.get_total_balance();

                        let mut snapshot = db.get_stx_balance_snapshot_genesis(principal);
                        snapshot.set_balance(balance);
                        snapshot.save();

                        println!("{} credited: {} uSTX", principal, total_balance);
                    }
                    db.commit();
                };
                (header_db, kv, ())
            });

            if mainnet {
                (
                    0,
                    Some(json!({
                        "message": "Database created.",
                        "network": "mainnet"
                    })),
                )
            } else {
                (
                    0,
                    Some(json!({
                        "message": "Database created.",
                        "network": "testnet"
                    })),
                )
            }
        }
        "generate_address" => {
            // random 20 bytes
            let random_bytes = rand::thread_rng().gen::<[u8; 20]>();
            // version = 22
            let addr =
                friendly_expect(c32_address(22, &random_bytes), "Failed to generate address");

            (0, Some(json!({ "address": format!("{}", addr) })))
        }
        "check" => {
            if args.len() < 2 {
                eprintln!(
                    "Usage: {} {} [program-file.clar] [--contract_id CONTRACT_ID] [--output_analysis] [--costs] [--testnet] (vm-state.db)",
                    invoked_by, args[0]
                );
                panic_test!();
            }

            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();
            let contract_id = if let Ok(optarg) = consume_arg(&mut argv, &["--contract_id"], true) {
                optarg
                    .map(|optarg_str| {
                        friendly_expect(
                            QualifiedContractIdentifier::parse(&optarg_str),
                            &format!("Error parsing contract identifier '{}", &optarg_str),
                        )
                    })
                    .unwrap_or(QualifiedContractIdentifier::transient())
            } else {
                eprintln!("Expected argument for --contract-id");
                panic_test!();
            };

            let output_analysis =
                if let Ok(optarg) = consume_arg(&mut argv, &["--output_analysis"], false) {
                    optarg.is_some()
                } else {
                    eprintln!("BUG: failed to parse arguments for --output_analysis");
                    panic_test!();
                };

            let costs = if let Ok(Some(_)) = consume_arg(&mut argv, &["--costs"], false) {
                true
            } else {
                false
            };

            // NOTE: ignored if we're using a DB
            let mut testnet_given = false;
            let mainnet = if let Ok(Some(_)) = consume_arg(&mut argv, &["--testnet"], false) {
                testnet_given = true;
                false
            } else {
                true
            };

            let content: String = if &argv[1] == "-" {
                let mut buffer = String::new();
                friendly_expect(
                    io::stdin().read_to_string(&mut buffer),
                    "Error reading from stdin.",
                );
                buffer
            } else {
                friendly_expect(
                    fs::read_to_string(&argv[1]),
                    &format!("Error reading file: {}", argv[1]),
                )
            };

            let mut ast = friendly_expect(parse(&contract_id, &content), "Failed to parse program");

            let contract_analysis_res = {
                if argv.len() >= 3 {
                    // use a persisted marf
                    if testnet_given {
                        eprintln!("WARN: ignoring --testnet in favor of DB state in {:?}. Re-instantiate the DB to change.", &argv[2]);
                    }

                    let vm_filename = &argv[2];
                    let header_db =
                        friendly_expect(CLIHeadersDB::resume(vm_filename), "Failed to open CLI DB");
                    let marf_kv = friendly_expect(
                        MarfedKV::open(vm_filename, None),
                        "Failed to open VM database.",
                    );

                    let result = at_chaintip(&argv[2], marf_kv, |mut marf| {
                        let result =
                            run_analysis(&contract_id, &mut ast, &header_db, &mut marf, false);
                        (marf, result)
                    });
                    result
                } else {
                    let header_db = CLIHeadersDB::new_memory(mainnet);
                    let mut analysis_marf = MemoryBackingStore::new();

                    install_boot_code(&header_db, &mut analysis_marf);
                    run_analysis(
                        &contract_id,
                        &mut ast,
                        &header_db,
                        &mut analysis_marf,
                        false,
                    )
                }
            };

            let mut contract_analysis = match contract_analysis_res {
                Ok(contract_analysis) => contract_analysis,
                Err((e, cost_tracker)) => {
                    let mut result = json!({
                        "message": "Checks failed.",
                        "error": {
                            "analysis": serde_json::to_value(&e.diagnostic).unwrap(),
                        }
                    });
                    add_costs(&mut result, costs, cost_tracker.get_total());
                    return (1, Some(result));
                }
            };

            let mut result = json!({
                "message": "Checks passed."
            });

            add_costs(
                &mut result,
                costs,
                contract_analysis.take_contract_cost_tracker().get_total(),
            );

            if output_analysis {
                result["analysis"] =
                    serde_json::to_value(&build_contract_interface(&contract_analysis)).unwrap();
            }
            (0, Some(result))
        }
        "repl" => {
            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();
            let mainnet = if let Ok(Some(_)) = consume_arg(&mut argv, &["--testnet"], false) {
                false
            } else {
                true
            };
            let mut marf = MemoryBackingStore::new();
            let mut vm_env = OwnedEnvironment::new_free(mainnet, marf.as_clarity_db());
            let mut exec_env = vm_env.get_exec_environment(None);
            let mut analysis_marf = MemoryBackingStore::new();

            let contract_id = QualifiedContractIdentifier::transient();

            let mut stdout = io::stdout();

            loop {
                let content: String = {
                    let mut buffer = String::new();
                    stdout.write(b"> ").unwrap_or_else(|e| {
                        panic!("Failed to write stdout prompt string:\n{}", e);
                    });
                    stdout.flush().unwrap_or_else(|e| {
                        panic!("Failed to flush stdout prompt string:\n{}", e);
                    });
                    match io::stdin().read_line(&mut buffer) {
                        Ok(_) => buffer,
                        Err(error) => {
                            eprintln!("Error reading from stdin:\n{}", error);
                            panic_test!();
                        }
                    }
                };

                let mut ast = match parse(&contract_id, &content) {
                    Ok(val) => val,
                    Err(error) => {
                        println!("Parse error:\n{}", error);
                        continue;
                    }
                };

                match run_analysis_free(&contract_id, &mut ast, &mut analysis_marf, true) {
                    Ok(_) => (),
                    Err((error, _)) => {
                        println!("Type check error:\n{}", error);
                        continue;
                    }
                }

                let eval_result = match exec_env.eval_raw(&content) {
                    Ok(val) => val,
                    Err(error) => {
                        println!("Execution error:\n{}", error);
                        continue;
                    }
                };

                println!("{}", eval_result);
            }
        }
        "eval_raw" => {
            let content: String = {
                let mut buffer = String::new();
                friendly_expect(
                    io::stdin().read_to_string(&mut buffer),
                    "Error reading from stdin.",
                );
                buffer
            };

            let mut analysis_marf = MemoryBackingStore::new();
            let mut marf = MemoryBackingStore::new();
            let mut vm_env = OwnedEnvironment::new_free(true, marf.as_clarity_db());

            let contract_id = QualifiedContractIdentifier::transient();

            let mut ast =
                friendly_expect(parse(&contract_id, &content), "Failed to parse program.");
            match run_analysis_free(&contract_id, &mut ast, &mut analysis_marf, true) {
                Ok(_) => {
                    let result = vm_env.get_exec_environment(None).eval_raw(&content);
                    match result {
                        Ok(x) => (
                            0,
                            Some(json!({
                                "output": serde_json::to_value(&x).unwrap()
                            })),
                        ),
                        Err(error) => (
                            1,
                            Some(json!({
                                "error": {
                                    "runtime": serde_json::to_value(&format!("{}", error)).unwrap()
                                }
                            })),
                        ),
                    }
                }
                Err((error, _)) => (
                    1,
                    Some(json!({
                        "error": {
                            "analysis": serde_json::to_value(&format!("{}", error)).unwrap()
                        }
                    })),
                ),
            }
        }
        "eval" => {
            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();

            let costs = if let Ok(Some(_)) = consume_arg(&mut argv, &["--costs"], false) {
                true
            } else {
                false
            };

            let evalInput = get_eval_input(invoked_by, &argv);
            let vm_filename = if argv.len() == 3 { &argv[2] } else { &argv[3] };
            let header_db =
                friendly_expect(CLIHeadersDB::resume(vm_filename), "Failed to open CLI DB");
            let marf_kv = friendly_expect(
                MarfedKV::open(vm_filename, None),
                "Failed to open VM database.",
            );
            let mainnet = header_db.is_mainnet();

            let (_, _, result_and_cost) = in_block(header_db, marf_kv, |header_db, mut marf| {
                let result_and_cost = with_env_costs(mainnet, &header_db, &mut marf, |vm_env| {
                    vm_env
                        .get_exec_environment(None)
                        .eval_read_only(&evalInput.contract_identifier, &evalInput.content)
                });
                (header_db, marf, result_and_cost)
            });

            match result_and_cost {
                (Ok(result), cost) => {
                    let mut result_json = json!({
                        "output": serde_json::to_value(&result).unwrap(),
                        "success": true,
                    });

                    add_serialized_output(&mut result_json, result);
                    add_costs(&mut result_json, costs, cost);

                    (0, Some(result_json))
                }
                (Err(error), cost) => {
                    let mut result_json = json!({
                        "error": {
                            "runtime": serde_json::to_value(&format!("{}", error)).unwrap()
                        },
                        "success": false,
                    });

                    add_costs(&mut result_json, costs, cost);

                    (1, Some(result_json))
                }
            }
        }
        "eval_at_chaintip" => {
            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();

            let costs = if let Ok(Some(_)) = consume_arg(&mut argv, &["--costs"], false) {
                true
            } else {
                false
            };

            let evalInput = get_eval_input(invoked_by, &argv);
            let vm_filename = if argv.len() == 3 { &argv[2] } else { &argv[3] };
            let header_db =
                friendly_expect(CLIHeadersDB::resume(vm_filename), "Failed to open CLI DB");
            let marf_kv = friendly_expect(
                MarfedKV::open(vm_filename, None),
                "Failed to open VM database.",
            );
            let mainnet = header_db.is_mainnet();
            let result_and_cost = at_chaintip(vm_filename, marf_kv, |mut marf| {
                let result_and_cost = with_env_costs(mainnet, &header_db, &mut marf, |vm_env| {
                    vm_env
                        .get_exec_environment(None)
                        .eval_read_only(&evalInput.contract_identifier, &evalInput.content)
                });
                (marf, result_and_cost)
            });

            match result_and_cost {
                (Ok(result), cost) => {
                    let mut result_json = json!({
                        "output": serde_json::to_value(&result).unwrap(),
                        "success": true,
                    });

                    add_serialized_output(&mut result_json, result);
                    add_costs(&mut result_json, costs, cost);

                    (0, Some(result_json))
                }
                (Err(error), cost) => {
                    let mut result_json = json!({
                        "error": {
                            "runtime": serde_json::to_value(&format!("{}", error)).unwrap()
                        },
                        "success": false,
                    });

                    add_costs(&mut result_json, costs, cost);

                    (1, Some(result_json))
                }
            }
        }
        "eval_at_block" => {
            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();

            let costs = if let Ok(Some(_)) = consume_arg(&mut argv, &["--costs"], false) {
                true
            } else {
                false
            };

            if argv.len() != 4 {
                eprintln!(
                    "Usage: {} {} [--costs] [index-block-hash] [contract-identifier] [vm/clarity dir]",
                    invoked_by, &argv[0]
                );
                panic_test!();
            }
            let chain_tip = &argv[1];
            let contract_identifier = friendly_expect(
                QualifiedContractIdentifier::parse(&argv[2]),
                "Failed to parse contract identifier.",
            );
            let content: String = {
                let mut buffer = String::new();
                friendly_expect(
                    io::stdin().read_to_string(&mut buffer),
                    "Error reading from stdin.",
                );
                buffer
            };

            let vm_filename = &argv[3];
            let header_db =
                friendly_expect(CLIHeadersDB::resume(vm_filename), "Failed to open CLI DB");
            let marf_kv = friendly_expect(
                MarfedKV::open(vm_filename, None),
                "Failed to open VM database.",
            );
            let mainnet = header_db.is_mainnet();
            let result_and_cost = at_block(chain_tip, marf_kv, |mut marf| {
                let result_and_cost = with_env_costs(mainnet, &header_db, &mut marf, |vm_env| {
                    vm_env
                        .get_exec_environment(None)
                        .eval_read_only(&contract_identifier, &content)
                });
                (marf, result_and_cost)
            });

            match result_and_cost {
                (Ok(result), cost) => {
                    let mut result_json = json!({
                        "output": serde_json::to_value(&result).unwrap(),
                        "success": true,
                    });

                    add_serialized_output(&mut result_json, result);
                    add_costs(&mut result_json, costs, cost);

                    (0, Some(result_json))
                }
                (Err(error), cost) => {
                    let mut result_json = json!({
                        "error": {
                            "runtime": serde_json::to_value(&format!("{}", error)).unwrap()
                        },
                        "success": false,
                    });

                    add_costs(&mut result_json, costs, cost);

                    (1, Some(result_json))
                }
            }
        }
        "launch" => {
            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();
            let costs = if let Ok(Some(_)) = consume_arg(&mut argv, &["--costs"], false) {
                true
            } else {
                false
            };
            let assets = if let Ok(Some(_)) = consume_arg(&mut argv, &["--assets"], false) {
                true
            } else {
                false
            };
            let output_analysis =
                if let Ok(Some(_)) = consume_arg(&mut argv, &["--output_analysis"], false) {
                    true
                } else {
                    false
                };
            if argv.len() < 4 {
                eprintln!(
                    "Usage: {} {} [--costs] [--assets] [--output_analysis] [contract-identifier] [contract-definition.clar] [vm-state.db]",
                    invoked_by, argv[0]
                );
                panic_test!();
            }

            let vm_filename = &argv[3];
            let contract_identifier = friendly_expect(
                QualifiedContractIdentifier::parse(&argv[1]),
                "Failed to parse contract identifier.",
            );

            let contract_content: String = friendly_expect(
                fs::read_to_string(&argv[2]),
                &format!("Error reading file: {}", argv[2]),
            );

            let mut ast = friendly_expect(
                parse(&contract_identifier, &contract_content),
                "Failed to parse program.",
            );
            let header_db =
                friendly_expect(CLIHeadersDB::resume(vm_filename), "Failed to open CLI DB");
            let marf_kv = friendly_expect(
                MarfedKV::open(vm_filename, None),
                "Failed to open VM database.",
            );
            let mainnet = header_db.is_mainnet();

            let (_, _, analysis_result_and_cost) =
                in_block(header_db, marf_kv, |header_db, mut marf| {
                    let analysis_result =
                        run_analysis(&contract_identifier, &mut ast, &header_db, &mut marf, true);
                    match analysis_result {
                        Err(e) => (header_db, marf, Err(e)),
                        Ok(analysis) => {
                            let result_and_cost =
                                with_env_costs(mainnet, &header_db, &mut marf, |vm_env| {
                                    vm_env
                                        .initialize_contract(contract_identifier, &contract_content)
                                });
                            (header_db, marf, Ok((analysis, result_and_cost)))
                        }
                    }
                });

            match analysis_result_and_cost {
                Ok((contract_analysis, (Ok((_x, asset_map, events)), cost))) => {
                    let mut result = json!({
                        "message": "Contract initialized!"
                    });

                    add_costs(&mut result, costs, cost);
                    add_assets(&mut result, assets, asset_map);

                    if output_analysis {
                        result["analysis"] =
                            serde_json::to_value(&build_contract_interface(&contract_analysis))
                                .unwrap();
                    }
                    let events_json: Vec<_> = events
                        .into_iter()
                        .map(|event| event.json_serialize(0, &Txid([0u8; 32]), true))
                        .collect();

                    result["events"] = serde_json::Value::Array(events_json);
                    (0, Some(result))
                }
                Err((error, cost_tracker)) => {
                    let mut result = json!({
                        "error": {
                            "initialization": serde_json::to_value(&format!("{}", error)).unwrap()
                        }
                    });

                    add_costs(&mut result, costs, cost_tracker.get_total());

                    (1, Some(result))
                }
                Ok((_, (Err(error), ..))) => (
                    1,
                    Some(json!({
                        "error": {
                            "initialization": serde_json::to_value(&format!("{}", error)).unwrap()
                        }
                    })),
                ),
            }
        }
        "execute" => {
            let mut argv: Vec<String> = args.into_iter().map(|x| x.clone()).collect();

            let costs = if let Ok(Some(_)) = consume_arg(&mut argv, &["--costs"], false) {
                true
            } else {
                false
            };
            let assets = if let Ok(Some(_)) = consume_arg(&mut argv, &["--assets"], false) {
                true
            } else {
                false
            };

            if argv.len() < 5 {
                eprintln!("Usage: {} {} [--costs] [--assets] [vm-state.db] [contract-identifier] [public-function-name] [sender-address] [args...]", invoked_by, argv[0]);
                panic_test!();
            }

            let vm_filename = &argv[1];
            let header_db =
                friendly_expect(CLIHeadersDB::resume(vm_filename), "Failed to open CLI DB");
            let marf_kv = friendly_expect(
                MarfedKV::open(vm_filename, None),
                "Failed to open VM database.",
            );
            let mainnet = header_db.is_mainnet();
            let contract_identifier = friendly_expect(
                QualifiedContractIdentifier::parse(&argv[2]),
                "Failed to parse contract identifier.",
            );

            let tx_name = &argv[3];
            let sender_in = &argv[4];

            let sender = {
                if let Ok(sender) = PrincipalData::parse_standard_principal(sender_in) {
                    PrincipalData::Standard(sender)
                } else {
                    eprintln!("Unexpected result parsing sender: {}", sender_in);
                    panic_test!();
                }
            };

            let arguments: Vec<_> = argv[5..]
                .iter()
                .map(|argument| {
                    let argument_parsed = friendly_expect(
                        vm_execute(argument),
                        &format!("Error parsing argument \"{}\"", argument),
                    );
                    let argument_value = friendly_expect_opt(
                        argument_parsed,
                        &format!("Failed to parse a value from the argument: {}", argument),
                    );
                    SymbolicExpression::atom_value(argument_value)
                })
                .collect();

            let (_, _, result_and_cost) = in_block(header_db, marf_kv, |header_db, mut marf| {
                let result_and_cost = with_env_costs(mainnet, &header_db, &mut marf, |vm_env| {
                    vm_env.execute_transaction(sender, contract_identifier, &tx_name, &arguments)
                });
                (header_db, marf, result_and_cost)
            });

            match result_and_cost {
                (Ok((x, asset_map, events)), cost) => {
                    if let Value::Response(data) = x {
                        if data.committed {
                            let mut result = json!({
                                "message": "Transaction executed and committed.",
                                "output": serde_json::to_value(&data.data).unwrap(),
                                "success": true,
                            });

                            add_serialized_output(&mut result, *data.data);
                            add_costs(&mut result, costs, cost);
                            add_assets(&mut result, assets, asset_map);

                            let events_json: Vec<_> = events
                                .into_iter()
                                .map(|event| event.json_serialize(0, &Txid([0u8; 32]), true))
                                .collect();

                            result["events"] = serde_json::Value::Array(events_json);
                            (0, Some(result))
                        } else {
                            let mut result = json!({
                                "message": "Aborted.",
                                "output": serde_json::to_value(&data.data).unwrap(),
                                "success": false,
                            });

                            add_costs(&mut result, costs, cost);
                            add_serialized_output(&mut result, *data.data);
                            add_assets(&mut result, assets, asset_map);

                            (0, Some(result))
                        }
                    } else {
                        let result = json!({
                            "error": {
                                "runtime": "Expected a ResponseType result from transaction.",
                                "output": serde_json::to_value(&x).unwrap()
                            },
                            "success": false,
                        });
                        (1, Some(result))
                    }
                }
                (Err(error), _) => {
                    let result = json!({
                        "error": {
                            "runtime": "Transaction execution error.",
                            "error": serde_json::to_value(&format!("{}", error)).unwrap()
                        },
                        "success": false,
                    });
                    (1, Some(result))
                }
            }
        }
        _ => {
            print_usage(invoked_by);
            (1, None)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_initial_alloc() {
        let db_name = format!("/tmp/db_{}", rand::thread_rng().gen::<i32>());
        let json_name = format!("/tmp/test-alloc_{}.json", rand::thread_rng().gen::<i32>());
        let clar_name = format!("/tmp/test-alloc_{}.clar", rand::thread_rng().gen::<i32>());

        fs::write(
            &json_name,
            r#"
[ { "principal": "S1G2081040G2081040G2081040G208105NK8PE5",
    "amount": 1000 },
  { "principal": "S1G2081040G2081040G2081040G208105NK8PE5.names",
    "amount": 2000 } ]
"#,
        )
        .unwrap();

        fs::write(&clar_name, r#"
(unwrap-panic (if (is-eq (stx-get-balance 'S1G2081040G2081040G2081040G208105NK8PE5) u1000) (ok 1) (err 2)))
(unwrap-panic (if (is-eq (stx-get-balance 'S1G2081040G2081040G2081040G208105NK8PE5.names) u2000) (ok 1) (err 2)))
"#).unwrap();

        let invoked = invoke_command(
            "test",
            &["initialize".to_string(), json_name.clone(), db_name.clone()],
        );
        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert_eq!(result["network"], "mainnet");

        let invoked = invoke_command(
            "test",
            &[
                "launch".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
                clar_name,
                db_name,
            ],
        );
        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
    }

    #[test]
    fn test_init_mainnet() {
        let db_name = format!("/tmp/db_{}", rand::thread_rng().gen::<i32>());
        let invoked = invoke_command("test", &["initialize".to_string(), db_name.clone()]);

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert_eq!(result["network"], "mainnet");

        let header_db = CLIHeadersDB::new(&db_name, true);
        assert!(header_db.is_mainnet());
    }

    #[test]
    fn test_init_testnet() {
        let db_name = format!("/tmp/db_{}", rand::thread_rng().gen::<i32>());
        let invoked = invoke_command(
            "test",
            &[
                "initialize".to_string(),
                "--testnet".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert_eq!(result["network"], "testnet");

        let header_db = CLIHeadersDB::new(&db_name, true);
        assert!(!header_db.is_mainnet());
    }

    #[test]
    fn test_samples() {
        let db_name = format!("/tmp/db_{}", rand::thread_rng().gen::<i32>());

        eprintln!("initialize");
        invoke_command("test", &["initialize".to_string(), db_name.clone()]);

        eprintln!("check tokens");
        let invoked = invoke_command(
            "test",
            &[
                "check".to_string(),
                "sample-contracts/tokens.clar".to_string(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);

        eprintln!("check tokens (idempotency)");
        let invoked = invoke_command(
            "test",
            &[
                "check".to_string(),
                "sample-contracts/tokens.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);

        eprintln!("launch tokens");
        let invoked = invoke_command(
            "test",
            &[
                "launch".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
                "sample-contracts/tokens.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);

        eprintln!("check names");
        let invoked = invoke_command(
            "test",
            &[
                "check".to_string(),
                "sample-contracts/names.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);

        eprintln!("check names with different contract ID");
        let invoked = invoke_command(
            "test",
            &[
                "check".to_string(),
                "sample-contracts/names.clar".to_string(),
                db_name.clone(),
                "--contract_id".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);

        eprintln!("check names with analysis");
        let invoked = invoke_command(
            "test",
            &[
                "check".to_string(),
                "--output_analysis".to_string(),
                "sample-contracts/names.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);
        assert!(result["analysis"] != json!(null));

        eprintln!("check names with cost");
        let invoked = invoke_command(
            "test",
            &[
                "check".to_string(),
                "--costs".to_string(),
                "sample-contracts/names.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);
        assert!(result["costs"] != json!(null));
        assert!(result["assets"] == json!(null));

        eprintln!("launch names with costs and assets");
        let invoked = invoke_command(
            "test",
            &[
                "launch".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.names".to_string(),
                "sample-contracts/names.clar".to_string(),
                "--costs".to_string(),
                "--assets".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);
        assert!(result["costs"] != json!(null));
        assert!(result["assets"] != json!(null));

        eprintln!("execute tokens");
        let invoked = invoke_command(
            "test",
            &[
                "execute".to_string(),
                db_name.clone(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
                "mint!".to_string(),
                "SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR".to_string(),
                "(+ u900 u100)".to_string(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);
        assert!(result["events"].as_array().unwrap().len() == 0);
        assert_eq!(result["output"], json!({"UInt": 1000}));

        eprintln!("eval tokens");
        let invoked = invoke_command(
            "test",
            &[
                "eval".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
                "sample-contracts/tokens-mint.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert_eq!(
            result["output"],
            json!({
                "Response": {
                    "committed": true,
                    "data": {
                        "UInt": 100
                    }
                }
            })
        );

        eprintln!("eval tokens with cost");
        let invoked = invoke_command(
            "test",
            &[
                "eval".to_string(),
                "--costs".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
                "sample-contracts/tokens-mint.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert_eq!(
            result["output"],
            json!({
                "Response": {
                    "committed": true,
                    "data": {
                        "UInt": 100
                    }
                }
            })
        );
        assert!(result["costs"] != json!(null));

        eprintln!("eval_at_chaintip tokens");
        let invoked = invoke_command(
            "test",
            &[
                "eval_at_chaintip".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
                "sample-contracts/tokens-mint.clar".to_string(),
                db_name.clone(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert_eq!(
            result["output"],
            json!({
                "Response": {
                    "committed": true,
                    "data": {
                        "UInt": 100
                    }
                }
            })
        );

        eprintln!("eval_at_chaintip tokens with cost");
        let invoked = invoke_command(
            "test",
            &[
                "eval_at_chaintip".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens".to_string(),
                "sample-contracts/tokens-mint.clar".to_string(),
                db_name.clone(),
                "--costs".to_string(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert_eq!(
            result["output"],
            json!({
                "Response": {
                    "committed": true,
                    "data": {
                        "UInt": 100
                    }
                }
            })
        );
        assert!(result["costs"] != json!(null));
    }

    #[test]
    fn test_assets() {
        let db_name = format!("/tmp/db_{}", rand::thread_rng().gen::<i32>());

        eprintln!("initialize");
        invoke_command("test", &["initialize".to_string(), db_name.clone()]);

        eprintln!("check tokens");
        let invoked = invoke_command(
            "test",
            &[
                "check".to_string(),
                "sample-contracts/tokens-ft.clar".to_string(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);

        eprintln!("launch tokens");
        let invoked = invoke_command(
            "test",
            &[
                "launch".to_string(),
                "S1G2081040G2081040G2081040G208105NK8PE5.tokens-ft".to_string(),
                "sample-contracts/tokens-ft.clar".to_string(),
                db_name.clone(),
                "--assets".to_string(),
            ],
        );

        let exit = invoked.0;
        let result = invoked.1.unwrap();

        eprintln!("{}", serde_json::to_string(&result).unwrap());

        assert_eq!(exit, 0);
        assert!(result["message"].as_str().unwrap().len() > 0);
        assert!(
            result["assets"]["tokens"]["S1G2081040G2081040G2081040G208105NK8PE5"]
                ["S1G2081040G2081040G2081040G208105NK8PE5.tokens-ft::tokens"]
                == "10300"
        );
        assert!(result["events"].as_array().unwrap().len() == 3);
        assert!(
            result["events"].as_array().unwrap()[0]
                == json!({
                    "committed": true,
                    "event_index": 0,
                    "ft_mint_event": {
                        "amount": "10300",
                        "asset_identifier": "S1G2081040G2081040G2081040G208105NK8PE5.tokens-ft::tokens",
                        "recipient": "S1G2081040G2081040G2081040G208105NK8PE5"
                    },
                    "txid": "0x0000000000000000000000000000000000000000000000000000000000000000",
                    "type": "ft_mint_event"
                })
        );
        assert!(
            result["events"].as_array().unwrap()[1]
                == json!({
                    "committed": true,
                    "event_index": 0,
                    "ft_transfer_event": {
                        "amount": "10000",
                        "asset_identifier": "S1G2081040G2081040G2081040G208105NK8PE5.tokens-ft::tokens",
                        "recipient": "SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR",
                        "sender": "S1G2081040G2081040G2081040G208105NK8PE5"
                    },
                    "txid": "0x0000000000000000000000000000000000000000000000000000000000000000",
                    "type": "ft_transfer_event"
                })
        );
        assert!(
            result["events"].as_array().unwrap()[2]
                == json!({
                    "committed": true,
                    "event_index": 0,
                    "ft_transfer_event": {
                        "amount": "300",
                        "asset_identifier": "S1G2081040G2081040G2081040G208105NK8PE5.tokens-ft::tokens",
                        "recipient": "SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G",
                        "sender": "S1G2081040G2081040G2081040G208105NK8PE5"
                    },
                    "txid": "0x0000000000000000000000000000000000000000000000000000000000000000",
                    "type": "ft_transfer_event"
                })
        );
    }
}
