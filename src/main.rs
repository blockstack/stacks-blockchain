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

#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

#[macro_use]
extern crate blockstack_lib;
extern crate rusqlite;

#[macro_use(o, slog_log, slog_trace, slog_debug, slog_info, slog_warn, slog_error)]
extern crate slog;

use std::io;
use std::io::prelude::*;
use std::process;
use std::{collections::HashMap, env};
use std::{convert::TryFrom, fs};

use rusqlite::types::ToSql;
use rusqlite::Connection;
use rusqlite::OpenFlags;

use blockstack_lib::burnchains::bitcoin::spv;
use blockstack_lib::burnchains::bitcoin::BitcoinNetworkType;
use blockstack_lib::chainstate::burn::ConsensusHash;
use blockstack_lib::chainstate::stacks::db::ChainStateBootData;
use blockstack_lib::chainstate::stacks::index::marf::MarfConnection;
use blockstack_lib::chainstate::stacks::index::marf::MARF;
use blockstack_lib::chainstate::stacks::*;
use blockstack_lib::codec::StacksMessageCodec;
use blockstack_lib::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash, PoxId};
use blockstack_lib::types::chainstate::{StacksBlockHeader, StacksBlockId};
use blockstack_lib::types::proof::ClarityMarfTrieId;
use blockstack_lib::util::get_epoch_time_ms;
use blockstack_lib::util::hash::{hex_bytes, to_hex};
use blockstack_lib::util::log;
use blockstack_lib::util::retry::LogReader;
use blockstack_lib::*;
use blockstack_lib::{
    burnchains::{db::BurnchainBlockData, PoxConstants},
    chainstate::{
        burn::db::sortdb::SortitionDB,
        stacks::db::{StacksChainState, StacksHeaderInfo},
    },
    core::MemPoolDB,
    util::{hash::Hash160, vrf::VRFProof},
    vm::costs::ExecutionCost,
};
use blockstack_lib::{
    net::{db::LocalPeer, p2p::PeerNetwork, PeerAddress},
    vm::representations::UrlString,
};

fn main() {
    let mut argv: Vec<String> = env::args().collect();
    if argv.len() < 2 {
        eprintln!("Usage: {} command [args...]", argv[0]);
        process::exit(1);
    }

    if argv[1] == "--version" {
        println!(
            "{}",
            &blockstack_lib::version_string(
                option_env!("CARGO_PKG_NAME").unwrap_or(&argv[0]),
                option_env!("CARGO_PKG_VERSION").unwrap_or("0.0.0.0")
            )
        );
        process::exit(0);
    }

    if argv[1] == "decode-bitcoin-header" {
        if argv.len() < 4 {
            eprintln!(
                "Usage: {} decode-bitcoin-header [-t|-r] BLOCK_HEIGHT PATH",
                argv[0]
            );
            process::exit(1);
        }

        let mut testnet = false;
        let mut regtest = false;
        let mut idx = 0;
        for i in 0..argv.len() {
            if argv[i] == "-t" {
                testnet = true;
                idx = i;
            } else if argv[i] == "-r" {
                regtest = true;
                idx = i;
            }
        }
        if regtest && testnet {
            // don't allow both
            eprintln!(
                "Usage: {} decode-bitcoin-header [-t|-r] BLOCK_HEIGHT PATH",
                argv[0]
            );
            process::exit(1);
        }
        if idx > 0 {
            argv.remove(idx);
        }

        let mode = if testnet {
            BitcoinNetworkType::Testnet
        } else if regtest {
            BitcoinNetworkType::Regtest
        } else {
            BitcoinNetworkType::Mainnet
        };

        let height = argv[2].parse::<u64>().expect("Invalid block height");
        let headers_path = &argv[3];

        let spv_client = spv::SpvClient::new(headers_path, 0, Some(height), mode, false, false)
            .expect("FATAL: could not instantiate SPV client");
        match spv_client
            .read_block_header(height)
            .expect("FATAL: could not read block header database")
        {
            Some(header) => {
                println!("{:#?}", header);
                process::exit(0);
            }
            None => {
                eprintln!("Failed to read header");
                process::exit(1);
            }
        }
    }

    if argv[1] == "decode-tx" {
        if argv.len() < 3 {
            eprintln!("Usage: {} decode-tx TRANSACTION", argv[0]);
            process::exit(1);
        }

        let tx_str = &argv[2];
        let tx_bytes = hex_bytes(tx_str)
            .map_err(|_e| {
                eprintln!("Failed to decode transaction: must be a hex string");
                process::exit(1);
            })
            .unwrap();

        let mut cursor = io::Cursor::new(&tx_bytes);
        let mut debug_cursor = LogReader::from_reader(&mut cursor);

        let tx = StacksTransaction::consensus_deserialize(&mut debug_cursor)
            .map_err(|e| {
                eprintln!("Failed to decode transaction: {:?}", &e);
                eprintln!("Bytes consumed:");
                for buf in debug_cursor.log().iter() {
                    eprintln!("  {}", to_hex(buf));
                }
                process::exit(1);
            })
            .unwrap();

        println!("Verified: {:#?}", tx.verify());
        println!("Address: {}", tx.auth.origin().address_mainnet());

        println!("{:#?}", &tx);
        process::exit(0);
    }

    if argv[1] == "decode-block" {
        if argv.len() < 3 {
            eprintln!("Usage: {} decode-block BLOCK_PATH", argv[0]);
            process::exit(1);
        }

        let block_path = &argv[2];
        let block_data = fs::read(block_path).expect(&format!("Failed to open {}", block_path));

        let block = StacksBlock::consensus_deserialize(&mut io::Cursor::new(&block_data))
            .map_err(|_e| {
                eprintln!("Failed to decode block");
                process::exit(1);
            })
            .unwrap();

        println!("{:#?}", &block);
        process::exit(0);
    }

    if argv[1] == "get-block-inventory" {
        if argv.len() < 3 {
            eprintln!(
                "Usage: {} get-block-inventory <working-dir>

Given a <working-dir>, obtain a 2100 header hash block inventory (with an empty header cache).
",
                argv[0]
            );
            process::exit(1);
        }

        let sort_db_path = format!("{}/mainnet/burnchain/sortition", &argv[2]);
        let chain_state_path = format!("{}/mainnet/chainstate/", &argv[2]);

        let sort_db = SortitionDB::open(&sort_db_path, false)
            .expect(&format!("Failed to open {}", &sort_db_path));
        let chain_id = core::CHAIN_ID_MAINNET;
        let (chain_state, _) = StacksChainState::open(true, chain_id, &chain_state_path)
            .expect("Failed to open stacks chain state");
        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())
            .expect("Failed to get sortition chain tip");

        let start = time::Instant::now();

        let header_hashes = {
            let ic = sort_db.index_conn();

            ic.get_stacks_header_hashes(2100, &chain_tip.consensus_hash, &HashMap::new())
                .unwrap()
        };

        println!(
            "Fetched header hashes in {}",
            start.elapsed().as_seconds_f32()
        );
        let start = time::Instant::now();

        let block_inv = chain_state.get_blocks_inventory(&header_hashes).unwrap();
        println!("Fetched block inv in {}", start.elapsed().as_seconds_f32());
        println!("{:?}", &block_inv);

        println!("Done!");
        process::exit(0);
    }

    if argv[1] == "can-download-microblock" {
        if argv.len() < 3 {
            eprintln!(
                "Usage: {} can-download-microblock <working-dir>

Given a <working-dir>, obtain a 2100 header hash inventory (with an empty header cache), and then
check if the associated microblocks can be downloaded 
",
                argv[0]
            );
            process::exit(1);
        }

        let sort_db_path = format!("{}/mainnet/burnchain/sortition", &argv[2]);
        let chain_state_path = format!("{}/mainnet/chainstate/", &argv[2]);

        let sort_db = SortitionDB::open(&sort_db_path, false)
            .expect(&format!("Failed to open {}", &sort_db_path));
        let chain_id = core::CHAIN_ID_MAINNET;
        let (chain_state, _) = StacksChainState::open(true, chain_id, &chain_state_path)
            .expect("Failed to open stacks chain state");
        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())
            .expect("Failed to get sortition chain tip");

        let start = time::Instant::now();
        let local_peer = LocalPeer::new(
            0,
            0,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            0,
            None,
            0,
            UrlString::try_from("abc").unwrap(),
        );

        let header_hashes = {
            let ic = sort_db.index_conn();

            ic.get_stacks_header_hashes(2100, &chain_tip.consensus_hash, &HashMap::new())
                .unwrap()
        };

        println!(
            "Fetched header hashes in {}",
            start.elapsed().as_seconds_f32()
        );

        let start = time::Instant::now();
        let mut total_load_headers = 0;

        for (consensus_hash, block_hash_opt) in header_hashes.iter() {
            let block_hash = match block_hash_opt {
                Some(b) => b,
                None => continue,
            };

            let index_block_hash =
                StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_hash);
            let start_load_header = get_epoch_time_ms();
            let parent_header_opt = {
                let child_block_info = match StacksChainState::load_staging_block_info(
                    &chain_state.db(),
                    &index_block_hash,
                ) {
                    Ok(Some(hdr)) => hdr,
                    _ => {
                        debug!("No such block: {:?}", &index_block_hash);
                        continue;
                    }
                };

                match StacksChainState::load_block_header(
                    &chain_state.blocks_path,
                    &child_block_info.parent_consensus_hash,
                    &child_block_info.parent_anchored_block_hash,
                ) {
                    Ok(header_opt) => {
                        header_opt.map(|hdr| (hdr, child_block_info.parent_consensus_hash))
                    }
                    Err(_) => {
                        // we don't know about this parent block yet
                        debug!("{:?}: Do not have parent of anchored block {}/{} yet, so cannot ask for the microblocks it produced", &local_peer, &consensus_hash, &block_hash);
                        continue;
                    }
                }
            };

            let end_load_header = get_epoch_time_ms();
            total_load_headers += end_load_header.saturating_sub(start_load_header);

            if let Some((parent_header, parent_consensus_hash)) = parent_header_opt {
                PeerNetwork::can_download_microblock_stream(
                    &local_peer,
                    &chain_state,
                    &parent_consensus_hash,
                    &parent_header.block_hash(),
                    &consensus_hash,
                    &block_hash,
                )
                .unwrap();
            } else {
                continue;
            }
        }

        println!(
            "Checked can_download in {} (headers load took {}ms)",
            start.elapsed().as_seconds_f32(),
            total_load_headers
        );

        println!("Done!");
        process::exit(0);
    }

    if argv[1] == "evaluate-pox-anchor" {
        if argv.len() < 4 {
            eprintln!("Usage: {} evaluate-pox-anchor <path to mainnet/burnchain/sortition> <height> (last-height)", argv[0]);
            process::exit(1);
        }
        let start_height: u64 = argv[3].parse().expect("Failed to parse <height> argument");
        let end_height: u64 = argv
            .get(4)
            .map(|x| x.parse().expect("Failed to parse <end-height> argument"))
            .unwrap_or(start_height);

        let sort_db =
            SortitionDB::open(&argv[2], false).expect(&format!("Failed to open {}", argv[2]));
        let chain_tip = SortitionDB::get_canonical_sortition_tip(sort_db.conn())
            .expect("Failed to get sortition chain tip");
        let sort_conn = sort_db.index_handle(&chain_tip);

        let mut results = vec![];

        for eval_height in start_height..(1 + end_height) {
            if (sort_conn.context.first_block_height + 100) >= eval_height {
                eprintln!("Block height too low to evaluate");
                process::exit(1);
            }

            let eval_tip = SortitionDB::get_ancestor_snapshot(&sort_conn, eval_height, &chain_tip)
                .expect("Failed to get chain tip to evaluate at")
                .expect("Failed to get chain tip to evaluate at");

            let pox_consts = PoxConstants::mainnet_default();

            let result = sort_conn
                .get_chosen_pox_anchor_check_position(
                    &eval_tip.burn_header_hash,
                    &pox_consts,
                    false,
                )
                .expect("Failed to compute PoX cycle");

            match result {
                Ok((_, _, confirmed_by)) => results.push((eval_height, true, confirmed_by)),
                Err(confirmed_by) => results.push((eval_height, false, confirmed_by)),
            };
        }

        println!("Block height, Would select anchor, Anchor agreement");
        for r in results.iter() {
            println!("{}, {}, {}", &r.0, &r.1, &r.2);
        }

        process::exit(0);
    }

    if argv[1] == "try-mine" {
        if argv.len() < 3 {
            eprintln!(
                "Usage: {} try-mine <working-dir>

Given a <working-dir>, try to ''mine'' an anchored block. This invokes the miner block
assembly, but does not attempt to broadcast a block commit. This is useful for determining
what transactions a given chain state would include in an anchor block, or otherwise
simulating a miner.
",
                argv[0]
            );
            process::exit(1);
        }

        let sort_db_path = format!("{}/mainnet/burnchain/sortition", &argv[2]);
        let chain_state_path = format!("{}/mainnet/chainstate/", &argv[2]);

        let sort_db = SortitionDB::open(&sort_db_path, false)
            .expect(&format!("Failed to open {}", &sort_db_path));
        let chain_id = core::CHAIN_ID_MAINNET;
        let (chain_state, _) = StacksChainState::open(true, chain_id, &chain_state_path)
            .expect("Failed to open stacks chain state");
        let chain_tip = SortitionDB::get_canonical_burn_chain_tip(sort_db.conn())
            .expect("Failed to get sortition chain tip");

        let mut mempool_db =
            MemPoolDB::open(true, chain_id, &chain_state_path).expect("Failed to open mempool db");

        let stacks_block = chain_state.get_stacks_chain_tip(&sort_db).unwrap().unwrap();
        let parent_header = StacksChainState::get_anchored_block_header_info(
            chain_state.db(),
            &stacks_block.consensus_hash,
            &stacks_block.anchored_block_hash,
        )
        .expect("Failed to load chain tip header info")
        .expect("Failed to load chain tip header info");

        let sk = StacksPrivateKey::new();
        let mut tx_auth = TransactionAuth::from_p2pkh(&sk).unwrap();
        tx_auth.set_origin_nonce(0);

        let mut coinbase_tx = StacksTransaction::new(
            TransactionVersion::Mainnet,
            tx_auth,
            TransactionPayload::Coinbase(CoinbasePayload([0u8; 32])),
        );

        coinbase_tx.chain_id = chain_id;
        coinbase_tx.anchor_mode = TransactionAnchorMode::OnChainOnly;
        let mut tx_signer = StacksTransactionSigner::new(&coinbase_tx);
        tx_signer.sign_origin(&sk).unwrap();
        let coinbase_tx = tx_signer.get_tx().unwrap();

        let result = StacksBlockBuilder::build_anchored_block(
            &chain_state,
            &sort_db.index_conn(),
            &mut mempool_db,
            &parent_header,
            chain_tip.total_burn,
            VRFProof::empty(),
            Hash160([0; 20]),
            &coinbase_tx,
            core::BLOCK_LIMIT_MAINNET.clone(),
            None,
        );

        println!(
            "{} mined block @ height = {}",
            if result.is_ok() {
                "Successfully"
            } else {
                "Failed to"
            },
            parent_header.block_height + 1
        );
        process::exit(0);
    }

    if argv[1] == "decode-microblocks" {
        if argv.len() < 3 {
            eprintln!(
                "Usage: {} decode-microblocks MICROBLOCK_STREAM_PATH",
                argv[0]
            );
            process::exit(1);
        }

        let mblock_path = &argv[2];
        let mblock_data = fs::read(mblock_path).expect(&format!("Failed to open {}", mblock_path));

        let mut cursor = io::Cursor::new(&mblock_data);
        let mut debug_cursor = LogReader::from_reader(&mut cursor);
        let mblocks: Vec<StacksMicroblock> = Vec::consensus_deserialize(&mut debug_cursor)
            .map_err(|e| {
                eprintln!("Failed to decode microblocks: {:?}", &e);
                eprintln!("Bytes consumed:");
                for buf in debug_cursor.log().iter() {
                    eprintln!("  {}", to_hex(buf));
                }
                process::exit(1);
            })
            .unwrap();

        println!("{:#?}", &mblocks);
        process::exit(0);
    }

    if argv[1] == "header-indexed-get" {
        if argv.len() < 5 {
            eprintln!(
                "Usage: {} header-indexed-get STATE_DIR BLOCK_ID_HASH KEY",
                argv[0]
            );
            eprintln!("       STATE_DIR is either the chain state directory OR a marf index and data db file");
            process::exit(1);
        }
        let (marf_path, db_path, arg_next) = if argv.len() == 5 {
            let headers_dir = &argv[2];
            (
                format!("{}/vm/index.sqlite", &headers_dir),
                format!("{}/vm/headers.sqlite", &headers_dir),
                3,
            )
        } else {
            (argv[2].to_string(), argv[3].to_string(), 4)
        };
        let marf_tip = &argv[arg_next];
        let marf_key = &argv[arg_next + 1];

        if fs::metadata(&marf_path).is_err() {
            eprintln!("No such file or directory: {}", &marf_path);
            process::exit(1);
        }

        if fs::metadata(&db_path).is_err() {
            eprintln!("No such file or directory: {}", &db_path);
            process::exit(1);
        }

        let marf_bhh = StacksBlockId::from_hex(marf_tip).expect("Bad MARF block hash");
        let mut marf = MARF::from_path(&marf_path).expect("Failed to open MARF");
        let value_opt = marf.get(&marf_bhh, marf_key).expect("Failed to read MARF");

        if let Some(value) = value_opt {
            let conn = Connection::open_with_flags(&db_path, OpenFlags::SQLITE_OPEN_READ_ONLY)
                .expect("Failed to open DB");
            let args: &[&dyn ToSql] = &[&value.to_hex()];
            let res: Result<String, rusqlite::Error> = conn.query_row_and_then(
                "SELECT value FROM __fork_storage WHERE value_hash = ?1",
                args,
                |row| {
                    let s: String = row.get_unwrap(0);
                    Ok(s)
                },
            );

            let row = res.expect(&format!(
                "Failed to query DB for MARF value hash {}",
                &value
            ));
            println!("{}", row);
        } else {
            println!("(undefined)");
        }

        process::exit(0);
    }

    if argv[1] == "exec_program" {
        if argv.len() < 3 {
            eprintln!("Usage: {} exec_program [program-file.clar]", argv[0]);
            process::exit(1);
        }
        let program: String =
            fs::read_to_string(&argv[2]).expect(&format!("Error reading file: {}", argv[2]));
        match vm::execute(&program) {
            Ok(Some(result)) => println!("{}", result),
            Ok(None) => println!(""),
            Err(error) => {
                panic!("Program Execution Error: \n{}", error);
            }
        }
        return;
    }

    if argv[1] == "marf-get" {
        let path = &argv[2];
        let tip = BlockHeaderHash::from_hex(&argv[3]).unwrap();
        let consensustip = ConsensusHash::from_hex(&argv[4]).unwrap();
        let itip = StacksBlockHeader::make_index_block_hash(&consensustip, &tip);
        let key = &argv[5];
        let mut marf = MARF::from_path(path).unwrap();
        let res = marf.get(&itip, key).expect("MARF error.");
        match res {
            Some(x) => println!("{}", x),
            None => println!("None"),
        };
        return;
    }

    if argv[1] == "get-ancestors" {
        let path = &argv[2];
        let tip = BlockHeaderHash::from_hex(&argv[3]).unwrap();
        let burntip = BurnchainHeaderHash::from_hex(&argv[4]).unwrap();

        let conn = rusqlite::Connection::open(path).unwrap();
        let mut cur_burn = burntip.clone();
        let mut cur_tip = tip.clone();
        loop {
            println!("{}, {}", cur_burn, cur_tip);
            let (next_burn, next_tip) = match
                conn.query_row("SELECT parent_burn_header_hash, parent_anchored_block_hash FROM staging_blocks WHERE anchored_block_hash = ? and burn_header_hash = ?",
                               &[&cur_tip as &dyn rusqlite::types::ToSql, &cur_burn], |row| Ok((row.get_unwrap(0), row.get_unwrap(1)))) {
                    Ok(x) => x,
                    Err(e) => {
                        match e {
                            rusqlite::Error::QueryReturnedNoRows => {},
                            e => {
                                eprintln!("SQL Error: {}", e);
                            },
                        }
                        break
                    }
                };
            cur_burn = next_burn;
            cur_tip = next_tip;
        }
        return;
    }

    if argv[1] == "docgen" {
        println!("{}", vm::docs::make_json_api_reference());
        return;
    }

    if argv[1] == "docgen_boot" {
        println!(
            "{}",
            vm::docs::contracts::make_json_boot_contracts_reference()
        );
        return;
    }

    if argv[1] == "local" {
        clarity::invoke_command(&format!("{} {}", argv[0], argv[1]), &argv[2..]);
        return;
    }

    if argv[1] == "process-block" {
        use chainstate::burn::db::sortdb::SortitionDB;
        use chainstate::stacks::db::StacksChainState;
        let path = &argv[2];
        let sort_path = &argv[3];
        let (mut chainstate, _) = StacksChainState::open(false, 0x80000000, path).unwrap();
        let mut sortition_db = SortitionDB::open(sort_path, true).unwrap();
        let sortition_tip = SortitionDB::get_canonical_burn_chain_tip(sortition_db.conn())
            .unwrap()
            .sortition_id;
        let mut tx = sortition_db.tx_handle_begin(&sortition_tip).unwrap();
        chainstate.process_next_staging_block(&mut tx).unwrap();
        return;
    }

    if argv[1] == "replay-chainstate" {
        use blockstack_lib::types::chainstate::StacksAddress;
        use blockstack_lib::types::chainstate::StacksBlockHeader;
        use burnchains::bitcoin::indexer::BitcoinIndexer;
        use burnchains::db::BurnchainDB;
        use burnchains::Address;
        use burnchains::Burnchain;
        use chainstate::burn::db::sortdb::SortitionDB;
        use chainstate::burn::BlockSnapshot;
        use chainstate::stacks::db::blocks::StagingBlock;
        use chainstate::stacks::db::StacksChainState;
        use chainstate::stacks::index::MarfTrieId;
        use core::*;
        use net::relay::Relayer;
        use std::collections::HashMap;
        use std::collections::HashSet;
        use std::thread;
        use util::sleep_ms;
        use vm::costs::ExecutionCost;

        if argv.len() < 7 {
            eprintln!("Usage: {} OLD_CHAINSTATE_PATH OLD_SORTITION_DB_PATH OLD_BURNCHAIN_DB_PATH NEW_CHAINSTATE_PATH NEW_BURNCHAIN_DB_PATH", &argv[0]);
            process::exit(1);
        }

        let old_chainstate_path = &argv[2];
        let old_sort_path = &argv[3];
        let old_burnchaindb_path = &argv[4];

        let new_chainstate_path = &argv[5];
        let burnchain_db_path = &argv[6];

        let (old_chainstate, _) =
            StacksChainState::open(false, 0x80000000, old_chainstate_path).unwrap();
        let old_sortition_db = SortitionDB::open(old_sort_path, true).unwrap();

        // initial argon balances -- see testnet/stacks-node/conf/testnet-follower-conf.toml
        let initial_balances = vec![
            (
                StacksAddress::from_string("ST2QKZ4FKHAH1NQKYKYAYZPY440FEPK7GZ1R5HBP2")
                    .unwrap()
                    .to_account_principal(),
                10000000000000000,
            ),
            (
                StacksAddress::from_string("ST319CF5WV77KYR1H3GT0GZ7B8Q4AQPY42ETP1VPF")
                    .unwrap()
                    .to_account_principal(),
                10000000000000000,
            ),
            (
                StacksAddress::from_string("ST221Z6TDTC5E0BYR2V624Q2ST6R0Q71T78WTAX6H")
                    .unwrap()
                    .to_account_principal(),
                10000000000000000,
            ),
            (
                StacksAddress::from_string("ST2TFVBMRPS5SSNP98DQKQ5JNB2B6NZM91C4K3P7B")
                    .unwrap()
                    .to_account_principal(),
                10000000000000000,
            ),
        ];

        // block limit that argon uses
        let argon_block_limit: ExecutionCost = ExecutionCost {
            write_length: 15_0_000_000,
            write_count: 5_0_000,
            read_length: 1_000_000_000,
            read_count: 5_0_000,
            runtime: 1_00_000_000,
        };
        let burnchain = Burnchain::regtest(&burnchain_db_path);
        let first_burnchain_block_height = burnchain.first_block_height;
        let first_burnchain_block_hash = burnchain.first_block_hash;
        let (mut new_sortition_db, _) = burnchain
            .connect_db(
                true,
                first_burnchain_block_hash,
                BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP.into(),
            )
            .unwrap();

        let old_burnchaindb = BurnchainDB::connect(
            &old_burnchaindb_path,
            first_burnchain_block_height,
            &first_burnchain_block_hash,
            BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP.into(),
            true,
        )
        .unwrap();

        let mut boot_data = ChainStateBootData {
            initial_balances,
            post_flight_callback: None,
            first_burnchain_block_hash,
            first_burnchain_block_height: first_burnchain_block_height as u32,
            first_burnchain_block_timestamp: 0,
            pox_constants: PoxConstants::regtest_default(),
            get_bulk_initial_lockups: None,
            get_bulk_initial_balances: None,
            get_bulk_initial_namespaces: None,
            get_bulk_initial_names: None,
        };

        let (mut new_chainstate, _) = StacksChainState::open_and_exec(
            false,
            0x80000000,
            new_chainstate_path,
            Some(&mut boot_data),
            argon_block_limit,
        )
        .unwrap();

        let all_snapshots = old_sortition_db.get_all_snapshots().unwrap();
        let all_stacks_blocks =
            StacksChainState::get_all_staging_block_headers(&old_chainstate.db()).unwrap();

        // order block hashes by arrival index
        let mut stacks_blocks_arrival_indexes = vec![];
        for snapshot in all_snapshots.iter() {
            if !snapshot.sortition {
                continue;
            }
            if snapshot.arrival_index == 0 {
                continue;
            }
            let index_hash = StacksBlockHeader::make_index_block_hash(
                &snapshot.consensus_hash,
                &snapshot.winning_stacks_block_hash,
            );
            stacks_blocks_arrival_indexes.push((index_hash, snapshot.arrival_index));
        }
        stacks_blocks_arrival_indexes.sort_by(|ref a, ref b| a.1.partial_cmp(&b.1).unwrap());
        let stacks_blocks_arrival_order: Vec<StacksBlockId> = stacks_blocks_arrival_indexes
            .into_iter()
            .map(|(h, _)| h)
            .collect();

        let mut stacks_blocks_available: HashMap<StacksBlockId, StagingBlock> = HashMap::new();
        let num_staging_blocks = all_stacks_blocks.len();
        for staging_block in all_stacks_blocks.into_iter() {
            if !staging_block.orphaned {
                let index_hash = StacksBlockHeader::make_index_block_hash(
                    &staging_block.consensus_hash,
                    &staging_block.anchored_block_hash,
                );
                eprintln!(
                    "Will consider {}/{}",
                    &staging_block.consensus_hash, &staging_block.anchored_block_hash
                );
                stacks_blocks_available.insert(index_hash, staging_block);
            }
        }

        eprintln!(
            "\nWill replay {} stacks epochs out of {}\n",
            &stacks_blocks_available.len(),
            num_staging_blocks
        );

        let mut known_stacks_blocks = HashSet::new();
        let mut next_arrival = 0;

        let (p2p_new_sortition_db, _) = burnchain
            .connect_db(
                true,
                first_burnchain_block_hash,
                BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP.into(),
            )
            .unwrap();
        let (mut p2p_chainstate, _) = StacksChainState::open_with_block_limit(
            false,
            0x80000000,
            new_chainstate_path,
            ExecutionCost::max_value(),
        )
        .unwrap();

        let _ = thread::spawn(move || {
            loop {
                // simulate the p2p refreshing itself
                // update p2p's read-only view of the unconfirmed state
                p2p_chainstate
                    .refresh_unconfirmed_state(&p2p_new_sortition_db.index_conn())
                    .expect("Failed to open unconfirmed Clarity state");

                sleep_ms(100);
            }
        });

        for old_snapshot in all_snapshots.into_iter() {
            // replay this burnchain block
            let BurnchainBlockData {
                header: burn_block_header,
                ops: blockstack_txs,
            } = old_burnchaindb
                .get_burnchain_block(&old_snapshot.burn_header_hash)
                .unwrap();
            if old_snapshot.parent_burn_header_hash == BurnchainHeaderHash::sentinel() {
                // skip initial snapshot -- it's a placeholder
                continue;
            }

            let (new_snapshot, ..) = {
                let sortition_tip =
                    SortitionDB::get_canonical_burn_chain_tip(new_sortition_db.conn()).unwrap();
                new_sortition_db
                    .evaluate_sortition(
                        &burn_block_header,
                        blockstack_txs,
                        &burnchain,
                        &sortition_tip.sortition_id,
                        None,
                    )
                    .unwrap()
            };

            // importantly, the burnchain linkage must all match
            assert_eq!(old_snapshot.burn_header_hash, new_snapshot.burn_header_hash);
            assert_eq!(
                old_snapshot.parent_burn_header_hash,
                new_snapshot.parent_burn_header_hash
            );
            assert_eq!(old_snapshot.sortition, new_snapshot.sortition);
            assert_eq!(
                old_snapshot.winning_stacks_block_hash,
                new_snapshot.winning_stacks_block_hash
            );
            assert_eq!(old_snapshot.consensus_hash, new_snapshot.consensus_hash);
            assert_eq!(old_snapshot.sortition_hash, new_snapshot.sortition_hash);
            assert_eq!(old_snapshot.block_height, new_snapshot.block_height);
            assert_eq!(old_snapshot.total_burn, new_snapshot.total_burn);
            assert_eq!(old_snapshot.ops_hash, new_snapshot.ops_hash);

            // "discover" the stacks blocks
            if new_snapshot.sortition {
                let mut stacks_block_id = StacksBlockHeader::make_index_block_hash(
                    &new_snapshot.consensus_hash,
                    &new_snapshot.winning_stacks_block_hash,
                );
                known_stacks_blocks.insert(stacks_block_id.clone());

                if next_arrival >= stacks_blocks_arrival_order.len() {
                    // all blocks should have been queued up
                    continue;
                }

                if stacks_block_id == stacks_blocks_arrival_order[next_arrival] {
                    while next_arrival < stacks_blocks_arrival_order.len()
                        && known_stacks_blocks.contains(&stacks_block_id)
                    {
                        if let Some(_) = stacks_blocks_available.get(&stacks_block_id) {
                            // load up the block
                            let stacks_block_opt = StacksChainState::load_block(
                                &old_chainstate.blocks_path,
                                &new_snapshot.consensus_hash,
                                &new_snapshot.winning_stacks_block_hash,
                            )
                            .unwrap();
                            if let Some(stacks_block) = stacks_block_opt {
                                // insert it into the new chainstate
                                let ic = new_sortition_db.index_conn();
                                Relayer::process_new_anchored_block(
                                    &ic,
                                    &mut new_chainstate,
                                    &new_snapshot.consensus_hash,
                                    &stacks_block,
                                    0,
                                )
                                .unwrap();
                            } else {
                                warn!(
                                    "No such stacks block {}/{}",
                                    &new_snapshot.consensus_hash,
                                    &new_snapshot.winning_stacks_block_hash
                                );
                            }
                        } else {
                            warn!(
                                "Missing stacks block {}/{}",
                                &new_snapshot.consensus_hash,
                                &new_snapshot.winning_stacks_block_hash
                            );
                        }

                        next_arrival += 1;
                        if next_arrival >= stacks_blocks_arrival_order.len() {
                            break;
                        }
                        stacks_block_id = stacks_blocks_arrival_order[next_arrival].clone();
                    }
                }

                // TODO: also process microblocks
                // TODO: process blocks in arrival order
            }

            // process all new blocks
            let mut epoch_receipts = vec![];
            loop {
                let sortition_tip =
                    SortitionDB::get_canonical_burn_chain_tip(new_sortition_db.conn())
                        .unwrap()
                        .sortition_id;
                let sortition_tx = new_sortition_db.tx_handle_begin(&sortition_tip).unwrap();
                let receipts = new_chainstate.process_blocks(sortition_tx, 1).unwrap();
                if receipts.len() == 0 {
                    break;
                }
                for (epoch_receipt_opt, _) in receipts.into_iter() {
                    if let Some(epoch_receipt) = epoch_receipt_opt {
                        epoch_receipts.push(epoch_receipt);
                    }
                }
            }
        }

        eprintln!(
            "Final arrival index is {} out of {}",
            next_arrival,
            stacks_blocks_arrival_order.len()
        );
        return;
    }

    if argv.len() < 4 {
        eprintln!("Usage: {} blockchain network working_dir", argv[0]);
        process::exit(1);
    }
}
