use std::cmp;
use std::sync::mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::{
    collections::HashMap,
    sync::atomic::{AtomicU64, Ordering},
};
use std::{env, thread};

use rusqlite::types::ToSql;

use crate::util::boot::boot_code_id;
use stacks::burnchains::bitcoin::address::{BitcoinAddress, BitcoinAddressType};
use stacks::burnchains::bitcoin::BitcoinNetworkType;
use stacks::burnchains::Txid;
use stacks::chainstate::burn::operations::{BlockstackOperationType, PreStxOp, TransferStxOp};
use stacks::codec::StacksMessageCodec;
use stacks::core;
use stacks::core::BLOCK_LIMIT_MAINNET;
use stacks::core::CHAIN_ID_TESTNET;
use stacks::net::atlas::{AtlasConfig, AtlasDB, MAX_ATTACHMENT_INV_PAGES_PER_REQUEST};
use stacks::net::{
    AccountEntryResponse, GetAttachmentResponse, GetAttachmentsInvResponse,
    PostTransactionRequestBody, RPCPeerInfoData,
};
use stacks::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, StacksAddress, StacksBlockHeader, StacksBlockId,
    StacksMicroblockHeader,
};
use stacks::util::hash::Hash160;
use stacks::util::hash::{bytes_to_hex, hex_bytes};
use stacks::util::secp256k1::Secp256k1PublicKey;
use stacks::util::{get_epoch_time_ms, get_epoch_time_secs, sleep_ms};
use stacks::vm::database::ClarityDeserializable;
use stacks::vm::execute;
use stacks::vm::types::PrincipalData;
use stacks::vm::Value;
use stacks::{
    burnchains::db::BurnchainDB,
    chainstate::{burn::ConsensusHash, stacks::StacksMicroblock},
};
use stacks::{
    burnchains::{Address, Burnchain, PoxConstants},
    vm::costs::ExecutionCost,
};
use stacks::{
    chainstate::stacks::{
        db::StacksChainState, StacksBlock, StacksPrivateKey, StacksPublicKey, StacksTransaction,
        TransactionPayload,
    },
    net::RPCPoxInfoData,
    util::db::query_row_columns,
    util::db::query_rows,
    util::db::u64_to_sql,
};

use crate::{
    burnchains::bitcoin_regtest_controller::UTXO, config::EventKeyType,
    config::EventObserverConfig, config::InitialBalance, neon, operations::BurnchainOpSigner,
    BitcoinRegtestController, BurnchainController, Config, ConfigFile, Keychain,
};

use crate::util::hash::{MerkleTree, Sha512Trunc256Sum};
use crate::util::secp256k1::MessageSignature;

use rand::Rng;

use super::bitcoin_regtest::BitcoinCoreController;
use super::{
    make_contract_call, make_contract_publish, make_contract_publish_microblock_only,
    make_microblock, make_stacks_transfer, make_stacks_transfer_mblock_only, to_addr, ADDR_4, SK_1,
    SK_2,
};

fn neon_integration_test_conf() -> (Config, StacksAddress) {
    let mut conf = super::new_test_conf();

    let keychain = Keychain::default(conf.node.seed.clone());

    conf.node.miner = true;
    conf.node.wait_time_for_microblocks = 500;
    conf.burnchain.burn_fee_cap = 20000;

    conf.burnchain.mode = "neon".into();
    conf.burnchain.username = Some("neon-tester".into());
    conf.burnchain.password = Some("neon-tester-pass".into());
    conf.burnchain.peer_host = "127.0.0.1".into();
    conf.burnchain.local_mining_public_key =
        Some(keychain.generate_op_signer().get_public_key().to_hex());
    conf.burnchain.commit_anchor_block_within = 0;

    // test to make sure config file parsing is correct
    let magic_bytes = Config::from_config_file(ConfigFile::xenon())
        .burnchain
        .magic_bytes;
    assert_eq!(magic_bytes.as_bytes(), &['T' as u8, '2' as u8]);
    conf.burnchain.magic_bytes = magic_bytes;
    conf.burnchain.poll_time_secs = 1;
    conf.node.pox_sync_sample_secs = 0;

    let miner_account = keychain.origin_address(conf.is_mainnet()).unwrap();

    (conf, miner_account)
}

mod test_observer {
    use std::convert::Infallible;
    use std::sync::Mutex;
    use std::thread;

    use tokio;
    use warp;
    use warp::Filter;

    pub const EVENT_OBSERVER_PORT: u16 = 50303;

    lazy_static! {
        pub static ref NEW_BLOCKS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
        pub static ref NEW_MICROBLOCKS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
        pub static ref BURN_BLOCKS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
        pub static ref MEMTXS: Mutex<Vec<String>> = Mutex::new(Vec::new());
        pub static ref MEMTXS_DROPPED: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());
        pub static ref ATTACHMENTS: Mutex<Vec<serde_json::Value>> = Mutex::new(Vec::new());
    }

    async fn handle_burn_block(
        burn_block: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let mut blocks = BURN_BLOCKS.lock().unwrap();
        blocks.push(burn_block);
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_block(block: serde_json::Value) -> Result<impl warp::Reply, Infallible> {
        let mut blocks = NEW_BLOCKS.lock().unwrap();
        blocks.push(block);
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_microblocks(
        microblocks: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let mut microblock_events = NEW_MICROBLOCKS.lock().unwrap();
        microblock_events.push(microblocks);
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_mempool_txs(txs: serde_json::Value) -> Result<impl warp::Reply, Infallible> {
        let new_rawtxs = txs
            .as_array()
            .unwrap()
            .into_iter()
            .map(|x| x.as_str().unwrap().to_string());
        let mut memtxs = MEMTXS.lock().unwrap();
        for new_tx in new_rawtxs {
            memtxs.push(new_tx);
        }
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_mempool_drop_txs(
        txs: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let dropped_txids = txs
            .get("dropped_txids")
            .unwrap()
            .as_array()
            .unwrap()
            .into_iter()
            .map(|x| x.as_str().unwrap().to_string());
        let reason = txs.get("reason").unwrap().as_str().unwrap().to_string();

        let mut memtxs = MEMTXS_DROPPED.lock().unwrap();
        for new_tx in dropped_txids {
            memtxs.push((new_tx, reason.clone()));
        }
        Ok(warp::http::StatusCode::OK)
    }

    async fn handle_attachments(
        attachments: serde_json::Value,
    ) -> Result<impl warp::Reply, Infallible> {
        let new_attachments = attachments.as_array().unwrap();
        let mut attachments = ATTACHMENTS.lock().unwrap();
        for new_attachment in new_attachments {
            attachments.push(new_attachment.clone());
        }
        Ok(warp::http::StatusCode::OK)
    }

    pub fn get_memtxs() -> Vec<String> {
        MEMTXS.lock().unwrap().clone()
    }

    pub fn get_memtx_drops() -> Vec<(String, String)> {
        MEMTXS_DROPPED.lock().unwrap().clone()
    }

    pub fn get_blocks() -> Vec<serde_json::Value> {
        NEW_BLOCKS.lock().unwrap().clone()
    }

    pub fn get_microblocks() -> Vec<serde_json::Value> {
        NEW_MICROBLOCKS.lock().unwrap().clone()
    }

    pub fn get_burn_blocks() -> Vec<serde_json::Value> {
        BURN_BLOCKS.lock().unwrap().clone()
    }

    pub fn get_attachments() -> Vec<serde_json::Value> {
        ATTACHMENTS.lock().unwrap().clone()
    }

    /// each path here should correspond to one of the paths listed in `event_dispatcher.rs`
    async fn serve() {
        let new_blocks = warp::path!("new_block")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_block);
        let mempool_txs = warp::path!("new_mempool_tx")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_mempool_txs);
        let mempool_drop_txs = warp::path!("drop_mempool_tx")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_mempool_drop_txs);
        let new_burn_blocks = warp::path!("new_burn_block")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_burn_block);
        let new_attachments = warp::path!("attachments" / "new")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_attachments);
        let new_microblocks = warp::path!("new_microblocks")
            .and(warp::post())
            .and(warp::body::json())
            .and_then(handle_microblocks);

        info!("Spawning warp server");
        warp::serve(
            new_blocks
                .or(mempool_txs)
                .or(mempool_drop_txs)
                .or(new_burn_blocks)
                .or(new_attachments)
                .or(new_microblocks),
        )
        .run(([127, 0, 0, 1], EVENT_OBSERVER_PORT))
        .await
    }

    pub fn spawn() {
        clear();
        thread::spawn(|| {
            let mut rt = tokio::runtime::Runtime::new().expect("Failed to initialize tokio");
            rt.block_on(serve());
        });
    }

    pub fn clear() {
        ATTACHMENTS.lock().unwrap().clear();
        BURN_BLOCKS.lock().unwrap().clear();
        NEW_BLOCKS.lock().unwrap().clear();
        MEMTXS.lock().unwrap().clear();
        MEMTXS_DROPPED.lock().unwrap().clear();
    }
}

const PANIC_TIMEOUT_SECS: u64 = 600;
fn next_block_and_wait(
    btc_controller: &mut BitcoinRegtestController,
    blocks_processed: &Arc<AtomicU64>,
) {
    let current = blocks_processed.load(Ordering::SeqCst);
    eprintln!(
        "Issuing block at {}, waiting for bump ({})",
        get_epoch_time_secs(),
        current
    );
    btc_controller.build_next_block(1);
    let start = Instant::now();
    while blocks_processed.load(Ordering::SeqCst) <= current {
        if start.elapsed() > Duration::from_secs(PANIC_TIMEOUT_SECS) {
            error!("Timed out waiting for block to process, trying to continue test");
            return;
        }
        thread::sleep(Duration::from_millis(100));
    }
    eprintln!(
        "Block bumped at {} ({})",
        get_epoch_time_secs(),
        blocks_processed.load(Ordering::SeqCst)
    );
}

fn wait_for_runloop(blocks_processed: &Arc<AtomicU64>) {
    let start = Instant::now();
    while blocks_processed.load(Ordering::SeqCst) == 0 {
        if start.elapsed() > Duration::from_secs(PANIC_TIMEOUT_SECS) {
            panic!("Timed out waiting for run loop to start");
        }
        thread::sleep(Duration::from_millis(100));
    }
}

fn wait_for_microblocks(microblocks_processed: &Arc<AtomicU64>, timeout: u64) -> bool {
    let mut current = microblocks_processed.load(Ordering::SeqCst);
    let start = Instant::now();
    info!("Waiting for next microblock");
    loop {
        let now = microblocks_processed.load(Ordering::SeqCst);
        if now == 0 && current != 0 {
            // wrapped around -- a new epoch started
            info!(
                "New microblock epoch started while waiting (originally {})",
                current
            );
            current = 0;
        }

        if now > current {
            break;
        }

        if start.elapsed() > Duration::from_secs(timeout) {
            warn!("Timed out waiting for microblocks to process");
            return false;
        }

        thread::sleep(Duration::from_millis(100));
    }
    return true;
}

/// returns Txid string
fn submit_tx(http_origin: &str, tx: &Vec<u8>) -> String {
    let client = reqwest::blocking::Client::new();
    let path = format!("{}/v2/transactions", http_origin);
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx.clone())
        .send()
        .unwrap();
    eprintln!("{:#?}", res);
    if res.status().is_success() {
        let res: String = res.json().unwrap();
        assert_eq!(
            res,
            StacksTransaction::consensus_deserialize(&mut &tx[..])
                .unwrap()
                .txid()
                .to_string()
        );
        return res;
    } else {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }
}

fn get_tip_anchored_block(conf: &Config) -> (ConsensusHash, StacksBlock) {
    let http_origin = format!("http://{}", &conf.node.rpc_bind);
    let client = reqwest::blocking::Client::new();

    // get the canonical chain tip
    let path = format!("{}/v2/info", &http_origin);
    let tip_info = client
        .get(&path)
        .send()
        .unwrap()
        .json::<RPCPeerInfoData>()
        .unwrap();
    let stacks_tip = tip_info.stacks_tip;
    let stacks_tip_consensus_hash = tip_info.stacks_tip_consensus_hash;

    let stacks_id_tip =
        StacksBlockHeader::make_index_block_hash(&stacks_tip_consensus_hash, &stacks_tip);

    // get the associated anchored block
    let path = format!("{}/v2/blocks/{}", &http_origin, &stacks_id_tip);
    let block_bytes = client.get(&path).send().unwrap().bytes().unwrap();
    let block = StacksBlock::consensus_deserialize(&mut block_bytes.as_ref()).unwrap();

    (stacks_tip_consensus_hash, block)
}

fn find_microblock_privkey(
    conf: &Config,
    pubkey_hash: &Hash160,
    max_tries: u64,
) -> Option<StacksPrivateKey> {
    let mut keychain = Keychain::default(conf.node.seed.clone());
    for ix in 0..max_tries {
        // the first rotation occurs at 203.
        let privk = keychain.rotate_microblock_keypair(203 + ix);
        let pubkh = Hash160::from_node_public_key(&StacksPublicKey::from_private(&privk));
        if pubkh == *pubkey_hash {
            return Some(privk);
        }
    }
    return None;
}

#[test]
#[ignore]
fn bitcoind_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, miner_account) = neon_integration_test_conf();
    let prom_bind = format!("{}:{}", "127.0.0.1", 6000);
    conf.node.prometheus_bind = Some(prom_bind.clone());

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:

    eprintln!("Miner account: {}", miner_account);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    // query for prometheus metrics
    #[cfg(feature = "monitoring_prom")]
    {
        let prom_http_origin = format!("http://{}", prom_bind);
        let client = reqwest::blocking::Client::new();
        let res = client
            .get(&prom_http_origin)
            .send()
            .unwrap()
            .text()
            .unwrap();
        assert!(res.contains("stacks_node_computed_miner_commitment_high 0"));
        assert!(res.contains("stacks_node_computed_miner_commitment_low 1"));
        assert!(res.contains("stacks_node_computed_relative_miner_score 100"));
        assert!(res.contains("stacks_node_miner_current_median_commitment_high 0"));
        assert!(res.contains("stacks_node_miner_current_median_commitment_low 1"));
        assert!(res.contains("stacks_node_active_miners_total 1"));
    }

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn most_recent_utxo_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (conf, _) = neon_integration_test_conf();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut miner_signer = Keychain::default(conf.node.seed.clone()).generate_op_signer();
    let pubkey = miner_signer.get_public_key();
    let utxos_before = btc_regtest_controller.get_all_utxos(&pubkey);

    let mut last_utxo: Option<UTXO> = None;
    let mut smallest_utxo: Option<UTXO> = None; // smallest non-dust UTXO
    let mut biggest_utxo: Option<UTXO> = None;
    for utxo in utxos_before.iter() {
        if let Some(last) = last_utxo {
            if utxo.confirmations < last.confirmations {
                last_utxo = Some(utxo.clone());
            } else {
                last_utxo = Some(last);
            }
        } else {
            last_utxo = Some(utxo.clone());
        }

        if let Some(smallest) = smallest_utxo {
            if utxo.amount > 5500 && utxo.amount < smallest.amount {
                smallest_utxo = Some(utxo.clone());
            } else {
                smallest_utxo = Some(smallest);
            }
        } else {
            smallest_utxo = Some(utxo.clone());
        }

        if let Some(biggest) = biggest_utxo {
            if utxo.amount > biggest.amount {
                biggest_utxo = Some(utxo.clone());
            } else {
                biggest_utxo = Some(biggest);
            }
        } else {
            biggest_utxo = Some(utxo.clone());
        }
    }

    let last_utxo = last_utxo.unwrap();
    let smallest_utxo = smallest_utxo.unwrap();
    let mut biggest_utxo = biggest_utxo.unwrap();

    eprintln!("Last-spent UTXO is {:?}", &last_utxo);
    eprintln!("Smallest UTXO is {:?}", &smallest_utxo);
    eprintln!("Biggest UTXO is {:?}", &biggest_utxo);

    assert_eq!(last_utxo, smallest_utxo);
    assert_ne!(biggest_utxo, last_utxo);
    assert_ne!(biggest_utxo, smallest_utxo);

    // third block will be the second mined Stacks block, and mining it should *not* spend the
    // biggest UTXO, but should spend the *smallest non-dust* UTXO
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let utxos_after = btc_regtest_controller.get_all_utxos(&pubkey);

    // last UTXO was spent, which would also have been the smallest.
    let mut has_biggest = false;
    for utxo in utxos_after.into_iter() {
        assert_ne!(utxo, last_utxo);
        assert_ne!(utxo, smallest_utxo);

        // don't care about confirmations here
        biggest_utxo.confirmations = utxo.confirmations;
        if utxo == biggest_utxo {
            has_biggest = true;
        }
    }

    // biggest UTXO is *not* spent
    assert!(has_biggest);

    channel.stop_chains_coordinator();
}

fn get_balance<F: std::fmt::Display>(http_origin: &str, account: &F) -> u128 {
    get_account(http_origin, account).balance
}

#[derive(Debug)]
struct Account {
    balance: u128,
    nonce: u64,
}

fn get_account<F: std::fmt::Display>(http_origin: &str, account: &F) -> Account {
    let client = reqwest::blocking::Client::new();
    let path = format!("{}/v2/accounts/{}?proof=0", http_origin, account);
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<AccountEntryResponse>()
        .unwrap();
    info!("Account response: {:#?}", res);
    Account {
        balance: u128::from_str_radix(&res.balance[2..], 16).unwrap(),
        nonce: res.nonce,
    }
}

fn get_pox_info(http_origin: &str) -> RPCPoxInfoData {
    let client = reqwest::blocking::Client::new();
    let path = format!("{}/v2/pox", http_origin);
    client
        .get(&path)
        .send()
        .unwrap()
        .json::<RPCPoxInfoData>()
        .unwrap()
}

fn get_chain_tip(http_origin: &str) -> (ConsensusHash, BlockHeaderHash) {
    let client = reqwest::blocking::Client::new();
    let path = format!("{}/v2/info", http_origin);
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<serde_json::Value>()
        .unwrap();
    (
        ConsensusHash::from_hex(
            res.get("stacks_tip_consensus_hash")
                .unwrap()
                .as_str()
                .unwrap(),
        )
        .unwrap(),
        BlockHeaderHash::from_hex(res.get("stacks_tip").unwrap().as_str().unwrap()).unwrap(),
    )
}

fn get_chain_tip_height(http_origin: &str) -> u64 {
    let client = reqwest::blocking::Client::new();
    let path = format!("{}/v2/info", http_origin);
    let res = client
        .get(&path)
        .send()
        .unwrap()
        .json::<RPCPeerInfoData>()
        .unwrap();

    res.stacks_tip_height
}

#[test]
#[ignore]
fn liquid_ustx_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // the contract that we'll test the costs of
    let caller_src = "
    (define-public (execute)
       (ok stx-liquid-supply))
    ";

    let spender_sk = StacksPrivateKey::new();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();

    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let spender_bal = 10_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ.clone(),
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let _sort_height = channel.get_sortitions_processed();

    let publish = make_contract_publish(&spender_sk, 0, 1000, "caller", caller_src);

    let replaced_txid = submit_tx(&http_origin, &publish);

    let publish = make_contract_publish(&spender_sk, 0, 1100, "caller", caller_src);
    submit_tx(&http_origin, &publish);

    let dropped_txs = test_observer::get_memtx_drops();
    assert_eq!(dropped_txs.len(), 1);
    assert_eq!(&dropped_txs[0].1, "ReplaceByFee");
    assert_eq!(&dropped_txs[0].0, &format!("0x{}", replaced_txid));

    // mine 1 burn block for the miner to issue the next block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // mine next burn block for the miner to win
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let call_tx = make_contract_call(
        &spender_sk,
        1,
        1000,
        &spender_addr,
        "caller",
        "execute",
        &[],
    );

    submit_tx(&http_origin, &call_tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "execute" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = <Value as ClarityDeserializable<Value>>::deserialize(&raw_result[2..]);
                let liquid_ustx = parsed.expect_result_ok().expect_u128();
                assert!(liquid_ustx > 0, "Should be more liquid ustx than 0");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");
}

#[test]
#[ignore]
fn lockup_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = neon_integration_test_conf();

    test_observer::spawn();

    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let _client = reqwest::blocking::Client::new();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query an account that unlocked STX
    // Looking at chainstate-test.txt,
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s,13888888889,1
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s,13888888889,3
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s,13888888889,3
    // 3QsabRcGFfw3B9rNpEcW9rN6twjZGwNz5s -> SN3Z4MMRJ29FVZB38FGYPE94N1D8ZGF55R7YWH00A
    let recipient_addr_str = "SN3Z4MMRJ29FVZB38FGYPE94N1D8ZGF55R7YWH00A";
    let recipient = StacksAddress::from_string(recipient_addr_str).unwrap();

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // block #1 should be unlocking STX
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    assert_eq!(get_balance(&http_origin, &recipient), 13888888889);
    let blocks = test_observer::get_blocks();
    let chain_tip = blocks.last().unwrap();

    let events = chain_tip.get("events").unwrap().as_array().unwrap();
    let mut found = false;
    for event in events.iter() {
        if event.get("type").unwrap().as_str().unwrap() == "stx_mint_event" {
            let payload = event.get("stx_mint_event").unwrap().as_object().unwrap();
            let address = payload.get("recipient").unwrap().as_str().unwrap();
            let amount = payload.get("amount").unwrap().as_str().unwrap();
            if address == recipient_addr_str && amount == "13888888889" {
                found = true;
            }
        }
    }
    assert_eq!(found, true);

    // block #2 won't unlock STX
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // block #3 should be unlocking STX
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    assert_eq!(get_balance(&http_origin, &recipient), 13888888889 * 3);

    // now let's ensure that the last block received by the event observer contains the lockup receipt
    let blocks = test_observer::get_blocks();
    let chain_tip = blocks.last().unwrap();

    let events = chain_tip.get("events").unwrap().as_array().unwrap();
    assert_eq!(events.len(), 2);
    for event in events {
        assert_eq!(
            event.get("type").unwrap().as_str().unwrap(),
            "stx_mint_event"
        );
    }

    test_observer::clear();
}

#[test]
#[ignore]
fn stx_transfer_btc_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_stx_addr: StacksAddress = to_addr(&spender_sk);
    let spender_addr: PrincipalData = spender_stx_addr.clone().into();
    let _spender_btc_addr = BitcoinAddress::from_bytes(
        BitcoinNetworkType::Regtest,
        BitcoinAddressType::PublicKeyHash,
        &spender_stx_addr.bytes.0,
    )
    .unwrap();

    let spender_2_sk = StacksPrivateKey::from_hex(SK_2).unwrap();
    let spender_2_stx_addr: StacksAddress = to_addr(&spender_2_sk);
    let spender_2_addr: PrincipalData = spender_2_stx_addr.clone().into();

    let (mut conf, _miner_account) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });

    conf.initial_balances.push(InitialBalance {
        address: spender_2_addr.clone(),
        amount: 100300,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the spender's account:
    assert_eq!(get_balance(&http_origin, &spender_addr), 100300);

    // okay, let's send a pre-stx op.
    let pre_stx_op = PreStxOp {
        output: spender_stx_addr.clone(),
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut miner_signer = Keychain::default(conf.node.seed.clone()).generate_op_signer();

    assert!(
        btc_regtest_controller.submit_operation(
            BlockstackOperationType::PreStx(pre_stx_op),
            &mut miner_signer,
            1
        ),
        "Pre-stx operation should submit successfully"
    );

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // let's fire off our transfer op.
    let recipient_sk = StacksPrivateKey::new();
    let recipient_addr = to_addr(&recipient_sk);
    let transfer_stx_op = TransferStxOp {
        sender: spender_stx_addr.clone(),
        recipient: recipient_addr.clone(),
        transfered_ustx: 100_000,
        memo: vec![],
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut spender_signer = BurnchainOpSigner::new(spender_sk.clone(), false);

    assert!(
        btc_regtest_controller.submit_operation(
            BlockstackOperationType::TransferStx(transfer_stx_op),
            &mut spender_signer,
            1
        ),
        "Transfer operation should submit successfully"
    );
    // should be elected in the same block as the transfer, so balances should be unchanged.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    assert_eq!(get_balance(&http_origin, &spender_addr), 100300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 0);

    // this block should process the transfer
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(get_balance(&http_origin, &spender_addr), 300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 100_000);
    assert_eq!(get_balance(&http_origin, &spender_2_addr), 100_300);

    // now let's do a pre-stx-op and a transfer op in the same burnchain block...
    // NOTE: bitcoind really doesn't want to return the utxo from the first op for some reason,
    //    so we have to get a little creative...

    // okay, let's send a pre-stx op.
    let pre_stx_op = PreStxOp {
        output: spender_2_stx_addr.clone(),
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut miner_signer = Keychain::default(conf.node.seed.clone()).generate_op_signer();

    let pre_stx_tx = btc_regtest_controller
        .submit_manual(
            BlockstackOperationType::PreStx(pre_stx_op),
            &mut miner_signer,
            None,
        )
        .expect("Pre-stx operation should submit successfully");

    let transfer_stx_utxo = UTXO {
        txid: pre_stx_tx.txid(),
        vout: 1,
        script_pub_key: pre_stx_tx.output[1].script_pubkey.clone(),
        amount: pre_stx_tx.output[1].value,
        confirmations: 0,
    };

    // let's fire off our transfer op.
    let transfer_stx_op = TransferStxOp {
        sender: spender_2_stx_addr.clone(),
        recipient: recipient_addr.clone(),
        transfered_ustx: 100_000,
        memo: vec![],
        // to be filled in
        txid: Txid([0u8; 32]),
        vtxindex: 0,
        block_height: 0,
        burn_header_hash: BurnchainHeaderHash([0u8; 32]),
    };

    let mut spender_signer = BurnchainOpSigner::new(spender_2_sk.clone(), false);

    btc_regtest_controller
        .submit_manual(
            BlockstackOperationType::TransferStx(transfer_stx_op),
            &mut spender_signer,
            Some(transfer_stx_utxo),
        )
        .expect("Transfer operation should submit successfully");

    // should be elected in the same block as the transfer, so balances should be unchanged.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(get_balance(&http_origin, &spender_addr), 300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 100_000);
    assert_eq!(get_balance(&http_origin, &spender_2_addr), 100_300);

    // should process the transfer
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    assert_eq!(get_balance(&http_origin, &spender_addr), 300);
    assert_eq!(get_balance(&http_origin, &recipient_addr), 200_000);
    assert_eq!(get_balance(&http_origin, &spender_2_addr), 300);

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn bitcoind_resubmission_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (mut conf, _miner_account) = neon_integration_test_conf();

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // next block, issue a commit
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's figure out the current chain tip
    let chain_tip = get_chain_tip(&http_origin);

    // HACK: this test relies on manually inserting a bad microblock into the chain state.
    //  this behavior is not guaranteed to continue to work like this, so at some point this
    //  test will need to be updated to handle that.
    {
        let (mut chainstate, _) = StacksChainState::open(
            false,
            conf.burnchain.chain_id,
            &conf.get_chainstate_path_str(),
        )
        .unwrap();
        let mut tx = chainstate.db_tx_begin().unwrap();

        let (consensus_hash, stacks_block) = get_tip_anchored_block(&conf);

        //        let tip_hash = StacksBlockId::new(&consensus_hash, &stacks_block.header.block_hash());

        let ublock_privk =
            find_microblock_privkey(&conf, &stacks_block.header.microblock_pubkey_hash, 1024)
                .unwrap();

        let garbage_tx = make_stacks_transfer_mblock_only(
            &spender_sk,
            0,
            100,
            &PrincipalData::from(StacksAddress::burn_address(false)),
            1000,
        );
        let mut garbage_block = StacksMicroblock::first_unsigned(
            &chain_tip.1,
            vec![StacksTransaction::consensus_deserialize(&mut garbage_tx.as_slice()).unwrap()],
        );
        garbage_block.header.prev_block = BlockHeaderHash([3; 32]);
        garbage_block.header.sequence = 1;
        garbage_block.sign(&ublock_privk).unwrap();

        eprintln!("Minting microblock at {}/{}", &chain_tip.0, &chain_tip.1);
        StacksChainState::store_staging_microblock(
            &mut tx,
            &consensus_hash,
            &stacks_block.header.block_hash(),
            &garbage_block,
        )
        .unwrap();
        tx.commit().unwrap();
    }

    thread::sleep(Duration::from_secs(30));

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let burnchain_db = BurnchainDB::open(
        &btc_regtest_controller
            .get_burnchain()
            .get_burnchaindb_path(),
        false,
    )
    .unwrap();

    let burn_tip = burnchain_db.get_canonical_chain_tip().unwrap();
    let last_burn_block = burnchain_db
        .get_burnchain_block(&burn_tip.block_hash)
        .unwrap();

    assert_eq!(
        last_burn_block.ops.len(),
        1,
        "Should only have ONE operation in the last burn block"
    );

    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn bitcoind_forking_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let (conf, miner_account) = neon_integration_test_conf();

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut sort_height = channel.get_sortitions_processed();
    eprintln!("Sort height: {}", sort_height);

    while sort_height < 210 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {}", sort_height);
    }
    // let's query the miner's account nonce:

    eprintln!("Miner account: {}", miner_account);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 7);

    // okay, let's figure out the burn block we want to fork away.
    let burn_header_hash_to_fork = btc_regtest_controller.get_block_hash(206);
    btc_regtest_controller.invalidate_block(&burn_header_hash_to_fork);
    btc_regtest_controller.build_next_block(5);

    thread::sleep(Duration::from_secs(5));
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 2);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    // but we're able to keep on mining
    assert_eq!(account.nonce, 3);

    channel.stop_chains_coordinator();
}

/// Returns a StacksMicroblock with the given transactions, sequence, and parent block that is
/// signed with the given private key.
fn make_signed_microblock(
    block_privk: &StacksPrivateKey,
    txs: Vec<StacksTransaction>,
    parent_block: BlockHeaderHash,
    seq: u16,
) -> StacksMicroblock {
    let mut rng = rand::thread_rng();

    let txid_vecs = txs.iter().map(|tx| tx.txid().as_bytes().to_vec()).collect();
    let merkle_tree = MerkleTree::<Sha512Trunc256Sum>::new(&txid_vecs);
    let tx_merkle_root = merkle_tree.root();

    let mut mblock = StacksMicroblock {
        header: StacksMicroblockHeader {
            version: rng.gen(),
            sequence: seq,
            prev_block: parent_block,
            tx_merkle_root: tx_merkle_root,
            signature: MessageSignature([0u8; 65]),
        },
        txs: txs,
    };
    mblock.sign(block_privk).unwrap();
    mblock
}

#[test]
#[ignore]
fn microblock_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();
    let second_spender_sk = StacksPrivateKey::from_hex(SK_2).unwrap();
    let second_spender_addr: PrincipalData = to_addr(&second_spender_sk).into();

    let (mut conf, miner_account) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });
    conf.initial_balances.push(InitialBalance {
        address: second_spender_addr.clone(),
        amount: 10000,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 10_000;
    conf.node.microblock_frequency = 1_000;

    test_observer::spawn();

    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    info!("Miner account: {}", miner_account);
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    // and our first spender
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, 100300);
    assert_eq!(account.nonce, 0);

    // and our second spender
    let account = get_account(&http_origin, &second_spender_addr);
    assert_eq!(account.balance, 10000);
    assert_eq!(account.nonce, 0);

    // okay, let's push a transaction that is marked microblock only!
    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let tx = make_stacks_transfer_mblock_only(&spender_sk, 0, 1000, &recipient.into(), 1000);
    submit_tx(&http_origin, &tx);

    info!("Try to mine a microblock-only tx");

    // now let's mine a couple blocks, and then check the sender's nonce.
    // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // this one will contain the sortition from above anchor block,
    //    which *should* have also confirmed the microblock.
    info!("Wait for second block");
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // I guess let's push another block for good measure?
    info!("Wait for third block");
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    info!("Test microblock");

    // microblock must have bumped our nonce
    // and our spender
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.nonce, 1);

    // push another two transactions that are marked microblock only
    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let unconfirmed_tx_bytes =
        make_stacks_transfer_mblock_only(&spender_sk, 1, 1000, &recipient.into(), 1000);
    let unconfirmed_tx =
        StacksTransaction::consensus_deserialize(&mut &unconfirmed_tx_bytes[..]).unwrap();
    let second_unconfirmed_tx_bytes =
        make_stacks_transfer_mblock_only(&second_spender_sk, 0, 1000, &recipient.into(), 1500);
    let second_unconfirmed_tx =
        StacksTransaction::consensus_deserialize(&mut &second_unconfirmed_tx_bytes[..]).unwrap();

    // TODO (hack) instantiate the sortdb in the burnchain
    let _ = btc_regtest_controller.sortdb_mut();

    // put each into a microblock
    let (first_microblock, second_microblock) = {
        let path = format!("{}/v2/info", &http_origin);
        let tip_info = client
            .get(&path)
            .send()
            .unwrap()
            .json::<RPCPeerInfoData>()
            .unwrap();
        let stacks_tip = tip_info.stacks_tip;

        let (consensus_hash, stacks_block) = get_tip_anchored_block(&conf);
        let tip_hash =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &stacks_block.block_hash());
        let privk =
            find_microblock_privkey(&conf, &stacks_block.header.microblock_pubkey_hash, 1024)
                .unwrap();
        let (mut chainstate, _) =
            StacksChainState::open(false, CHAIN_ID_TESTNET, &conf.get_chainstate_path_str())
                .unwrap();

        chainstate
            .reload_unconfirmed_state(&btc_regtest_controller.sortdb_ref().index_conn(), tip_hash)
            .unwrap();
        let first_microblock = make_microblock(
            &privk,
            &mut chainstate,
            &btc_regtest_controller.sortdb_ref().index_conn(),
            consensus_hash,
            stacks_block.clone(),
            vec![unconfirmed_tx],
        );

        let second_microblock =
            make_signed_microblock(&privk, vec![second_unconfirmed_tx], stacks_tip, 1);

        (first_microblock, second_microblock)
    };

    let mut microblock_bytes = vec![];
    first_microblock
        .consensus_serialize(&mut microblock_bytes)
        .unwrap();

    // post the first microblock
    let path = format!("{}/v2/microblocks", &http_origin);
    let res: String = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(microblock_bytes.clone())
        .send()
        .unwrap()
        .json()
        .unwrap();

    assert_eq!(res, format!("{}", &first_microblock.block_hash()));

    eprintln!("\n\nBegin testing\nmicroblock: {:?}\n\n", &first_microblock);

    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 98300);

    let mut second_microblock_bytes = vec![];
    second_microblock
        .consensus_serialize(&mut second_microblock_bytes)
        .unwrap();

    // post the second microblock
    let path = format!("{}/v2/microblocks", &http_origin);
    let res: String = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(second_microblock_bytes.clone())
        .send()
        .unwrap()
        .json()
        .unwrap();

    assert_eq!(res, format!("{}", &second_microblock.block_hash()));

    sleep_ms(5_000);

    let path = format!("{}/v2/info", &http_origin);
    let mut iter_count = 0;
    let tip_info = loop {
        let tip_info = client
            .get(&path)
            .send()
            .unwrap()
            .json::<RPCPeerInfoData>()
            .unwrap();
        eprintln!("{:#?}", tip_info);
        if tip_info.unanchored_tip == StacksBlockId([0; 32]) {
            iter_count += 1;
            assert!(
                iter_count < 10,
                "Hit retry count while waiting for net module to process pushed microblock"
            );
            sleep_ms(5_000);
            continue;
        } else {
            break tip_info;
        }
    };

    assert!(tip_info.stacks_tip_height >= 3);
    let stacks_tip = tip_info.stacks_tip;
    let stacks_tip_consensus_hash = tip_info.stacks_tip_consensus_hash;
    let stacks_id_tip =
        StacksBlockHeader::make_index_block_hash(&stacks_tip_consensus_hash, &stacks_tip);

    // todo - pipe in the PoxSyncWatchdog to the RunLoop struct to avoid flakiness here
    // wait at least two p2p refreshes so it can produce the microblock
    for i in 0..30 {
        info!(
            "wait {} more seconds for microblock miner to find our transaction...",
            30 - i
        );
        sleep_ms(1000);
    }

    // check event observer for new microblock event (expect 4)
    let mut microblock_events = test_observer::get_microblocks();
    assert_eq!(microblock_events.len(), 4);
    // this microblock should correspond to `second_microblock`
    let microblock = microblock_events.pop().unwrap();
    let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
    assert_eq!(transactions.len(), 1);
    let tx_sequence = transactions[0]
        .get("microblock_sequence")
        .unwrap()
        .as_u64()
        .unwrap();
    assert_eq!(tx_sequence, 1);
    let microblock_hash = transactions[0]
        .get("microblock_hash")
        .unwrap()
        .as_str()
        .unwrap();
    assert_eq!(
        microblock_hash[2..],
        format!("{}", second_microblock.header.block_hash())
    );
    let microblock_associated_hash = microblock
        .get("parent_index_block_hash")
        .unwrap()
        .as_str()
        .unwrap();
    let index_block_hash_bytes = hex_bytes(&microblock_associated_hash[2..]).unwrap();
    assert_eq!(
        StacksBlockId::from_vec(&index_block_hash_bytes),
        Some(stacks_id_tip)
    );
    // make sure we have stats for the burn block
    let _burn_block_hash = microblock.get("burn_block_hash").unwrap().as_str().unwrap();
    let _burn_block_height = microblock
        .get("burn_block_height")
        .unwrap()
        .as_u64()
        .unwrap();
    let _burn_block_timestamp = microblock
        .get("burn_block_timestamp")
        .unwrap()
        .as_u64()
        .unwrap();

    // this microblock should correspond to the first microblock that was posted
    let microblock = microblock_events.pop().unwrap();
    let transactions = microblock.get("transactions").unwrap().as_array().unwrap();
    assert_eq!(transactions.len(), 1);
    let tx_sequence = transactions[0]
        .get("microblock_sequence")
        .unwrap()
        .as_u64()
        .unwrap();
    assert_eq!(tx_sequence, 0);

    // check mempool tx events
    let memtx_events = test_observer::get_memtxs();
    assert_eq!(memtx_events.len(), 1);
    assert_eq!(&memtx_events[0], &format!("0x{}", &bytes_to_hex(&tx)));

    // let's make sure the returned blocks all point at each other.
    let blocks_observed = test_observer::get_blocks();
    // we at least mined 5 blocks
    assert!(
        blocks_observed.len() >= 3,
        "Blocks observed {} should be >= 3",
        blocks_observed.len()
    );
    assert_eq!(blocks_observed.len() as u64, tip_info.stacks_tip_height);

    let burn_blocks_observed = test_observer::get_burn_blocks();
    let burn_blocks_with_burns: Vec<_> = burn_blocks_observed
        .into_iter()
        .filter(|block| block.get("burn_amount").unwrap().as_u64().unwrap() > 0)
        .collect();
    assert!(
        burn_blocks_with_burns.len() >= 3,
        "Burn block sortitions {} should be >= 3",
        burn_blocks_with_burns.len()
    );
    for burn_block in burn_blocks_with_burns {
        eprintln!("{}", burn_block);
    }

    let mut prior = None;
    for block in blocks_observed.iter() {
        let parent_index_hash = block
            .get("parent_index_block_hash")
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();
        let my_index_hash = block
            .get("index_block_hash")
            .unwrap()
            .as_str()
            .unwrap()
            .to_string();
        if let Some(ref previous_index_hash) = prior {
            assert_eq!(&parent_index_hash, previous_index_hash);
        }

        // make sure we have a burn_block_hash, burn_block_height and miner_txid

        let _burn_block_hash = block.get("burn_block_hash").unwrap().as_str().unwrap();

        let _burn_block_height = block.get("burn_block_height").unwrap().as_u64().unwrap();

        let _miner_txid = block.get("miner_txid").unwrap().as_str().unwrap();

        // make sure we have stats for the previous burn block
        let _parent_burn_block_hash = block
            .get("parent_burn_block_hash")
            .unwrap()
            .as_str()
            .unwrap();

        let _parent_burn_block_height = block
            .get("parent_burn_block_height")
            .unwrap()
            .as_u64()
            .unwrap();

        let _parent_burn_block_timestamp = block
            .get("parent_burn_block_timestamp")
            .unwrap()
            .as_u64()
            .unwrap();

        prior = Some(my_index_hash);
    }

    // we can query unconfirmed state from the microblock we announced
    let path = format!(
        "{}/v2/accounts/{}?proof=0&tip={}",
        &http_origin, &spender_addr, &tip_info.unanchored_tip
    );

    eprintln!("{:?}", &path);

    let mut iter_count = 0;
    let res = loop {
        let http_resp = client.get(&path).send().unwrap();

        info!("{:?}", http_resp);

        match http_resp.json::<AccountEntryResponse>() {
            Ok(x) => break x,
            Err(e) => {
                warn!("Failed to query {}; will try again. Err = {:?}", &path, e);
                iter_count += 1;
                assert!(iter_count < 10, "Retry limit reached querying account");
                sleep_ms(1000);
                continue;
            }
        };
    };

    info!("Account Response = {:#?}", res);
    assert_eq!(res.nonce, 2);
    assert_eq!(u128::from_str_radix(&res.balance[2..], 16).unwrap(), 96300);

    // limited by chaining
    for next_nonce in 2..5 {
        // verify that the microblock miner can automatically pick up transactions
        debug!(
            "Try to send unconfirmed tx from {} to {}",
            &spender_addr, &recipient
        );
        let unconfirmed_tx_bytes = make_stacks_transfer_mblock_only(
            &spender_sk,
            next_nonce,
            1000,
            &recipient.into(),
            1000,
        );

        let path = format!("{}/v2/transactions", &http_origin);
        let res = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(unconfirmed_tx_bytes.clone())
            .send()
            .unwrap();
        eprintln!("{:#?}", res);
        if res.status().is_success() {
            let res: String = res.json().unwrap();
            assert_eq!(
                res,
                StacksTransaction::consensus_deserialize(&mut &unconfirmed_tx_bytes[..])
                    .unwrap()
                    .txid()
                    .to_string()
            );
        } else {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // wait at least two p2p refreshes
        // so it can produce the microblock
        for i in 0..30 {
            debug!(
                "wait {} more seconds for microblock miner to find our transaction...",
                30 - i
            );
            sleep_ms(1000);
        }

        // we can query _new_ unconfirmed state from the microblock we announced
        let path = format!(
            "{}/v2/accounts/{}?proof=0&tip={}",
            &http_origin, &spender_addr, &tip_info.unanchored_tip
        );

        let res_text = client.get(&path).send().unwrap().text().unwrap();

        eprintln!("text of {}\n{}", &path, &res_text);

        let res = client
            .get(&path)
            .send()
            .unwrap()
            .json::<AccountEntryResponse>()
            .unwrap();
        eprintln!("{:?}", &path);
        eprintln!("{:#?}", res);

        // advanced!
        assert_eq!(res.nonce, next_nonce + 1);
        assert_eq!(
            u128::from_str_radix(&res.balance[2..], 16).unwrap(),
            (96300 - 2000 * (next_nonce - 1)) as u128
        );
    }

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn size_check_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // used to specify how long to wait in between blocks.
    //   we could _probably_ add a hook to the neon node that
    //   would remove some of the need for this
    let mut giant_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..(1024 * 1024 + 500) {
        giant_contract.push_str(" ");
    }

    let spender_sks: Vec<_> = (0..10)
        .into_iter()
        .map(|_| StacksPrivateKey::new())
        .collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();
    // make a bunch of txs that will only fit one per block.
    let txs: Vec<_> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            if ix % 2 == 0 {
                make_contract_publish(spender_sk, 0, 1049230, "large-0", &giant_contract)
            } else {
                let tx = make_contract_publish_microblock_only(
                    spender_sk,
                    0,
                    1049230,
                    "large-0",
                    &giant_contract,
                );
                let parsed_tx = StacksTransaction::consensus_deserialize(&mut &tx[..]).unwrap();
                debug!("Mine transaction {} in a microblock", &parsed_tx.txid());
                tx
            }
        })
        .collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 1049230,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 5000;
    conf.node.microblock_frequency = 1000;

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);
    // and our potential spenders:

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 1049230);
    }

    for tx in txs.iter() {
        // okay, let's push a bunch of transactions that can only fit one per block!
        submit_tx(&http_origin, tx);
    }

    sleep_ms(75_000);

    // now let's mine a couple blocks, and then check the sender's nonce.
    //  at the end of mining three blocks, there should be _two_ transactions from the microblock
    //  only set that got mined (since the block before this one was empty, a microblock can
    //  be added),
    //  and _two_ transactions from the two anchor blocks that got mined (and processed)
    //
    // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // this one will contain the sortition from above anchor block,
    //    which *should* have also confirmed the microblock.
    sleep_ms(75_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's figure out how many micro-only and anchor-only txs got accepted
    //   by examining our account nonces:
    let mut micro_block_txs = 0;
    let mut anchor_block_txs = 0;
    for (ix, spender_addr) in spender_addrs.iter().enumerate() {
        let res = get_account(&http_origin, &spender_addr);
        if res.nonce == 1 {
            if ix % 2 == 0 {
                anchor_block_txs += 1;
            } else {
                micro_block_txs += 1;
            }
        } else if res.nonce != 0 {
            panic!("Spender address nonce incremented past 1");
        }

        debug!("Spender {},{}: {:?}", ix, &spender_addr, &res);
    }

    eprintln!(
        "anchor_block_txs: {}, micro_block_txs: {}",
        anchor_block_txs, micro_block_txs
    );

    assert_eq!(anchor_block_txs, 2);
    assert_eq!(micro_block_txs, 2);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

// if a microblock consumes the majority of the block budget, then _only_ a microblock will be
// mined for an epoch.
#[test]
#[ignore]
fn size_overflow_unconfirmed_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // stuff a gigantic contract into the anchored block
    let mut giant_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..(1024 * 1024 + 500) {
        giant_contract.push_str(" ");
    }

    // small-sized contracts for microblocks
    let mut small_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..(1024 * 1024 + 500) {
        small_contract.push_str(" ");
    }

    let spender_sks: Vec<_> = (0..5)
        .into_iter()
        .map(|_| StacksPrivateKey::new())
        .collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let txs: Vec<Vec<_>> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            if ix % 2 == 0 {
                // almost fills a whole block
                vec![make_contract_publish(
                    spender_sk,
                    0,
                    1100000,
                    "large-0",
                    &giant_contract,
                )]
            } else {
                let mut ret = vec![];
                for i in 0..25 {
                    let tx = make_contract_publish_microblock_only(
                        spender_sk,
                        i as u64,
                        1100000,
                        &format!("small-{}", i),
                        &small_contract,
                    );
                    ret.push(tx);
                }
                ret
            }
        })
        .collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 10492300000,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 5_000;
    conf.node.microblock_frequency = 5_000;

    test_observer::spawn();
    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let microblocks_processed = run_loop.get_microblocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);
    // and our potential spenders:

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 10492300000);
    }

    for tx_batch in txs.iter() {
        for tx in tx_batch.iter() {
            // okay, let's push a bunch of transactions that can only fit one per block!
            submit_tx(&http_origin, tx);
        }
    }

    while wait_for_microblocks(&microblocks_processed, 30) {
        info!("Waiting for microblocks to no longer be processed");
    }

    // now let's mine a couple blocks, and then check the sender's nonce.
    //  at the end of mining three blocks, there should be _two_ transactions from the microblock
    //  only set that got mined (since the block before this one was empty, a microblock can
    //  be added),
    //  and _two_ transactions from the two anchor blocks that got mined (and processed)
    //
    // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // this one will contain the sortition from above anchor block,
    //    which *should* have also confirmed the microblock.

    while wait_for_microblocks(&microblocks_processed, 30) {
        info!("Waiting for microblocks to no longer be processed");
    }

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 3);

    let mut max_big_txs_per_block = 0;
    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_per_block = 0;
    let mut total_big_txs_per_microblock = 0;

    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        eprintln!("{}", transactions.len());

        let mut num_big_anchored_txs = 0;
        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(tsc) = parsed.payload {
                if tsc.name.to_string().find("large-").is_some() {
                    num_big_anchored_txs += 1;
                    total_big_txs_per_block += 1;
                } else if tsc.name.to_string().find("small-").is_some() {
                    num_big_microblock_txs += 1;
                    total_big_txs_per_microblock += 1;
                }
            }
        }

        if num_big_anchored_txs > max_big_txs_per_block {
            max_big_txs_per_block = num_big_anchored_txs;
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    eprintln!(
        "max_big_txs_per_microblock: {}, max_big_txs_per_block: {}, total_big_txs_per_block: {}, total_big_txs_per_microblock: {}",
        max_big_txs_per_microblock, max_big_txs_per_block, total_big_txs_per_block, total_big_txs_per_microblock
    );

    assert!(max_big_txs_per_block > 0);
    assert!(max_big_txs_per_microblock > 0);
    assert!(total_big_txs_per_block > 0);
    assert!(total_big_txs_per_microblock > 0);

    // can't have too many
    assert!(max_big_txs_per_microblock <= 3);
    assert!(max_big_txs_per_block <= 1);

    // NOTE: last-mined blocks aren't counted by the observer
    assert!(total_big_txs_per_block <= 2);
    assert!(total_big_txs_per_microblock <= 3);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

// mine a stream of microblocks, and verify that the miner won't let us overflow the size
#[test]
#[ignore]
fn size_overflow_unconfirmed_stream_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut small_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..((1024 * 1024 + 500) / 3) {
        small_contract.push_str(" ");
    }

    let spender_sks: Vec<_> = (0..20)
        .into_iter()
        .map(|_| StacksPrivateKey::new())
        .collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let txs: Vec<Vec<_>> = spender_sks
        .iter()
        .map(|spender_sk| {
            let mut ret = vec![];
            for i in 0..1 {
                let tx = make_contract_publish_microblock_only(
                    spender_sk,
                    i as u64,
                    600000,
                    &format!("small-{}", i),
                    &small_contract,
                );
                ret.push(tx);
            }
            ret
        })
        .collect();

    let flat_txs: Vec<_> = txs.iter().flat_map(|a| a.clone()).collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 10492300000,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 1000;
    conf.node.microblock_frequency = 1000;
    conf.node.max_microblocks = 65536;
    conf.burnchain.max_rbf = 1000000;

    test_observer::spawn();
    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let microblocks_processed = run_loop.get_microblocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 10492300000);
    }

    let mut ctr = 0;
    while ctr < flat_txs.len() {
        submit_tx(&http_origin, &flat_txs[ctr]);
        if !wait_for_microblocks(&microblocks_processed, 60) {
            break;
        }
        ctr += 1;
    }

    // should be able to fit 5 transactions in, in 5 microblocks
    assert_eq!(ctr, 5);
    sleep_ms(5_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    eprintln!("First confirmed microblock stream!");

    microblocks_processed.store(0, Ordering::SeqCst);

    while ctr < flat_txs.len() {
        submit_tx(&http_origin, &flat_txs[ctr]);
        if !wait_for_microblocks(&microblocks_processed, 60) {
            break;
        }
        ctr += 1;
    }

    // should be able to fit 5 more transactions in, in 5 microblocks
    assert_eq!(ctr, 10);
    sleep_ms(5_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    eprintln!("Second confirmed microblock stream!");

    // confirm it
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 4);

    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_per_microblock = 0;

    // NOTE: this only counts the number of txs per stream, not in each microblock
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        eprintln!("{}", transactions.len());

        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(tsc) = parsed.payload {
                if tsc.name.to_string().find("small-").is_some() {
                    num_big_microblock_txs += 1;
                    total_big_txs_per_microblock += 1;
                }
            }
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    eprintln!(
        "max_big_txs_per_microblock: {}, total_big_txs_per_microblock: {}",
        max_big_txs_per_microblock, total_big_txs_per_microblock
    );

    assert_eq!(max_big_txs_per_microblock, 5);
    assert!(total_big_txs_per_microblock >= 10);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

// Mine a too-long microblock stream, and verify that the anchored block miner truncates it down to
// the longest prefix of the stream that can be mined.
#[test]
#[ignore]
fn size_overflow_unconfirmed_invalid_stream_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // create microblock streams that are too big
    env::set_var(core::FAULT_DISABLE_MICROBLOCKS_BYTES_CHECK, "1");
    env::set_var(core::FAULT_DISABLE_MICROBLOCKS_COST_CHECK, "1");

    let mut small_contract = "(define-public (f) (ok 1))".to_string();
    for _i in 0..((1024 * 1024 + 500) / 8) {
        small_contract.push_str(" ");
    }

    let spender_sks: Vec<_> = (0..25)
        .into_iter()
        .map(|_| StacksPrivateKey::new())
        .collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let txs: Vec<Vec<_>> = spender_sks
        .iter()
        .map(|spender_sk| {
            let mut ret = vec![];
            for i in 0..1 {
                let tx = make_contract_publish_microblock_only(
                    spender_sk,
                    i as u64,
                    1149230,
                    &format!("small-{}", i),
                    &small_contract,
                );
                ret.push(tx);
            }
            ret
        })
        .collect();

    let flat_txs: Vec<_> = txs.iter().fold(vec![], |mut acc, a| {
        acc.append(&mut a.clone());
        acc
    });

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 10492300000,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 5_000;
    conf.node.microblock_frequency = 1_000;
    conf.node.max_microblocks = 65536;
    conf.burnchain.max_rbf = 1000000;
    conf.block_limit = BLOCK_LIMIT_MAINNET.clone();

    test_observer::spawn();
    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let microblocks_processed = run_loop.get_microblocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 10492300000);
    }

    let mut ctr = 0;
    for _i in 0..6 {
        submit_tx(&http_origin, &flat_txs[ctr]);
        if !wait_for_microblocks(&microblocks_processed, 60) {
            break;
        }
        ctr += 1;
    }

    // confirm that we were able to use the fault-injection to *mine* 6 microblocks
    assert_eq!(ctr, 6);
    sleep_ms(5_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    eprintln!("First confirmed microblock stream!");

    // confirm it
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 3);

    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_per_microblock = 0;

    // NOTE: this only counts the number of txs per stream, not in each microblock
    for block in blocks {
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        eprintln!("{}", transactions.len());

        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::SmartContract(tsc) = parsed.payload {
                if tsc.name.to_string().find("small-").is_some() {
                    num_big_microblock_txs += 1;
                    total_big_txs_per_microblock += 1;
                }
            }
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    eprintln!(
        "max_big_txs_per_microblock: {}, total_big_txs_per_microblock: {}",
        max_big_txs_per_microblock, total_big_txs_per_microblock
    );

    assert_eq!(max_big_txs_per_microblock, 3);
    assert!(total_big_txs_per_microblock <= 6);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn runtime_overflow_unconfirmed_microblocks_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sks: Vec<_> = (0..4)
        .into_iter()
        .map(|_| StacksPrivateKey::new())
        .collect();
    let spender_addrs: Vec<PrincipalData> = spender_sks.iter().map(|x| to_addr(x).into()).collect();
    let spender_addrs_c32: Vec<StacksAddress> =
        spender_sks.iter().map(|x| to_addr(x).into()).collect();

    let txs: Vec<Vec<_>> = spender_sks
        .iter()
        .enumerate()
        .map(|(ix, spender_sk)| {
            if ix % 2 == 0 {
                // almost fills a whole block
                vec![make_contract_publish(
                    spender_sk,
                    0,
                    1049230,
                    &format!("large-{}", ix),
                    &format!("
                        ;; a single one of these transactions consumes over half the runtime budget
                        (define-constant BUFF_TO_BYTE (list 
                           0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07 0x08 0x09 0x0a 0x0b 0x0c 0x0d 0x0e 0x0f
                           0x10 0x11 0x12 0x13 0x14 0x15 0x16 0x17 0x18 0x19 0x1a 0x1b 0x1c 0x1d 0x1e 0x1f
                           0x20 0x21 0x22 0x23 0x24 0x25 0x26 0x27 0x28 0x29 0x2a 0x2b 0x2c 0x2d 0x2e 0x2f
                           0x30 0x31 0x32 0x33 0x34 0x35 0x36 0x37 0x38 0x39 0x3a 0x3b 0x3c 0x3d 0x3e 0x3f
                           0x40 0x41 0x42 0x43 0x44 0x45 0x46 0x47 0x48 0x49 0x4a 0x4b 0x4c 0x4d 0x4e 0x4f
                           0x50 0x51 0x52 0x53 0x54 0x55 0x56 0x57 0x58 0x59 0x5a 0x5b 0x5c 0x5d 0x5e 0x5f
                           0x60 0x61 0x62 0x63 0x64 0x65 0x66 0x67 0x68 0x69 0x6a 0x6b 0x6c 0x6d 0x6e 0x6f
                           0x70 0x71 0x72 0x73 0x74 0x75 0x76 0x77 0x78 0x79 0x7a 0x7b 0x7c 0x7d 0x7e 0x7f
                           0x80 0x81 0x82 0x83 0x84 0x85 0x86 0x87 0x88 0x89 0x8a 0x8b 0x8c 0x8d 0x8e 0x8f
                           0x90 0x91 0x92 0x93 0x94 0x95 0x96 0x97 0x98 0x99 0x9a 0x9b 0x9c 0x9d 0x9e 0x9f
                           0xa0 0xa1 0xa2 0xa3 0xa4 0xa5 0xa6 0xa7 0xa8 0xa9 0xaa 0xab 0xac 0xad 0xae 0xaf
                           0xb0 0xb1 0xb2 0xb3 0xb4 0xb5 0xb6 0xb7 0xb8 0xb9 0xba 0xbb 0xbc 0xbd 0xbe 0xbf
                           0xc0 0xc1 0xc2 0xc3 0xc4 0xc5 0xc6 0xc7 0xc8 0xc9 0xca 0xcb 0xcc 0xcd 0xce 0xcf
                           0xd0 0xd1 0xd2 0xd3 0xd4 0xd5 0xd6 0xd7 0xd8 0xd9 0xda 0xdb 0xdc 0xdd 0xde 0xdf
                           0xe0 0xe1 0xe2 0xe3 0xe4 0xe5 0xe6 0xe7 0xe8 0xe9 0xea 0xeb 0xec 0xed 0xee 0xef
                           0xf0 0xf1 0xf2 0xf3 0xf4 0xf5 0xf6 0xf7 0xf8 0xf9 0xfa 0xfb 0xfc 0xfd 0xfe 0xff
                        ))
                        (define-private (crash-me-folder (input (buff 1)) (ctr uint))
                            (begin
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (unwrap-panic (index-of BUFF_TO_BYTE input))
                                (+ u1 ctr)
                            )
                        )
                        (define-public (crash-me (name (string-ascii 128)))
                            (begin
                                (fold crash-me-folder BUFF_TO_BYTE u0)
                                (print name)
                                (ok u0)
                            )
                        )
                        (begin
                            (crash-me \"{}\"))
                        ",
                        &format!("large-contract-{}-{}", &spender_addrs_c32[ix], &ix)
                    )
                )]
            } else {
                let mut ret = vec![];
                for i in 0..1 {
                    let tx = make_contract_publish_microblock_only(
                        spender_sk,
                        i as u64,
                        210000,
                        &format!("small-{}-{}", ix, i),
                        &format!("
                            ;; a single one of these transactions consumes over half the runtime budget
                            (define-constant BUFF_TO_BYTE (list 
                               0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07 0x08 0x09 0x0a 0x0b 0x0c 0x0d 0x0e 0x0f
                               0x10 0x11 0x12 0x13 0x14 0x15 0x16 0x17 0x18 0x19 0x1a 0x1b 0x1c 0x1d 0x1e 0x1f
                               0x20 0x21 0x22 0x23 0x24 0x25 0x26 0x27 0x28 0x29 0x2a 0x2b 0x2c 0x2d 0x2e 0x2f
                               0x30 0x31 0x32 0x33 0x34 0x35 0x36 0x37 0x38 0x39 0x3a 0x3b 0x3c 0x3d 0x3e 0x3f
                               0x40 0x41 0x42 0x43 0x44 0x45 0x46 0x47 0x48 0x49 0x4a 0x4b 0x4c 0x4d 0x4e 0x4f
                               0x50 0x51 0x52 0x53 0x54 0x55 0x56 0x57 0x58 0x59 0x5a 0x5b 0x5c 0x5d 0x5e 0x5f
                               0x60 0x61 0x62 0x63 0x64 0x65 0x66 0x67 0x68 0x69 0x6a 0x6b 0x6c 0x6d 0x6e 0x6f
                               0x70 0x71 0x72 0x73 0x74 0x75 0x76 0x77 0x78 0x79 0x7a 0x7b 0x7c 0x7d 0x7e 0x7f
                               0x80 0x81 0x82 0x83 0x84 0x85 0x86 0x87 0x88 0x89 0x8a 0x8b 0x8c 0x8d 0x8e 0x8f
                               0x90 0x91 0x92 0x93 0x94 0x95 0x96 0x97 0x98 0x99 0x9a 0x9b 0x9c 0x9d 0x9e 0x9f
                               0xa0 0xa1 0xa2 0xa3 0xa4 0xa5 0xa6 0xa7 0xa8 0xa9 0xaa 0xab 0xac 0xad 0xae 0xaf
                               0xb0 0xb1 0xb2 0xb3 0xb4 0xb5 0xb6 0xb7 0xb8 0xb9 0xba 0xbb 0xbc 0xbd 0xbe 0xbf
                               0xc0 0xc1 0xc2 0xc3 0xc4 0xc5 0xc6 0xc7 0xc8 0xc9 0xca 0xcb 0xcc 0xcd 0xce 0xcf
                               0xd0 0xd1 0xd2 0xd3 0xd4 0xd5 0xd6 0xd7 0xd8 0xd9 0xda 0xdb 0xdc 0xdd 0xde 0xdf
                               0xe0 0xe1 0xe2 0xe3 0xe4 0xe5 0xe6 0xe7 0xe8 0xe9 0xea 0xeb 0xec 0xed 0xee 0xef
                               0xf0 0xf1 0xf2 0xf3 0xf4 0xf5 0xf6 0xf7 0xf8 0xf9 0xfa 0xfb 0xfc 0xfd 0xfe 0xff
                            ))
                            (define-private (crash-me-folder (input (buff 1)) (ctr uint))
                                (begin
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (unwrap-panic (index-of BUFF_TO_BYTE input))
                                    (+ u1 ctr)
                                )
                            )
                            (define-public (crash-me (name (string-ascii 128)))
                                (begin
                                    (fold crash-me-folder BUFF_TO_BYTE u0)
                                    (print name)
                                    (ok u0)
                                )
                            )
                            (begin
                                (crash-me \"{}\"))
                            ", &format!("small-contract-{}-{}-{}", &spender_addrs_c32[ix], &ix, i))
                    );
                    ret.push(tx);
                }
                ret
            }
        })
        .collect();

    let (mut conf, miner_account) = neon_integration_test_conf();

    for spender_addr in spender_addrs.iter() {
        conf.initial_balances.push(InitialBalance {
            address: spender_addr.clone(),
            amount: 1049230,
        });
    }

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 0;
    conf.node.microblock_frequency = 15000;
    conf.block_limit = BLOCK_LIMIT_MAINNET.clone();

    test_observer::spawn();
    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);
    // and our potential spenders:

    for spender_addr in spender_addrs.iter() {
        let account = get_account(&http_origin, &spender_addr);
        assert_eq!(account.nonce, 0);
        assert_eq!(account.balance, 1049230);
    }

    for tx_batch in txs.iter() {
        for tx in tx_batch.iter() {
            // okay, let's push a bunch of transactions that can only fit one per block!
            submit_tx(&http_origin, tx);
        }
    }

    debug!("Wait for 1st microblock to be mined");
    sleep_ms(150_000);

    // now let's mine a couple blocks, and then check the sender's nonce.
    //  at the end of mining three blocks, there should be _two_ transactions from the microblock
    //  only set that got mined (since the block before this one was empty, a microblock can
    //  be added),
    //  and _two_ transactions from the two anchor blocks that got mined (and processed)
    //
    // this one wakes up our node, so that it'll mine a microblock _and_ an anchor block.
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // this one will contain the sortition from above anchor block,
    //    which *should* have also confirmed the microblock.

    debug!("Wait for 2nd microblock to be mined");
    sleep_ms(150_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    debug!("Wait for 3nd microblock to be mined");
    sleep_ms(150_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let blocks = test_observer::get_blocks();
    assert_eq!(blocks.len(), 4);

    let mut max_big_txs_per_block = 0;
    let mut max_big_txs_per_microblock = 0;
    let mut total_big_txs_per_block = 0;
    let mut total_big_txs_per_microblock = 0;

    for block in blocks {
        eprintln!("block {:?}", &block);
        let transactions = block.get("transactions").unwrap().as_array().unwrap();

        let mut num_big_anchored_txs = 0;
        let mut num_big_microblock_txs = 0;

        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            eprintln!("tx: {:?}", &parsed);
            if let TransactionPayload::SmartContract(tsc) = parsed.payload {
                if tsc.name.to_string().find("large-").is_some() {
                    num_big_anchored_txs += 1;
                    total_big_txs_per_block += 1;
                } else if tsc.name.to_string().find("small-").is_some() {
                    num_big_microblock_txs += 1;
                    total_big_txs_per_microblock += 1;
                }
            }
        }

        if num_big_anchored_txs > max_big_txs_per_block {
            max_big_txs_per_block = num_big_anchored_txs;
        }
        if num_big_microblock_txs > max_big_txs_per_microblock {
            max_big_txs_per_microblock = num_big_microblock_txs;
        }
    }

    debug!(
        "max_big_txs_per_microblock: {}, max_big_txs_per_block: {}",
        max_big_txs_per_microblock, max_big_txs_per_block
    );
    debug!(
        "total_big_txs_per_microblock: {}, total_big_txs_per_block: {}",
        total_big_txs_per_microblock, total_big_txs_per_block
    );

    // at most one big tx per block and at most one big tx per stream, always.
    assert!(max_big_txs_per_microblock == 1);
    assert!(max_big_txs_per_block == 1);

    // if the mblock stream has a big tx, the anchored block won't (and vice versa)
    assert!(total_big_txs_per_block == 1); // last block didn't get counted by the observer
    assert!(total_big_txs_per_microblock == 2);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn block_replay_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::from_hex(SK_1).unwrap();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    let (mut conf, miner_account) = neon_integration_test_conf();

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: 100300,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 30000;
    conf.node.microblock_frequency = 5_000;

    test_observer::spawn();

    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:

    info!("Miner account: {}", miner_account);
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    // and our spender
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, 100300);
    assert_eq!(account.nonce, 0);

    let recipient = StacksAddress::from_string(ADDR_4).unwrap();
    let tx = make_stacks_transfer(&spender_sk, 0, 1000, &recipient.into(), 1000);
    submit_tx(&http_origin, &tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // try and push the mined block back at the node lots of times
    let (tip_consensus_hash, tip_block) = get_tip_anchored_block(&conf);
    let mut tip_block_bytes = vec![];
    tip_block.consensus_serialize(&mut tip_block_bytes).unwrap();

    for i in 0..1024 {
        let path = format!("{}/v2/blocks/upload/{}", &http_origin, &tip_consensus_hash);
        let res_text = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(tip_block_bytes.clone())
            .send()
            .unwrap()
            .text()
            .unwrap();

        eprintln!("{}: text of {}\n{}", i, &path, &res_text);
    }

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn cost_voting_integration() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // let's make `<` free...
    let cost_definer_src = "
    (define-read-only (cost-definition-le (size uint))
       {
         runtime: u0, write_length: u0, write_count: u0, read_count: u0, read_length: u0
       })
    ";

    // the contract that we'll test the costs of
    let caller_src = "
    (define-public (execute-2 (a uint))
       (ok (< a a)))
    ";

    let power_vote_src = "
    (define-public (propose-vote-confirm)
      (let
        ((proposal-id (unwrap-panic (contract-call? 'ST000000000000000000002AMW42H.cost-voting submit-proposal
                            'ST000000000000000000002AMW42H.costs \"cost_le\"
                            .cost-definer \"cost-definition-le\")))
         (vote-amount (* u9000000000 u1000000)))
        (try! (contract-call? 'ST000000000000000000002AMW42H.cost-voting vote-proposal proposal-id vote-amount))
        (try! (contract-call? 'ST000000000000000000002AMW42H.cost-voting confirm-votes proposal-id))
        (ok proposal-id)))
    ";

    let spender_sk = StacksPrivateKey::new();
    let spender_addr = to_addr(&spender_sk);
    let spender_princ: PrincipalData = spender_addr.into();

    let (mut conf, miner_account) = neon_integration_test_conf();

    test_observer::spawn();

    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let spender_bal = 10_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);

    conf.initial_balances.push(InitialBalance {
        address: spender_princ.clone(),
        amount: spender_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // let's query the miner's account nonce:
    let res = get_account(&http_origin, &miner_account);
    assert_eq!(res.balance, 0);
    assert_eq!(res.nonce, 1);

    // and our spender:
    let res = get_account(&http_origin, &spender_princ);
    assert_eq!(res.balance, spender_bal as u128);
    assert_eq!(res.nonce, 0);

    let transactions = vec![
        make_contract_publish(&spender_sk, 0, 1000, "cost-definer", cost_definer_src),
        make_contract_publish(&spender_sk, 1, 1000, "caller", caller_src),
        make_contract_publish(&spender_sk, 2, 1000, "voter", power_vote_src),
    ];

    for tx in transactions.into_iter() {
        submit_tx(&http_origin, &tx);
    }

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let vote_tx = make_contract_call(
        &spender_sk,
        3,
        1000,
        &spender_addr,
        "voter",
        "propose-vote-confirm",
        &[],
    );

    let call_le_tx = make_contract_call(
        &spender_sk,
        4,
        1000,
        &spender_addr,
        "caller",
        "execute-2",
        &[Value::UInt(1)],
    );

    submit_tx(&http_origin, &vote_tx);
    submit_tx(&http_origin, &call_le_tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    let mut exec_cost = ExecutionCost::zero();
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "execute-2" {
                exec_cost =
                    serde_json::from_value(tx.get("execution_cost").cloned().unwrap()).unwrap();
            } else if contract_call.function_name.as_str() == "propose-vote-confirm" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = <Value as ClarityDeserializable<Value>>::deserialize(&raw_result[2..]);
                assert_eq!(parsed.to_string(), "(ok u0)");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    // try to confirm the passed vote (this will fail)
    let confirm_proposal = make_contract_call(
        &spender_sk,
        5,
        1000,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "cost-voting",
        "confirm-miners",
        &[Value::UInt(0)],
    );

    submit_tx(&http_origin, &confirm_proposal);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "confirm-miners" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = <Value as ClarityDeserializable<Value>>::deserialize(&raw_result[2..]);
                assert_eq!(parsed.to_string(), "(err 13)");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    for _i in 0..58 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    }

    // confirm the passed vote
    let confirm_proposal = make_contract_call(
        &spender_sk,
        6,
        1000,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "cost-voting",
        "confirm-miners",
        &[Value::UInt(0)],
    );

    submit_tx(&http_origin, &confirm_proposal);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();
    eprintln!("{}", transactions.len());
    let mut tested = false;
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "confirm-miners" {
                let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                let parsed = <Value as ClarityDeserializable<Value>>::deserialize(&raw_result[2..]);
                assert_eq!(parsed.to_string(), "(ok true)");
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    let call_le_tx = make_contract_call(
        &spender_sk,
        7,
        1000,
        &spender_addr,
        "caller",
        "execute-2",
        &[Value::UInt(1)],
    );

    submit_tx(&http_origin, &call_le_tx);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    // clear and mine another burnchain block, so that the new winner is seen by the observer
    //   (the observer is logically "one block behind" the miner
    test_observer::clear();
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut blocks = test_observer::get_blocks();
    // should have produced 1 new block
    assert_eq!(blocks.len(), 1);
    let block = blocks.pop().unwrap();
    let transactions = block.get("transactions").unwrap().as_array().unwrap();

    let mut tested = false;
    let mut new_exec_cost = ExecutionCost::max_value();
    for tx in transactions.iter() {
        let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
        if raw_tx == "0x00" {
            continue;
        }
        let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
        let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
        if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
            eprintln!("{}", contract_call.function_name.as_str());
            if contract_call.function_name.as_str() == "execute-2" {
                new_exec_cost =
                    serde_json::from_value(tx.get("execution_cost").cloned().unwrap()).unwrap();
                tested = true;
            }
        }
    }
    assert!(tested, "Should have found a contract call tx");

    assert!(exec_cost.exceeds(&new_exec_cost));

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn near_full_block_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    // cost = {
    //   "write_length":350981,
    //   "write_count":932,
    //   "read_length":3711941,
    //   "read_count":3721,
    //   "runtime":4960871000
    // }
    let max_contract_src = format!(
        "(define-public (f) (begin {} (ok 1))) (begin (f))",
        (0..310)
            .map(|_| format!(
                "(unwrap! (contract-call? '{} submit-proposal '{} \"cost-old\" '{} \"cost-new\") (err 1))",
                boot_code_id("cost-voting", false),
                boot_code_id("costs", false),
                boot_code_id("costs", false),
            ))
            .collect::<Vec<String>>()
            .join(" ")
    );

    let spender_sk = StacksPrivateKey::new();
    let addr = to_addr(&spender_sk);

    let tx = make_contract_publish(&spender_sk, 0, 58450, "max", &max_contract_src);

    let (mut conf, miner_account) = neon_integration_test_conf();

    // Set block limit
    conf.block_limit = BLOCK_LIMIT_MAINNET;

    conf.initial_balances.push(InitialBalance {
        address: addr.clone().into(),
        amount: 10000000,
    });

    conf.node.mine_microblocks = true;
    conf.node.wait_time_for_microblocks = 30000;
    conf.node.microblock_frequency = 1000;

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut btc_regtest_controller = BitcoinRegtestController::new(conf.clone(), None);
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf);
    let blocks_processed = run_loop.get_blocks_processed_arc();

    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(None, 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.nonce, 1);
    assert_eq!(account.balance, 0);

    let account = get_account(&http_origin, &addr);
    assert_eq!(account.nonce, 0);
    assert_eq!(account.balance, 10000000);

    submit_tx(&http_origin, &tx);
    sleep_ms(60_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
    sleep_ms(60_000);

    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let res = get_account(&http_origin, &addr);
    assert_eq!(res.nonce, 1);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[test]
#[ignore]
fn pox_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let spender_sk = StacksPrivateKey::new();
    let spender_addr: PrincipalData = to_addr(&spender_sk).into();

    let spender_2_sk = StacksPrivateKey::new();
    let spender_2_addr: PrincipalData = to_addr(&spender_2_sk).into();

    let spender_3_sk = StacksPrivateKey::new();
    let spender_3_addr: PrincipalData = to_addr(&spender_3_sk).into();

    let pox_pubkey = Secp256k1PublicKey::from_hex(
        "02f006a09b59979e2cb8449f58076152af6b124aa29b948a3714b8d5f15aa94ede",
    )
    .unwrap();
    let pox_pubkey_hash = bytes_to_hex(
        &Hash160::from_node_public_key(&pox_pubkey)
            .to_bytes()
            .to_vec(),
    );

    let pox_2_pubkey = Secp256k1PublicKey::from_private(&StacksPrivateKey::new());
    let pox_2_pubkey_hash = bytes_to_hex(
        &Hash160::from_node_public_key(&pox_2_pubkey)
            .to_bytes()
            .to_vec(),
    );

    let pox_2_address = BitcoinAddress::from_bytes(
        BitcoinNetworkType::Testnet,
        BitcoinAddressType::PublicKeyHash,
        &Hash160::from_node_public_key(&pox_2_pubkey).to_bytes(),
    )
    .unwrap();

    let (mut conf, miner_account) = neon_integration_test_conf();

    test_observer::spawn();

    conf.events_observers.push(EventObserverConfig {
        endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
        events_keys: vec![EventKeyType::AnyEvent],
    });

    let first_bal = 6_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let second_bal = 2_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let third_bal = 2_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64);
    let stacked_bal = 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u128);

    conf.initial_balances.push(InitialBalance {
        address: spender_addr.clone(),
        amount: first_bal,
    });

    conf.initial_balances.push(InitialBalance {
        address: spender_2_addr.clone(),
        amount: second_bal,
    });

    conf.initial_balances.push(InitialBalance {
        address: spender_3_addr.clone(),
        amount: third_bal,
    });

    let mut btcd_controller = BitcoinCoreController::new(conf.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let mut burnchain_config = Burnchain::regtest(&conf.get_burn_db_path());

    // reward cycle length = 15, so 10 reward cycle slots + 5 prepare-phase burns
    let reward_cycle_len = 15;
    let prepare_phase_len = 5;
    let pox_constants = PoxConstants::new(
        reward_cycle_len,
        prepare_phase_len,
        4 * prepare_phase_len / 5,
        5,
        15,
        (16 * reward_cycle_len - 1).into(),
        (17 * reward_cycle_len).into(),
    );
    burnchain_config.pox_constants = pox_constants.clone();

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let sort_height = channel.get_sortitions_processed();

    // let's query the miner's account nonce:
    let account = get_account(&http_origin, &miner_account);
    assert_eq!(account.balance, 0);
    assert_eq!(account.nonce, 1);

    // and our potential spenders:
    let account = get_account(&http_origin, &spender_addr);
    assert_eq!(account.balance, first_bal as u128);
    assert_eq!(account.nonce, 0);

    let pox_info = get_pox_info(&http_origin);

    assert_eq!(
        &pox_info.contract_id,
        &format!("ST000000000000000000002AMW42H.pox")
    );
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.next_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 0);
    assert_eq!(pox_info.current_cycle.is_pox_active, false);
    assert_eq!(pox_info.next_cycle.stacked_ustx, 0);
    assert_eq!(pox_info.reward_slots as u32, pox_constants.reward_slots());
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 210);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 205);
    assert_eq!(pox_info.next_cycle.min_increment_ustx, 1250710410920);
    assert_eq!(
        pox_info.prepare_cycle_length as u32,
        pox_constants.prepare_length
    );
    assert_eq!(
        pox_info.rejection_fraction,
        pox_constants.pox_rejection_fraction
    );
    assert_eq!(pox_info.reward_cycle_id, 0);
    assert_eq!(pox_info.current_cycle.id, 0);
    assert_eq!(pox_info.next_cycle.id, 1);
    assert_eq!(
        pox_info.reward_cycle_length as u32,
        pox_constants.reward_cycle_length
    );
    assert_eq!(pox_info.total_liquid_supply_ustx, 10005683287360023);
    assert_eq!(pox_info.next_reward_cycle_in, 6);

    let tx = make_contract_call(
        &spender_sk,
        0,
        260,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked_bal),
            execute(&format!(
                "{{ hashbytes: 0x{}, version: 0x00 }}",
                pox_pubkey_hash
            ))
            .unwrap()
            .unwrap(),
            Value::UInt(sort_height as u128),
            Value::UInt(6),
        ],
    );

    // okay, let's push that stacking transaction!
    submit_tx(&http_origin, &tx);

    let mut sort_height = channel.get_sortitions_processed();
    eprintln!("Sort height: {}", sort_height);
    test_observer::clear();

    // now let's mine until the next reward cycle starts ...
    while sort_height < ((14 * pox_constants.reward_cycle_length) + 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {}", sort_height);
    }

    let pox_info = get_pox_info(&http_origin);

    assert_eq!(
        &pox_info.contract_id,
        &format!("ST000000000000000000002AMW42H.pox")
    );
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.next_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 1000000000000000);
    assert!(pox_info.pox_activation_threshold_ustx > 1500000000000000);
    assert_eq!(pox_info.current_cycle.is_pox_active, false);
    assert_eq!(pox_info.next_cycle.stacked_ustx, 1000000000000000);
    assert_eq!(pox_info.reward_slots as u32, pox_constants.reward_slots());
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 225);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 220);
    assert_eq!(
        pox_info.prepare_cycle_length as u32,
        pox_constants.prepare_length
    );
    assert_eq!(
        pox_info.rejection_fraction,
        pox_constants.pox_rejection_fraction
    );
    assert_eq!(pox_info.reward_cycle_id, 14);
    assert_eq!(pox_info.current_cycle.id, 14);
    assert_eq!(pox_info.next_cycle.id, 15);
    assert_eq!(
        pox_info.reward_cycle_length as u32,
        pox_constants.reward_cycle_length
    );
    assert_eq!(pox_info.next_reward_cycle_in, 14);

    let blocks_observed = test_observer::get_blocks();
    assert!(
        blocks_observed.len() >= 2,
        "Blocks observed {} should be >= 2",
        blocks_observed.len()
    );

    // look up the return value of our stacking operation...
    let mut tested = false;
    for block in blocks_observed.iter() {
        if tested {
            break;
        }
        let transactions = block.get("transactions").unwrap().as_array().unwrap();
        for tx in transactions.iter() {
            let raw_tx = tx.get("raw_tx").unwrap().as_str().unwrap();
            if raw_tx == "0x00" {
                continue;
            }
            let tx_bytes = hex_bytes(&raw_tx[2..]).unwrap();
            let parsed = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).unwrap();
            if let TransactionPayload::ContractCall(contract_call) = parsed.payload {
                eprintln!("{}", contract_call.function_name.as_str());
                if contract_call.function_name.as_str() == "stack-stx" {
                    let raw_result = tx.get("raw_result").unwrap().as_str().unwrap();
                    let parsed =
                        <Value as ClarityDeserializable<Value>>::deserialize(&raw_result[2..]);
                    // should unlock at height 300 (we're in reward cycle 13, lockup starts in reward cycle
                    // 14, and goes for 6 blocks, so we unlock in reward cycle 20, which with a reward
                    // cycle length of 15 blocks, is a burnchain height of 300)
                    assert_eq!(parsed.to_string(),
                               format!("(ok (tuple (lock-amount u1000000000000000) (stacker {}) (unlock-burn-height u300)))",
                                       &spender_addr));
                    tested = true;
                }
            }
        }
    }

    assert!(tested, "Should have observed stack-stx transaction");

    // let's stack with spender 2 and spender 3...

    // now let's have sender_2 and sender_3 stack to pox addr 2 in
    //  two different txs, and make sure that they sum together in the reward set.

    let tx = make_contract_call(
        &spender_2_sk,
        0,
        260,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked_bal / 2),
            execute(&format!(
                "{{ hashbytes: 0x{}, version: 0x00 }}",
                pox_2_pubkey_hash
            ))
            .unwrap()
            .unwrap(),
            Value::UInt(sort_height as u128),
            Value::UInt(6),
        ],
    );

    // okay, let's push that stacking transaction!
    submit_tx(&http_origin, &tx);

    let tx = make_contract_call(
        &spender_3_sk,
        0,
        260,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "pox",
        "stack-stx",
        &[
            Value::UInt(stacked_bal / 2),
            execute(&format!(
                "{{ hashbytes: 0x{}, version: 0x00 }}",
                pox_2_pubkey_hash
            ))
            .unwrap()
            .unwrap(),
            Value::UInt(sort_height as u128),
            Value::UInt(6),
        ],
    );

    submit_tx(&http_origin, &tx);

    // mine until the end of the current reward cycle.
    sort_height = channel.get_sortitions_processed();
    while sort_height < ((15 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {}", sort_height);
    }

    let pox_info = get_pox_info(&http_origin);

    assert_eq!(
        &pox_info.contract_id,
        &format!("ST000000000000000000002AMW42H.pox")
    );
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.next_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 1000000000000000);
    assert_eq!(pox_info.current_cycle.is_pox_active, false);
    assert_eq!(pox_info.next_cycle.stacked_ustx, 2000000000000000);
    assert_eq!(pox_info.reward_slots as u32, pox_constants.reward_slots());
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 225);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 220);
    assert_eq!(pox_info.next_cycle.blocks_until_prepare_phase, -4);
    assert_eq!(
        pox_info.prepare_cycle_length as u32,
        pox_constants.prepare_length
    );
    assert_eq!(
        pox_info.rejection_fraction,
        pox_constants.pox_rejection_fraction
    );
    assert_eq!(pox_info.reward_cycle_id, 14);
    assert_eq!(pox_info.current_cycle.id, 14);
    assert_eq!(pox_info.next_cycle.id, 15);
    assert_eq!(
        pox_info.reward_cycle_length as u32,
        pox_constants.reward_cycle_length
    );
    assert_eq!(pox_info.next_reward_cycle_in, 1);

    // we should have received _no_ Bitcoin commitments, because the pox participation threshold
    //   was not met!
    let utxos = btc_regtest_controller.get_all_utxos(&pox_pubkey);
    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        0,
        "Should have received no outputs during PoX reward cycle"
    );

    // let's test the reward information in the observer
    test_observer::clear();

    // before sunset
    // mine until the end of the next reward cycle,
    //   the participation threshold now should be met.
    while sort_height < ((16 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {}", sort_height);
    }

    let pox_info = get_pox_info(&http_origin);

    assert_eq!(
        &pox_info.contract_id,
        &format!("ST000000000000000000002AMW42H.pox")
    );
    assert_eq!(pox_info.first_burnchain_block_height, 0);
    assert_eq!(pox_info.current_cycle.min_threshold_ustx, 125080000000000);
    assert_eq!(pox_info.current_cycle.stacked_ustx, 2000000000000000);
    assert_eq!(pox_info.current_cycle.is_pox_active, true);
    assert_eq!(pox_info.next_cycle.reward_phase_start_block_height, 240);
    assert_eq!(pox_info.next_cycle.prepare_phase_start_block_height, 235);
    assert_eq!(pox_info.next_cycle.blocks_until_prepare_phase, -4);
    assert_eq!(pox_info.next_reward_cycle_in, 1);

    // we should have received _seven_ Bitcoin commitments, because our commitment was 7 * threshold
    let utxos = btc_regtest_controller.get_all_utxos(&pox_pubkey);

    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        7,
        "Should have received outputs during PoX reward cycle"
    );

    // we should have received _seven_ Bitcoin commitments to pox_2_pubkey, because our commitment was 7 * threshold
    //   note: that if the reward set "summing" isn't implemented, this recipient would only have received _6_ slots,
    //         because each `stack-stx` call only received enough to get 3 slot individually.
    let utxos = btc_regtest_controller.get_all_utxos(&pox_2_pubkey);

    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        7,
        "Should have received outputs during PoX reward cycle"
    );

    let burn_blocks = test_observer::get_burn_blocks();
    let mut recipient_slots: HashMap<String, u64> = HashMap::new();

    for block in burn_blocks.iter() {
        let reward_slot_holders = block
            .get("reward_slot_holders")
            .unwrap()
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap().to_string());
        for holder in reward_slot_holders {
            if let Some(current) = recipient_slots.get_mut(&holder) {
                *current += 1;
            } else {
                recipient_slots.insert(holder, 1);
            }
        }
    }

    let pox_1_address = BitcoinAddress::from_bytes(
        BitcoinNetworkType::Testnet,
        BitcoinAddressType::PublicKeyHash,
        &Hash160::from_node_public_key(&pox_pubkey).to_bytes(),
    )
    .unwrap();

    assert_eq!(recipient_slots.len(), 2);
    assert_eq!(
        recipient_slots.get(&pox_2_address.to_b58()).cloned(),
        Some(7u64)
    );
    assert_eq!(
        recipient_slots.get(&pox_1_address.to_b58()).cloned(),
        Some(7u64)
    );

    // get the canonical chain tip
    let path = format!("{}/v2/info", &http_origin);
    let tip_info = client
        .get(&path)
        .send()
        .unwrap()
        .json::<RPCPeerInfoData>()
        .unwrap();

    eprintln!("Stacks tip is now {}", tip_info.stacks_tip_height);
    assert_eq!(tip_info.stacks_tip_height, 36);

    // now let's mine into the sunset
    while sort_height < ((17 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {}", sort_height);
    }

    // get the canonical chain tip
    let path = format!("{}/v2/info", &http_origin);
    let tip_info = client
        .get(&path)
        .send()
        .unwrap()
        .json::<RPCPeerInfoData>()
        .unwrap();

    eprintln!("Stacks tip is now {}", tip_info.stacks_tip_height);
    assert_eq!(tip_info.stacks_tip_height, 51);

    let utxos = btc_regtest_controller.get_all_utxos(&pox_2_pubkey);

    // should receive more rewards during this cycle...
    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        14,
        "Should have received more outputs during the sunsetting PoX reward cycle"
    );

    // and after sunset
    while sort_height < ((18 * pox_constants.reward_cycle_length) - 1).into() {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sort_height = channel.get_sortitions_processed();
        eprintln!("Sort height: {}", sort_height);
    }

    let utxos = btc_regtest_controller.get_all_utxos(&pox_2_pubkey);

    // should *not* receive more rewards during the after sunset cycle...
    eprintln!("Got UTXOs: {}", utxos.len());
    assert_eq!(
        utxos.len(),
        14,
        "Should have received no more outputs after sunset PoX reward cycle"
    );

    // should have progressed the chain, though!
    // get the canonical chain tip
    let path = format!("{}/v2/info", &http_origin);
    let tip_info = client
        .get(&path)
        .send()
        .unwrap()
        .json::<RPCPeerInfoData>()
        .unwrap();

    eprintln!("Stacks tip is now {}", tip_info.stacks_tip_height);
    assert_eq!(tip_info.stacks_tip_height, 66);

    test_observer::clear();
    channel.stop_chains_coordinator();
}

#[derive(Debug)]
enum Signal {
    BootstrapNodeReady,
    FollowerNodeReady,
    ReplicatingAttachmentsStartTest1,
    ReplicatingAttachmentsCheckTest1(u64),
    ReplicatingAttachmentsStartTest2,
    ReplicatingAttachmentsCheckTest2(u64),
}

#[test]
#[ignore]
fn atlas_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let user_1 = StacksPrivateKey::new();
    let initial_balance_user_1 = InitialBalance {
        address: to_addr(&user_1).into(),
        amount: 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64),
    };

    // Prepare the config of the bootstrap node
    let (mut conf_bootstrap_node, _) = neon_integration_test_conf();
    let bootstrap_node_public_key = {
        let keychain = Keychain::default(conf_bootstrap_node.node.seed.clone());
        let mut pk = keychain.generate_op_signer().get_public_key();
        pk.set_compressed(true);
        pk.to_hex()
    };
    conf_bootstrap_node
        .initial_balances
        .push(initial_balance_user_1.clone());

    // Prepare the config of the follower node
    let (mut conf_follower_node, _) = neon_integration_test_conf();
    let bootstrap_node_url = format!(
        "{}@{}",
        bootstrap_node_public_key, conf_bootstrap_node.node.p2p_bind
    );
    conf_follower_node.node.set_bootstrap_nodes(
        bootstrap_node_url,
        conf_follower_node.burnchain.chain_id,
        conf_follower_node.burnchain.peer_version,
    );
    conf_follower_node.node.miner = false;
    conf_follower_node
        .initial_balances
        .push(initial_balance_user_1.clone());
    conf_follower_node
        .events_observers
        .push(EventObserverConfig {
            endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
            events_keys: vec![EventKeyType::AnyEvent],
        });

    // Our 2 nodes will share the bitcoind node
    let mut btcd_controller = BitcoinCoreController::new(conf_bootstrap_node.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let (bootstrap_node_tx, bootstrap_node_rx) = mpsc::channel();
    let (follower_node_tx, follower_node_rx) = mpsc::channel();

    let bootstrap_node_thread = thread::spawn(move || {
        let burnchain_config = Burnchain::regtest(&conf_bootstrap_node.get_burn_db_path());

        let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
            conf_bootstrap_node.clone(),
            None,
            Some(burnchain_config.clone()),
            None,
        );
        let http_origin = format!("http://{}", &conf_bootstrap_node.node.rpc_bind);

        btc_regtest_controller.bootstrap_chain(201);

        eprintln!("Chain bootstrapped...");

        let mut run_loop = neon::RunLoop::new(conf_bootstrap_node.clone());
        let blocks_processed = run_loop.get_blocks_processed_arc();
        let client = reqwest::blocking::Client::new();
        let channel = run_loop.get_coordinator_channel().unwrap();

        thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

        // give the run loop some time to start up!
        wait_for_runloop(&blocks_processed);

        // first block wakes up the run loop
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // first block will hold our VRF registration
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // second block will be the first mined Stacks block
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // Let's setup the follower now.
        follower_node_tx
            .send(Signal::BootstrapNodeReady)
            .expect("Unable to send signal");

        match bootstrap_node_rx.recv() {
            Ok(Signal::ReplicatingAttachmentsStartTest1) => {
                println!("Follower node is ready...");
            }
            _ => panic!("Bootstrap node could nod boot. Aborting test."),
        };

        // Let's publish a (1) namespace-preorder, (2) namespace-reveal and (3) name-import in this mempool

        // (define-public (namespace-preorder (hashed-salted-namespace (buff 20))
        //                            (stx-to-burn uint))
        let namespace = "passport";
        let salt = "some-salt";
        let salted_namespace = format!("{}{}", namespace, salt);
        let hashed_namespace = Hash160::from_data(salted_namespace.as_bytes());
        let tx_1 = make_contract_call(
            &user_1,
            0,
            260,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "namespace-preorder",
            &[
                Value::buff_from(hashed_namespace.to_bytes().to_vec()).unwrap(),
                Value::UInt(1000000000),
            ],
        );

        let path = format!("{}/v2/transactions", &http_origin);
        let res = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(tx_1.clone())
            .send()
            .unwrap();
        eprintln!("{:#?}", res);
        if res.status().is_success() {
            let res: String = res.json().unwrap();
            assert_eq!(
                res,
                StacksTransaction::consensus_deserialize(&mut &tx_1[..])
                    .unwrap()
                    .txid()
                    .to_string()
            );
        } else {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // (define-public (namespace-reveal (namespace (buff 20))
        //                                  (namespace-salt (buff 20))
        //                                  (p-func-base uint)
        //                                  (p-func-coeff uint)
        //                                  (p-func-b1 uint)
        //                                  (p-func-b2 uint)
        //                                  (p-func-b3 uint)
        //                                  (p-func-b4 uint)
        //                                  (p-func-b5 uint)
        //                                  (p-func-b6 uint)
        //                                  (p-func-b7 uint)
        //                                  (p-func-b8 uint)
        //                                  (p-func-b9 uint)
        //                                  (p-func-b10 uint)
        //                                  (p-func-b11 uint)
        //                                  (p-func-b12 uint)
        //                                  (p-func-b13 uint)
        //                                  (p-func-b14 uint)
        //                                  (p-func-b15 uint)
        //                                  (p-func-b16 uint)
        //                                  (p-func-non-alpha-discount uint)
        //                                  (p-func-no-vowel-discount uint)
        //                                  (lifetime uint)
        //                                  (namespace-import principal))
        let tx_2 = make_contract_call(
            &user_1,
            1,
            1000,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "namespace-reveal",
            &[
                Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                Value::buff_from(salt.as_bytes().to_vec()).unwrap(),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1),
                Value::UInt(1000),
                Value::Principal(initial_balance_user_1.address.clone()),
            ],
        );

        let path = format!("{}/v2/transactions", &http_origin);
        let res = client
            .post(&path)
            .header("Content-Type", "application/octet-stream")
            .body(tx_2.clone())
            .send()
            .unwrap();
        eprintln!("{:#?}", res);
        if res.status().is_success() {
            let res: String = res.json().unwrap();
            assert_eq!(
                res,
                StacksTransaction::consensus_deserialize(&mut &tx_2[..])
                    .unwrap()
                    .txid()
                    .to_string()
            );
        } else {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // (define-public (name-import (namespace (buff 20))
        //                             (name (buff 48))
        //                             (zonefile-hash (buff 20)))
        let zonefile_hex = "facade00";
        let hashed_zonefile = Hash160::from_data(&hex_bytes(zonefile_hex).unwrap());
        let tx_3 = make_contract_call(
            &user_1,
            2,
            500,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "name-import",
            &[
                Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                Value::buff_from("johndoe".as_bytes().to_vec()).unwrap(),
                Value::Principal(to_addr(&user_1).into()),
                Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
            ],
        );

        let body = {
            let content = PostTransactionRequestBody {
                tx: bytes_to_hex(&tx_3),
                attachment: Some(zonefile_hex.to_string()),
            };
            serde_json::to_vec(&json!(content)).unwrap()
        };

        let path = format!("{}/v2/transactions", &http_origin);
        let res = client
            .post(&path)
            .header("Content-Type", "application/json")
            .body(body)
            .send()
            .unwrap();
        eprintln!("{:#?}", res);
        if !res.status().is_success() {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }

        // From there, let's mine these transaction, and build more blocks.
        let mut sort_height = channel.get_sortitions_processed();
        let few_blocks = sort_height + 5;

        while sort_height < few_blocks {
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            sort_height = channel.get_sortitions_processed();
            eprintln!("Sort height: {}", sort_height);
        }

        // Then check that the follower is correctly replicating the attachment
        follower_node_tx
            .send(Signal::ReplicatingAttachmentsCheckTest1(sort_height))
            .expect("Unable to send signal");

        match bootstrap_node_rx.recv() {
            Ok(Signal::ReplicatingAttachmentsStartTest2) => {
                println!("Follower node is ready...");
            }
            _ => panic!("Bootstrap node could nod boot. Aborting test."),
        };

        // From there, let's mine these transaction, and build more blocks.
        let mut sort_height = channel.get_sortitions_processed();
        let few_blocks = sort_height + 5;

        while sort_height < few_blocks {
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            sort_height = channel.get_sortitions_processed();
            eprintln!("Sort height: {}", sort_height);
        }

        // Poll GET v2/attachments/<attachment-hash>
        for i in 1..10 {
            let mut attachments_did_sync = false;
            let mut timeout = 120;
            while attachments_did_sync != true {
                let zonefile_hex = hex_bytes(&format!("facade0{}", i)).unwrap();
                let hashed_zonefile = Hash160::from_data(&zonefile_hex);
                let path = format!(
                    "{}/v2/attachments/{}",
                    &http_origin,
                    hashed_zonefile.to_hex()
                );
                let res = client
                    .get(&path)
                    .header("Content-Type", "application/json")
                    .send()
                    .unwrap();
                eprintln!("{:#?}", res);
                if res.status().is_success() {
                    let attachment_response: GetAttachmentResponse = res.json().unwrap();
                    assert_eq!(attachment_response.attachment.content, zonefile_hex);
                    attachments_did_sync = true;
                } else {
                    timeout -= 1;
                    if timeout == 0 {
                        panic!("Failed syncing 9 attachments between 2 neon runloops within 60s - Something is wrong");
                    }
                    eprintln!("Attachment {} not sync'd yet", bytes_to_hex(&zonefile_hex));
                    thread::sleep(Duration::from_millis(1000));
                }
            }
        }

        // Then check that the follower is correctly replicating the attachment
        follower_node_tx
            .send(Signal::ReplicatingAttachmentsCheckTest2(sort_height))
            .expect("Unable to send signal");

        channel.stop_chains_coordinator();
    });

    // Start the attached observer
    test_observer::spawn();

    // The bootstrap node mined a few blocks and is ready, let's setup this node.
    match follower_node_rx.recv() {
        Ok(Signal::BootstrapNodeReady) => {
            println!("Booting follower node...");
        }
        _ => panic!("Bootstrap node could nod boot. Aborting test."),
    };

    let burnchain_config = Burnchain::regtest(&conf_follower_node.get_burn_db_path());
    let http_origin = format!("http://{}", &conf_follower_node.node.rpc_bind);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf_follower_node.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();
    let channel = run_loop.get_coordinator_channel().unwrap();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // Follower node is ready, the bootstrap node will now handover
    bootstrap_node_tx
        .send(Signal::ReplicatingAttachmentsStartTest1)
        .expect("Unable to send signal");

    // The bootstrap node published and mined a transaction that includes an attachment.
    // Lets observe the attachments replication kicking in.
    let target_height = match follower_node_rx.recv() {
        Ok(Signal::ReplicatingAttachmentsCheckTest1(target_height)) => target_height,
        _ => panic!("Bootstrap node could nod boot. Aborting test."),
    };

    let mut sort_height = channel.get_sortitions_processed();
    while sort_height < target_height {
        wait_for_runloop(&blocks_processed);
        sort_height = channel.get_sortitions_processed();
    }

    // Now wait for the node to sync the attachment
    let mut attachments_did_sync = false;
    let mut timeout = 60;
    while attachments_did_sync != true {
        let zonefile_hex = "facade00";
        let hashed_zonefile = Hash160::from_data(&hex_bytes(zonefile_hex).unwrap());
        let path = format!(
            "{}/v2/attachments/{}",
            &http_origin,
            hashed_zonefile.to_hex()
        );
        let res = client
            .get(&path)
            .header("Content-Type", "application/json")
            .send()
            .unwrap();
        eprintln!("{:#?}", res);
        if res.status().is_success() {
            eprintln!("Success syncing attachment - {}", res.text().unwrap());
            attachments_did_sync = true;
        } else {
            timeout -= 1;
            if timeout == 0 {
                panic!("Failed syncing 1 attachments between 2 neon runloops within 60s - Something is wrong");
            }
            eprintln!("Attachment {} not sync'd yet", zonefile_hex);
            thread::sleep(Duration::from_millis(1000));
        }
    }

    // Test 2: 9 transactions are posted to the follower.
    // We want to make sure that the miner is able to
    // 1) mine these transactions
    // 2) retrieve the attachments staged on the follower node.
    // 3) ensure that the follower is also instanciating the attachments after
    // executing the transactions, once mined.
    let namespace = "passport";
    for i in 1..10 {
        let user = StacksPrivateKey::new();
        let zonefile_hex = format!("facade0{}", i);
        let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());
        let name = format!("johndoe{}", i);
        let tx = make_contract_call(
            &user_1,
            2 + i,
            500,
            &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
            "bns",
            "name-import",
            &[
                Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                Value::Principal(to_addr(&user).into()),
                Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
            ],
        );

        let body = {
            let content = PostTransactionRequestBody {
                tx: bytes_to_hex(&tx),
                attachment: Some(zonefile_hex.to_string()),
            };
            serde_json::to_vec(&json!(content)).unwrap()
        };

        let path = format!("{}/v2/transactions", &http_origin);
        let res = client
            .post(&path)
            .header("Content-Type", "application/json")
            .body(body)
            .send()
            .unwrap();
        eprintln!("{:#?}", res);
        if !res.status().is_success() {
            eprintln!("{}", res.text().unwrap());
            panic!("");
        }
    }

    bootstrap_node_tx
        .send(Signal::ReplicatingAttachmentsStartTest2)
        .expect("Unable to send signal");

    let target_height = match follower_node_rx.recv() {
        Ok(Signal::ReplicatingAttachmentsCheckTest2(target_height)) => target_height,
        _ => panic!("Bootstrap node could not boot. Aborting test."),
    };

    let mut sort_height = channel.get_sortitions_processed();
    while sort_height < target_height {
        wait_for_runloop(&blocks_processed);
        sort_height = channel.get_sortitions_processed();
    }

    // Poll GET v2/attachments/<attachment-hash>
    for i in 1..10 {
        let mut attachments_did_sync = false;
        let mut timeout = 60;
        while attachments_did_sync != true {
            let zonefile_hex = hex_bytes(&format!("facade0{}", i)).unwrap();
            let hashed_zonefile = Hash160::from_data(&zonefile_hex);
            let path = format!(
                "{}/v2/attachments/{}",
                &http_origin,
                hashed_zonefile.to_hex()
            );
            let res = client
                .get(&path)
                .header("Content-Type", "application/json")
                .send()
                .unwrap();
            eprintln!("{:#?}", res);
            if res.status().is_success() {
                let attachment_response: GetAttachmentResponse = res.json().unwrap();
                assert_eq!(attachment_response.attachment.content, zonefile_hex);
                attachments_did_sync = true;
            } else {
                timeout -= 1;
                if timeout == 0 {
                    panic!("Failed syncing 9 attachments between 2 neon runloops within 60s - Something is wrong");
                }
                eprintln!("Attachment {} not sync'd yet", bytes_to_hex(&zonefile_hex));
                thread::sleep(Duration::from_millis(1000));
            }
        }
    }

    // Ensure that we the attached sidecar was able to receive a total of 10 attachments
    // This last assertion is flacky for some reason, it does not worth bullying the CI or disabling this whole test
    // We're using an inequality as a best effort, to make sure that **some** attachments were received.
    assert!(test_observer::get_attachments().len() > 0);
    test_observer::clear();
    channel.stop_chains_coordinator();

    bootstrap_node_thread.join().unwrap();
}

#[test]
#[ignore]
fn antientropy_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let user_1 = StacksPrivateKey::new();
    let initial_balance_user_1 = InitialBalance {
        address: to_addr(&user_1).into(),
        amount: 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64),
    };

    // Prepare the config of the bootstrap node
    let (mut conf_bootstrap_node, _) = neon_integration_test_conf();
    let bootstrap_node_public_key = {
        let keychain = Keychain::default(conf_bootstrap_node.node.seed.clone());
        let mut pk = keychain.generate_op_signer().get_public_key();
        pk.set_compressed(true);
        pk.to_hex()
    };
    conf_bootstrap_node
        .initial_balances
        .push(initial_balance_user_1.clone());
    conf_bootstrap_node.connection_options.antientropy_retry = 10; // move this along -- do anti-entropy protocol once every 10 seconds
    conf_bootstrap_node.connection_options.antientropy_public = true; // always push blocks, even if we're not NAT'ed
    conf_bootstrap_node.connection_options.max_block_push = 1000;
    conf_bootstrap_node.connection_options.max_microblock_push = 1000;

    // Prepare the config of the follower node
    let (mut conf_follower_node, _) = neon_integration_test_conf();
    let bootstrap_node_url = format!(
        "{}@{}",
        bootstrap_node_public_key, conf_bootstrap_node.node.p2p_bind
    );
    conf_follower_node.connection_options.disable_block_download = true;
    conf_follower_node.node.set_bootstrap_nodes(
        bootstrap_node_url,
        conf_follower_node.burnchain.chain_id,
        conf_follower_node.burnchain.peer_version,
    );
    conf_follower_node.node.miner = false;
    conf_follower_node
        .initial_balances
        .push(initial_balance_user_1.clone());
    conf_follower_node
        .events_observers
        .push(EventObserverConfig {
            endpoint: format!("localhost:{}", test_observer::EVENT_OBSERVER_PORT),
            events_keys: vec![EventKeyType::AnyEvent],
        });

    // Our 2 nodes will share the bitcoind node
    let mut btcd_controller = BitcoinCoreController::new(conf_bootstrap_node.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let (bootstrap_node_tx, bootstrap_node_rx) = mpsc::channel();
    let (follower_node_tx, follower_node_rx) = mpsc::channel();

    let burnchain_config = Burnchain::regtest(&conf_bootstrap_node.get_burn_db_path());
    let target_height = 3 + (3 * burnchain_config.pox_constants.reward_cycle_length);

    let bootstrap_node_thread = thread::spawn(move || {
        let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
            conf_bootstrap_node.clone(),
            None,
            Some(burnchain_config.clone()),
            None,
        );

        btc_regtest_controller.bootstrap_chain(201);

        eprintln!("Chain bootstrapped...");

        let mut run_loop = neon::RunLoop::new(conf_bootstrap_node.clone());
        let blocks_processed = run_loop.get_blocks_processed_arc();
        let channel = run_loop.get_coordinator_channel().unwrap();

        thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

        // give the run loop some time to start up!
        wait_for_runloop(&blocks_processed);

        // first block wakes up the run loop
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        // first block will hold our VRF registration
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

        for i in 0..(target_height - 3) {
            eprintln!("Mine block {}", i);
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            let sort_height = channel.get_sortitions_processed();
            eprintln!("Sort height: {}", sort_height);
        }

        // Let's setup the follower now.
        follower_node_tx
            .send(Signal::BootstrapNodeReady)
            .expect("Unable to send signal");

        eprintln!("Bootstrap node informed follower that it's ready; waiting for acknowledgement");

        // wait for bootstrap node to terminate
        match bootstrap_node_rx.recv() {
            Ok(Signal::FollowerNodeReady) => {
                println!("Follower has finished");
            }
            Ok(x) => {
                println!("Follower gave a bad signal: {:?}", &x);
                panic!();
            }
            Err(e) => {
                println!("Failed to recv: {:?}", &e);
                panic!();
            }
        };

        channel.stop_chains_coordinator();
    });

    // Start the attached observer
    test_observer::spawn();

    // The bootstrap node mined a few blocks and is ready, let's setup this node.
    match follower_node_rx.recv() {
        Ok(Signal::BootstrapNodeReady) => {
            println!("Booting follower node...");
        }
        _ => panic!("Bootstrap node could not boot. Aborting test."),
    };

    let burnchain_config = Burnchain::regtest(&conf_follower_node.get_burn_db_path());
    let http_origin = format!("http://{}", &conf_follower_node.node.rpc_bind);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf_follower_node.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let channel = run_loop.get_coordinator_channel().unwrap();

    let thread_burnchain_config = burnchain_config.clone();
    thread::spawn(move || run_loop.start(Some(thread_burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    let mut sort_height = channel.get_sortitions_processed();
    while sort_height < (target_height + 200) as u64 {
        eprintln!(
            "Follower sortition is {}, target is {}",
            sort_height,
            target_height + 200
        );
        wait_for_runloop(&blocks_processed);
        sort_height = channel.get_sortitions_processed();
        sleep_ms(1000);
    }

    eprintln!("Follower booted up; waiting for blocks");

    // wait for block height to reach target
    let mut tip_height = get_chain_tip_height(&http_origin);
    eprintln!(
        "Follower Stacks tip height is {}, wait until {} >= {} - 3",
        tip_height, tip_height, target_height
    );

    let btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf_follower_node.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );

    let mut burnchain_deadline = get_epoch_time_secs() + 60;
    while tip_height < (target_height - 3) as u64 {
        sleep_ms(1000);
        tip_height = get_chain_tip_height(&http_origin);

        eprintln!("Follower Stacks tip height is {}", tip_height);

        if burnchain_deadline < get_epoch_time_secs() {
            burnchain_deadline = get_epoch_time_secs() + 60;
            btc_regtest_controller.build_next_block(1);
        }
    }

    bootstrap_node_tx
        .send(Signal::FollowerNodeReady)
        .expect("Unable to send signal");
    bootstrap_node_thread.join().unwrap();

    eprintln!("Follower node finished");

    test_observer::clear();
    channel.stop_chains_coordinator();
}

fn wait_for_mined(
    btc_regtest_controller: &mut BitcoinRegtestController,
    blocks_processed: &Arc<AtomicU64>,
    http_origin: &str,
    users: &[StacksPrivateKey],
    account_before_nonces: &Vec<u64>,
    batch_size: usize,
    batches: usize,
    index_block_hashes: &mut Vec<StacksBlockId>,
) {
    let mut all_mined_vec = vec![false; batches * batch_size];
    let mut account_after_nonces = vec![0; batches * batch_size];
    let mut all_mined = false;
    for _k in 0..10 {
        next_block_and_wait(btc_regtest_controller, &blocks_processed);
        sleep_ms(10_000);

        let (ch, bhh) = get_chain_tip(http_origin);
        let ibh = StacksBlockHeader::make_index_block_hash(&ch, &bhh);

        if let Some(last_ibh) = index_block_hashes.last() {
            if *last_ibh != ibh {
                index_block_hashes.push(ibh);
                eprintln!("Tip is now {}", &ibh);
            }
        }

        for j in 0..batches * batch_size {
            let account_after = get_account(&http_origin, &to_addr(&users[j]));
            let account_after_nonce = account_after.nonce;
            account_after_nonces[j] = account_after_nonce;

            if account_before_nonces[j] + 1 <= account_after_nonce {
                all_mined_vec[j] = true;
            }
        }

        all_mined = all_mined_vec.iter().fold(true, |acc, elem| acc && *elem);
        if all_mined {
            break;
        }
    }
    if !all_mined {
        eprintln!(
            "Failed to mine all transactions: nonces = {:?}, expected {:?} + {}",
            &account_after_nonces, account_before_nonces, batch_size
        );
        panic!();
    }
}

#[test]
#[ignore]
fn atlas_stress_integration_test() {
    if env::var("BITCOIND_TEST") != Ok("1".into()) {
        return;
    }

    let mut initial_balances = vec![];
    let mut users = vec![];

    let batches = 5;
    let batch_size = 20;

    for _i in 0..(2 * batches * batch_size + 1) {
        let user = StacksPrivateKey::new();
        let initial_balance_user = InitialBalance {
            address: to_addr(&user).into(),
            amount: 1_000_000_000 * (core::MICROSTACKS_PER_STACKS as u64),
        };
        users.push(user);
        initial_balances.push(initial_balance_user);
    }

    // Prepare the config of the bootstrap node
    let (mut conf_bootstrap_node, _) = neon_integration_test_conf();
    conf_bootstrap_node
        .initial_balances
        .append(&mut initial_balances.clone());

    let user_1 = users.pop().unwrap();
    let initial_balance_user_1 = initial_balances.pop().unwrap();

    // Start the attached observer
    test_observer::spawn();

    let mut btcd_controller = BitcoinCoreController::new(conf_bootstrap_node.clone());
    btcd_controller
        .start_bitcoind()
        .map_err(|_e| ())
        .expect("Failed starting bitcoind");

    let burnchain_config = Burnchain::regtest(&conf_bootstrap_node.get_burn_db_path());

    let mut btc_regtest_controller = BitcoinRegtestController::with_burnchain(
        conf_bootstrap_node.clone(),
        None,
        Some(burnchain_config.clone()),
        None,
    );
    let http_origin = format!("http://{}", &conf_bootstrap_node.node.rpc_bind);

    btc_regtest_controller.bootstrap_chain(201);

    eprintln!("Chain bootstrapped...");

    let mut run_loop = neon::RunLoop::new(conf_bootstrap_node.clone());
    let blocks_processed = run_loop.get_blocks_processed_arc();
    let client = reqwest::blocking::Client::new();

    thread::spawn(move || run_loop.start(Some(burnchain_config), 0));

    // give the run loop some time to start up!
    wait_for_runloop(&blocks_processed);

    // first block wakes up the run loop
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // first block will hold our VRF registration
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    // second block will be the first mined Stacks block
    next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);

    let mut index_block_hashes = vec![];

    // Let's publish a (1) namespace-preorder, (2) namespace-reveal and (3) name-import in this mempool

    // (define-public (namespace-preorder (hashed-salted-namespace (buff 20))
    //                            (stx-to-burn uint))
    let namespace = "passport";
    let salt = "some-salt";
    let salted_namespace = format!("{}{}", namespace, salt);
    let hashed_namespace = Hash160::from_data(salted_namespace.as_bytes());
    let tx_1 = make_contract_call(
        &user_1,
        0,
        260,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "bns",
        "namespace-preorder",
        &[
            Value::buff_from(hashed_namespace.to_bytes().to_vec()).unwrap(),
            Value::UInt(1000000000),
        ],
    );

    let path = format!("{}/v2/transactions", &http_origin);
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx_1.clone())
        .send()
        .unwrap();
    eprintln!("{:#?}", res);
    if res.status().is_success() {
        let res: String = res.json().unwrap();
        assert_eq!(
            res,
            StacksTransaction::consensus_deserialize(&mut &tx_1[..])
                .unwrap()
                .txid()
                .to_string()
        );
    } else {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }

    // (define-public (namespace-reveal (namespace (buff 20))
    //                                  (namespace-salt (buff 20))
    //                                  (p-func-base uint)
    //                                  (p-func-coeff uint)
    //                                  (p-func-b1 uint)
    //                                  (p-func-b2 uint)
    //                                  (p-func-b3 uint)
    //                                  (p-func-b4 uint)
    //                                  (p-func-b5 uint)
    //                                  (p-func-b6 uint)
    //                                  (p-func-b7 uint)
    //                                  (p-func-b8 uint)
    //                                  (p-func-b9 uint)
    //                                  (p-func-b10 uint)
    //                                  (p-func-b11 uint)
    //                                  (p-func-b12 uint)
    //                                  (p-func-b13 uint)
    //                                  (p-func-b14 uint)
    //                                  (p-func-b15 uint)
    //                                  (p-func-b16 uint)
    //                                  (p-func-non-alpha-discount uint)
    //                                  (p-func-no-vowel-discount uint)
    //                                  (lifetime uint)
    //                                  (namespace-import principal))
    let tx_2 = make_contract_call(
        &user_1,
        1,
        1000,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "bns",
        "namespace-reveal",
        &[
            Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
            Value::buff_from(salt.as_bytes().to_vec()).unwrap(),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1),
            Value::UInt(1000),
            Value::Principal(initial_balance_user_1.address.clone()),
        ],
    );

    let path = format!("{}/v2/transactions", &http_origin);
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx_2.clone())
        .send()
        .unwrap();
    eprintln!("{:#?}", res);
    if res.status().is_success() {
        let res: String = res.json().unwrap();
        assert_eq!(
            res,
            StacksTransaction::consensus_deserialize(&mut &tx_2[..])
                .unwrap()
                .txid()
                .to_string()
        );
    } else {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }

    let mut mined_namespace_reveal = false;
    for _j in 0..10 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sleep_ms(10_000);

        let account_after = get_account(&http_origin, &to_addr(&user_1));
        if account_after.nonce == 2 {
            mined_namespace_reveal = true;
            break;
        }
    }
    if !mined_namespace_reveal {
        eprintln!("Did not mine namespace preorder or reveal");
        panic!();
    }

    let mut all_zonefiles = vec![];

    // make a _ton_ of name-imports
    for i in 0..batches {
        let account_before = get_account(&http_origin, &to_addr(&user_1));

        for j in 0..batch_size {
            // (define-public (name-import (namespace (buff 20))
            //                             (name (buff 48))
            //                             (zonefile-hash (buff 20)))
            let zonefile_hex = format!("facade00{:04x}{:04x}{:04x}", batch_size * i + j, i, j);
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            all_zonefiles.push(zonefile_hex.clone());

            let tx_3 = make_contract_call(
                &user_1,
                2 + (batch_size * i + j) as u64,
                500,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-import",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(format!("johndoe{}", i * batch_size + j).as_bytes().to_vec())
                        .unwrap(),
                    Value::Principal(to_addr(&users[i * batch_size + j]).into()),
                    Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_3),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{}/v2/transactions", &http_origin);
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{:#?}", res);
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        // wait for them all to be mined
        let mut all_mined = false;
        let account_after_nonce = 0;
        for _j in 0..10 {
            next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
            sleep_ms(10_000);

            let (ch, bhh) = get_chain_tip(&http_origin);
            let ibh = StacksBlockHeader::make_index_block_hash(&ch, &bhh);
            index_block_hashes.push(ibh);

            let account_after = get_account(&http_origin, &to_addr(&user_1));
            let account_after_nonce = account_after.nonce;
            if account_before.nonce + (batch_size as u64) <= account_after_nonce {
                all_mined = true;
                break;
            }
        }
        if !all_mined {
            eprintln!(
                "Failed to mine all transactions: nonce = {}, expected {}",
                account_after_nonce,
                account_before.nonce + (batch_size as u64)
            );
            panic!();
        }
    }

    // launch namespace
    // (define-public (namespace-ready (namespace (buff 20)))
    let namespace = "passport";
    let tx_4 = make_contract_call(
        &user_1,
        2 + (batch_size as u64) * (batches as u64),
        260,
        &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
        "bns",
        "namespace-ready",
        &[Value::buff_from(namespace.as_bytes().to_vec()).unwrap()],
    );

    let path = format!("{}/v2/transactions", &http_origin);
    let res = client
        .post(&path)
        .header("Content-Type", "application/octet-stream")
        .body(tx_4.clone())
        .send()
        .unwrap();
    eprintln!("{:#?}", res);
    if !res.status().is_success() {
        eprintln!("{}", res.text().unwrap());
        panic!("");
    }

    let mut mined_namespace_ready = false;
    for _j in 0..10 {
        next_block_and_wait(&mut btc_regtest_controller, &blocks_processed);
        sleep_ms(10_000);

        let (ch, bhh) = get_chain_tip(&http_origin);
        let ibh = StacksBlockHeader::make_index_block_hash(&ch, &bhh);
        index_block_hashes.push(ibh);

        let account_after = get_account(&http_origin, &to_addr(&user_1));
        if account_after.nonce == 2 + (batch_size as u64) * (batches as u64) {
            mined_namespace_ready = true;
            break;
        }
    }
    if !mined_namespace_ready {
        eprintln!("Did not mine namespace ready");
        panic!();
    }

    // make a _ton_ of preorders
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let fqn = format!("janedoe{}.passport", j);
            let fqn_bytes = fqn.as_bytes().to_vec();
            let salt = format!("{:04x}", j);
            let salt_bytes = salt.as_bytes().to_vec();
            let mut hash_data = fqn_bytes.clone();
            hash_data.append(&mut salt_bytes.clone());

            let salted_hash = Hash160::from_data(&hash_data);

            let tx_5 = make_contract_call(
                &users[batches * batch_size + j],
                0,
                500,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-preorder",
                &[
                    Value::buff_from(salted_hash.0.to_vec()).unwrap(),
                    Value::UInt(500),
                ],
            );

            let path = format!("{}/v2/transactions", &http_origin);
            let res = client
                .post(&path)
                .header("Content-Type", "application/octet-stream")
                .body(tx_5.clone())
                .send()
                .unwrap();

            eprintln!(
                "sent preorder for {}:\n{:#?}",
                &to_addr(&users[batches * batch_size + j]),
                res
            );
            if !res.status().is_success() {
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // make a _ton_ of registers
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let name = format!("janedoe{}", j);
            let salt = format!("{:04x}", j);

            let zonefile_hex = format!("facade01{:04x}", j);
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            all_zonefiles.push(zonefile_hex.clone());

            let tx_6 = make_contract_call(
                &users[batches * batch_size + j],
                1,
                500,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-register",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(salt.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_6),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{}/v2/transactions", &http_origin);
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{:#?}", res);
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // make a _ton_ of updates
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let name = format!("janedoe{}", j);
            let zonefile_hex = format!("facade02{:04x}", j);
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            all_zonefiles.push(zonefile_hex.clone());

            let tx_7 = make_contract_call(
                &users[batches * batch_size + j],
                2,
                500,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-update",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_7),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{}/v2/transactions", &http_origin);
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{:#?}", res);
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // make a _ton_ of renewals
    {
        let mut account_before_nonces = vec![0; batches * batch_size];
        for j in 0..batches * batch_size {
            let account_before =
                get_account(&http_origin, &to_addr(&users[batches * batch_size + j]));
            account_before_nonces[j] = account_before.nonce;

            let name = format!("janedoe{}", j);
            let zonefile_hex = format!("facade03{:04x}", j);
            let hashed_zonefile = Hash160::from_data(&hex_bytes(&zonefile_hex).unwrap());

            all_zonefiles.push(zonefile_hex.clone());

            let tx_8 = make_contract_call(
                &users[batches * batch_size + j],
                3,
                500,
                &StacksAddress::from_string("ST000000000000000000002AMW42H").unwrap(),
                "bns",
                "name-renewal",
                &[
                    Value::buff_from(namespace.as_bytes().to_vec()).unwrap(),
                    Value::buff_from(name.as_bytes().to_vec()).unwrap(),
                    Value::UInt(500),
                    Value::none(),
                    Value::some(Value::buff_from(hashed_zonefile.as_bytes().to_vec()).unwrap())
                        .unwrap(),
                ],
            );

            let body = {
                let content = PostTransactionRequestBody {
                    tx: bytes_to_hex(&tx_8),
                    attachment: Some(zonefile_hex.to_string()),
                };
                serde_json::to_vec(&json!(content)).unwrap()
            };

            let path = format!("{}/v2/transactions", &http_origin);
            let res = client
                .post(&path)
                .header("Content-Type", "application/json")
                .body(body)
                .send()
                .unwrap();
            eprintln!("{:#?}", res);
            if !res.status().is_success() {
                eprintln!("{}", res.text().unwrap());
                panic!("");
            }
        }

        wait_for_mined(
            &mut btc_regtest_controller,
            &blocks_processed,
            &http_origin,
            &users[batches * batch_size..],
            &account_before_nonces,
            batch_size,
            batches,
            &mut index_block_hashes,
        );
    }

    // find all attachment indexes and make sure we can get them
    let mut attachment_indexes = HashMap::new();
    let mut attachment_hashes = HashMap::new();
    {
        let atlasdb_path = conf_bootstrap_node.get_atlas_db_file_path();
        let atlasdb = AtlasDB::connect(AtlasConfig::default(false), &atlasdb_path, false).unwrap();
        for ibh in index_block_hashes.iter() {
            let indexes = query_rows::<u64, _>(
                &atlasdb.conn,
                "SELECT attachment_index FROM attachment_instances WHERE index_block_hash = ?1",
                &[ibh],
            )
            .unwrap();
            if indexes.len() > 0 {
                attachment_indexes.insert(ibh.clone(), indexes.clone());
            }

            for index in indexes.iter() {
                let mut hashes = query_row_columns::<Hash160, _>(
                    &atlasdb.conn,
                    "SELECT content_hash FROM attachment_instances WHERE index_block_hash = ?1 AND attachment_index = ?2",
                    &[ibh as &dyn ToSql, &u64_to_sql(*index).unwrap() as &dyn ToSql],
                    "content_hash")
                .unwrap();
                if hashes.len() > 0 {
                    assert_eq!(hashes.len(), 1);
                    attachment_hashes.insert((ibh.clone(), *index), hashes.pop());
                }
            }
        }
    }
    eprintln!("attachment_indexes = {:?}", &attachment_indexes);

    for (ibh, attachments) in attachment_indexes.iter() {
        let l = attachments.len();
        for i in 0..(l / MAX_ATTACHMENT_INV_PAGES_PER_REQUEST + 1) {
            if i * MAX_ATTACHMENT_INV_PAGES_PER_REQUEST >= l {
                break;
            }

            let attachments_batch = attachments[i * MAX_ATTACHMENT_INV_PAGES_PER_REQUEST
                ..cmp::min((i + 1) * MAX_ATTACHMENT_INV_PAGES_PER_REQUEST, l)]
                .to_vec();
            let path = format!(
                "{}/v2/attachments/inv?index_block_hash={}&pages_indexes={}",
                &http_origin,
                ibh,
                attachments_batch
                    .iter()
                    .map(|a| format!("{}", &a))
                    .collect::<Vec<String>>()
                    .join(",")
            );

            let attempts = 10;
            let ts_begin = get_epoch_time_ms();
            for _ in 0..attempts {
                let res = client.get(&path).send().unwrap();

                if res.status().is_success() {
                    let attachment_inv_response: GetAttachmentsInvResponse = res.json().unwrap();
                    eprintln!(
                        "attachment inv response for {}: {:?}",
                        &path, &attachment_inv_response
                    );
                } else {
                    eprintln!("Bad response for `{}`: `{:?}`", &path, res.text().unwrap());
                    panic!();
                }
            }
            let ts_end = get_epoch_time_ms();
            let total_time = ts_end.saturating_sub(ts_begin);
            eprintln!("Requested {} {} times in {}ms", &path, attempts, total_time);

            // requests should take no more than 20ms
            assert!(
                total_time < attempts * 50,
                "Atlas inventory request is too slow: {} >= {} * 50",
                total_time,
                attempts
            );
        }

        for i in 0..l {
            if attachments[i] == 0 {
                continue;
            }
            let content_hash = attachment_hashes
                .get(&(*ibh, attachments[i]))
                .cloned()
                .unwrap()
                .unwrap();

            let path = format!("{}/v2/attachments/{}", &http_origin, &content_hash);

            let attempts = 10;
            let ts_begin = get_epoch_time_ms();
            for _ in 0..attempts {
                let res = client.get(&path).send().unwrap();

                if res.status().is_success() {
                    let attachment_response: GetAttachmentResponse = res.json().unwrap();
                    eprintln!(
                        "attachment response for {}: {:?}",
                        &path, &attachment_response
                    );
                } else {
                    eprintln!("Bad response for `{}`: `{:?}`", &path, res.text().unwrap());
                    panic!();
                }
            }
            let ts_end = get_epoch_time_ms();
            let total_time = ts_end.saturating_sub(ts_begin);
            eprintln!("Requested {} {} times in {}ms", &path, attempts, total_time);

            // requests should take no more than 40ms
            assert!(
                total_time < attempts * 50,
                "Atlas chunk request is too slow: {} >= {} * 50",
                total_time,
                attempts
            );
        }
    }

    test_observer::clear();
}
