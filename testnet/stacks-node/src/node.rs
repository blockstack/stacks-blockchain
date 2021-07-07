use std::convert::TryFrom;
use std::default::Default;
use std::net::SocketAddr;
use std::sync::mpsc::{sync_channel, Receiver, SyncSender};
use std::sync::{atomic::AtomicBool, Arc};
use std::{collections::HashSet, env};
use std::{thread, thread::JoinHandle, time};

use stacks::chainstate::burn::operations::{
    leader_block_commit::{RewardSetInfo, BURN_BLOCK_MINED_AT_MODULUS},
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp,
};
use stacks::chainstate::burn::ConsensusHash;
use stacks::chainstate::stacks::db::{
    ChainStateBootData, ClarityTx, StacksChainState, StacksHeaderInfo,
};
use stacks::chainstate::stacks::events::{
    StacksTransactionEvent, StacksTransactionReceipt, TransactionOrigin,
};
use stacks::chainstate::stacks::{
    CoinbasePayload, StacksBlock, StacksMicroblock, StacksTransaction, StacksTransactionSigner,
    TransactionAnchorMode, TransactionPayload, TransactionVersion,
};
use stacks::chainstate::{burn::db::sortdb::SortitionDB, stacks::db::StacksEpochReceipt};
use stacks::core::mempool::MemPoolDB;
use stacks::net::atlas::AttachmentInstance;
use stacks::net::{
    atlas::{AtlasConfig, AtlasDB},
    db::PeerDB,
    p2p::PeerNetwork,
    rpc::RPCHandlerArgs,
    Error as NetError, PeerAddress,
};
use stacks::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, StacksAddress, StacksBlockHeader, VRFSeed,
};
use stacks::types::proof::TrieHash;
use stacks::util::get_epoch_time_secs;
use stacks::util::hash::Sha256Sum;
use stacks::util::secp256k1::Secp256k1PrivateKey;
use stacks::util::strings::UrlString;
use stacks::util::vrf::VRFPublicKey;
use stacks::{
    burnchains::{Burnchain, Txid},
    chainstate::stacks::db::{
        ChainstateAccountBalance, ChainstateAccountLockup, ChainstateBNSName,
        ChainstateBNSNamespace,
    },
};

use crate::{genesis_data::USE_TEST_GENESIS_CHAINSTATE, run_loop::RegisteredKey};

use super::{BurnchainController, BurnchainTip, Config, EventDispatcher, Keychain, Tenure};
use stacks::burnchains::bitcoin::BitcoinNetworkType;
use stacks::burnchains::PoxConstants;

#[derive(Debug, Clone)]
pub struct ChainTip {
    pub metadata: StacksHeaderInfo,
    pub block: StacksBlock,
    pub receipts: Vec<StacksTransactionReceipt>,
}

impl ChainTip {
    pub fn genesis(
        first_burnchain_block_hash: &BurnchainHeaderHash,
        first_burnchain_block_height: u64,
        first_burnchain_block_timestamp: u64,
    ) -> ChainTip {
        ChainTip {
            metadata: StacksHeaderInfo::genesis(
                TrieHash([0u8; 32]),
                first_burnchain_block_hash,
                first_burnchain_block_height as u32,
                first_burnchain_block_timestamp,
            ),
            block: StacksBlock::genesis_block(),
            receipts: vec![],
        }
    }
}

/// Node is a structure modelising an active node working on the stacks chain.
pub struct Node {
    pub chain_state: StacksChainState,
    pub config: Config,
    active_registered_key: Option<RegisteredKey>,
    bootstraping_chain: bool,
    pub burnchain_tip: Option<BurnchainTip>,
    pub chain_tip: Option<ChainTip>,
    keychain: Keychain,
    last_sortitioned_block: Option<BurnchainTip>,
    event_dispatcher: EventDispatcher,
    nonce: u64,
    attachments_tx: SyncSender<HashSet<AttachmentInstance>>,
}

pub fn get_account_lockups(
    use_test_chainstate_data: bool,
) -> Box<dyn Iterator<Item = ChainstateAccountLockup>> {
    Box::new(
        stx_genesis::GenesisData::new(use_test_chainstate_data)
            .read_lockups()
            .map(|item| ChainstateAccountLockup {
                address: item.address,
                amount: item.amount,
                block_height: item.block_height,
            }),
    )
}

pub fn get_account_balances(
    use_test_chainstate_data: bool,
) -> Box<dyn Iterator<Item = ChainstateAccountBalance>> {
    Box::new(
        stx_genesis::GenesisData::new(use_test_chainstate_data)
            .read_balances()
            .map(|item| ChainstateAccountBalance {
                address: item.address,
                amount: item.amount,
            }),
    )
}

pub fn get_namespaces(
    use_test_chainstate_data: bool,
) -> Box<dyn Iterator<Item = ChainstateBNSNamespace>> {
    Box::new(
        stx_genesis::GenesisData::new(use_test_chainstate_data)
            .read_namespaces()
            .map(|item| ChainstateBNSNamespace {
                namespace_id: item.namespace_id,
                importer: item.importer,
                buckets: item.buckets,
                base: item.base as u64,
                coeff: item.coeff as u64,
                nonalpha_discount: item.nonalpha_discount as u64,
                no_vowel_discount: item.no_vowel_discount as u64,
                lifetime: item.lifetime as u64,
            }),
    )
}

pub fn get_names(use_test_chainstate_data: bool) -> Box<dyn Iterator<Item = ChainstateBNSName>> {
    Box::new(
        stx_genesis::GenesisData::new(use_test_chainstate_data)
            .read_names()
            .map(|item| ChainstateBNSName {
                fully_qualified_name: item.fully_qualified_name,
                owner: item.owner,
                zonefile_hash: item.zonefile_hash,
            }),
    )
}

fn spawn_peer(
    is_mainnet: bool,
    chain_id: u32,
    mut this: PeerNetwork,
    p2p_sock: &SocketAddr,
    rpc_sock: &SocketAddr,
    burn_db_path: String,
    stacks_chainstate_path: String,
    event_dispatcher: EventDispatcher,
    exit_at_block_height: Option<u64>,
    genesis_chainstate_hash: Sha256Sum,
    poll_timeout: u64,
    attachments_rx: Receiver<HashSet<AttachmentInstance>>,
) -> Result<JoinHandle<()>, NetError> {
    this.bind(p2p_sock, rpc_sock).unwrap();
    let server_thread = thread::spawn(move || {
        let handler_args = RPCHandlerArgs {
            exit_at_block_height: exit_at_block_height.as_ref(),
            genesis_chainstate_hash: genesis_chainstate_hash,
            ..RPCHandlerArgs::default()
        };

        loop {
            let sortdb = match SortitionDB::open(&burn_db_path, false) {
                Ok(x) => x,
                Err(e) => {
                    warn!("Error while connecting burnchain db in peer loop: {}", e);
                    thread::sleep(time::Duration::from_secs(1));
                    continue;
                }
            };
            let (mut chainstate, _) =
                match StacksChainState::open(is_mainnet, chain_id, &stacks_chainstate_path) {
                    Ok(x) => x,
                    Err(e) => {
                        warn!("Error while connecting chainstate db in peer loop: {}", e);
                        thread::sleep(time::Duration::from_secs(1));
                        continue;
                    }
                };

            let mut mem_pool = match MemPoolDB::open(is_mainnet, chain_id, &stacks_chainstate_path)
            {
                Ok(x) => x,
                Err(e) => {
                    warn!("Error while connecting to mempool db in peer loop: {}", e);
                    thread::sleep(time::Duration::from_secs(1));
                    continue;
                }
            };

            let mut expected_attachments = match attachments_rx.try_recv() {
                Ok(expected_attachments) => expected_attachments,
                _ => {
                    debug!("Atlas: attachment channel is empty");
                    HashSet::new()
                }
            };

            let net_result = this
                .run(
                    &sortdb,
                    &mut chainstate,
                    &mut mem_pool,
                    None,
                    false,
                    false,
                    poll_timeout,
                    &handler_args,
                    &mut expected_attachments,
                )
                .unwrap();
            if net_result.has_transactions() {
                event_dispatcher.process_new_mempool_txs(net_result.transactions())
            }
            // Dispatch retrieved attachments, if any.
            if net_result.has_attachments() {
                event_dispatcher.process_new_attachments(&net_result.attachments);
            }
        }
    });
    Ok(server_thread)
}

// Check if the small test genesis chainstate data should be used.
// First check env var, then config file, then use default.
pub fn use_test_genesis_chainstate(config: &Config) -> bool {
    if env::var("BLOCKSTACK_USE_TEST_GENESIS_CHAINSTATE") == Ok("1".to_string()) {
        true
    } else if let Some(use_test_genesis_chainstate) = config.node.use_test_genesis_chainstate {
        use_test_genesis_chainstate
    } else {
        USE_TEST_GENESIS_CHAINSTATE
    }
}

impl Node {
    /// Instantiate and initialize a new node, given a config
    pub fn new(
        config: Config,
        boot_block_exec: Box<dyn FnOnce(&mut ClarityTx) -> ()>,
        attachments_tx: SyncSender<HashSet<AttachmentInstance>>,
    ) -> Self {
        let use_test_genesis_data = if config.burnchain.mode == "mocknet" {
            use_test_genesis_chainstate(&config)
        } else {
            USE_TEST_GENESIS_CHAINSTATE
        };

        let keychain = Keychain::default(config.node.seed.clone());

        let initial_balances = config
            .initial_balances
            .iter()
            .map(|e| (e.address.clone(), e.amount))
            .collect();
        let pox_constants = match config.burnchain.get_bitcoin_network() {
            (_, BitcoinNetworkType::Mainnet) => PoxConstants::mainnet_default(),
            (_, BitcoinNetworkType::Testnet) => PoxConstants::testnet_default(),
            (_, BitcoinNetworkType::Regtest) => PoxConstants::regtest_default(),
        };

        let mut boot_data = ChainStateBootData {
            initial_balances,
            first_burnchain_block_hash: BurnchainHeaderHash::zero(),
            first_burnchain_block_height: 0,
            first_burnchain_block_timestamp: 0,
            pox_constants,
            post_flight_callback: Some(boot_block_exec),
            get_bulk_initial_lockups: Some(Box::new(move || {
                get_account_lockups(use_test_genesis_data)
            })),
            get_bulk_initial_balances: Some(Box::new(move || {
                get_account_balances(use_test_genesis_data)
            })),
            get_bulk_initial_namespaces: Some(Box::new(move || {
                get_namespaces(use_test_genesis_data)
            })),
            get_bulk_initial_names: Some(Box::new(move || get_names(use_test_genesis_data))),
        };

        let chain_state_result = StacksChainState::open_and_exec(
            config.is_mainnet(),
            config.burnchain.chain_id,
            &config.get_chainstate_path_str(),
            Some(&mut boot_data),
            config.block_limit.clone(),
        );

        let (chain_state, receipts) = match chain_state_result {
            Ok(res) => res,
            Err(err) => panic!(
                "Error while opening chain state at path {}: {:?}",
                config.get_chainstate_path_str(),
                err
            ),
        };

        // avoid race to create condition on mempool db
        let _mem_pool = MemPoolDB::open(
            config.is_mainnet(),
            config.burnchain.chain_id,
            &chain_state.root_path,
        )
        .expect("FATAL: failed to initiate mempool");

        let mut event_dispatcher = EventDispatcher::new();

        for observer in &config.events_observers {
            event_dispatcher.register_observer(observer, Arc::new(AtomicBool::new(true)));
        }

        event_dispatcher.process_boot_receipts(receipts);

        Self {
            active_registered_key: None,
            bootstraping_chain: false,
            chain_state,
            chain_tip: None,
            keychain,
            last_sortitioned_block: None,
            config,
            burnchain_tip: None,
            nonce: 0,
            event_dispatcher,
            attachments_tx,
        }
    }

    pub fn init_and_sync(
        config: Config,
        burnchain_controller: &mut Box<dyn BurnchainController>,
    ) -> Node {
        let burnchain_tip = burnchain_controller.get_chain_tip();

        let keychain = Keychain::default(config.node.seed.clone());

        let mut event_dispatcher = EventDispatcher::new();

        for observer in &config.events_observers {
            event_dispatcher.register_observer(observer, Arc::new(AtomicBool::new(true)));
        }

        let chainstate_path = config.get_chainstate_path_str();
        let sortdb_path = config.get_burn_db_file_path();

        let (chain_state, _) = match StacksChainState::open(
            config.is_mainnet(),
            config.burnchain.chain_id,
            &chainstate_path,
        ) {
            Ok(x) => x,
            Err(_e) => panic!(),
        };

        let (attachments_tx, attachments_rx) = sync_channel(1);
        let mut node = Node {
            active_registered_key: None,
            bootstraping_chain: false,
            chain_state,
            chain_tip: None,
            keychain,
            last_sortitioned_block: None,
            config,
            burnchain_tip: None,
            nonce: 0,
            event_dispatcher,
            attachments_tx,
        };

        node.spawn_peer_server(attachments_rx);

        loop {
            let sortdb =
                SortitionDB::open(&sortdb_path, false).expect("BUG: failed to open burn database");
            if let Ok(Some(ref chain_tip)) = node.chain_state.get_stacks_chain_tip(&sortdb) {
                if chain_tip.consensus_hash == burnchain_tip.block_snapshot.consensus_hash {
                    info!("Syncing Stacks blocks - completed");
                    break;
                } else {
                    info!(
                        "Syncing Stacks blocks - received block #{}",
                        chain_tip.height
                    );
                }
            } else {
                info!("Syncing Stacks blocks - unable to progress");
            }
            thread::sleep(time::Duration::from_secs(5));
        }
        node
    }

    pub fn spawn_peer_server(&mut self, attachments_rx: Receiver<HashSet<AttachmentInstance>>) {
        // we can call _open_ here rather than _connect_, since connect is first called in
        //   make_genesis_block
        let sortdb = SortitionDB::open(&self.config.get_burn_db_file_path(), true)
            .expect("Error while instantiating burnchain db");

        let burnchain = Burnchain::regtest(&self.config.get_burn_db_path());

        let view = {
            let sortition_tip = SortitionDB::get_canonical_burn_chain_tip(&sortdb.conn())
                .expect("Failed to get sortition tip");
            SortitionDB::get_burnchain_view(&sortdb.conn(), &burnchain, &sortition_tip).unwrap()
        };

        // create a new peerdb
        let data_url = UrlString::try_from(format!("{}", self.config.node.data_url)).unwrap();

        let initial_neighbors = self.config.node.bootstrap_node.clone();

        println!("BOOTSTRAP WITH {:?}", initial_neighbors);

        let rpc_sock: SocketAddr = self.config.node.rpc_bind.parse().expect(&format!(
            "Failed to parse socket: {}",
            &self.config.node.rpc_bind
        ));
        let p2p_sock: SocketAddr = self.config.node.p2p_bind.parse().expect(&format!(
            "Failed to parse socket: {}",
            &self.config.node.p2p_bind
        ));
        let p2p_addr: SocketAddr = self.config.node.p2p_address.parse().expect(&format!(
            "Failed to parse socket: {}",
            &self.config.node.p2p_address
        ));
        let node_privkey = {
            let mut re_hashed_seed = self.config.node.local_peer_seed.clone();
            let my_private_key = loop {
                match Secp256k1PrivateKey::from_slice(&re_hashed_seed[..]) {
                    Ok(sk) => break sk,
                    Err(_) => {
                        re_hashed_seed = Sha256Sum::from_data(&re_hashed_seed[..])
                            .as_bytes()
                            .to_vec()
                    }
                }
            };
            my_private_key
        };

        let mut peerdb = PeerDB::connect(
            &self.config.get_peer_db_file_path(),
            true,
            self.config.burnchain.chain_id,
            burnchain.network_id,
            Some(node_privkey),
            self.config.connection_options.private_key_lifetime.clone(),
            PeerAddress::from_socketaddr(&p2p_addr),
            p2p_sock.port(),
            data_url,
            &vec![],
            Some(&initial_neighbors),
        )
        .unwrap();

        println!("DENY NEIGHBORS {:?}", &self.config.node.deny_nodes);
        {
            let mut tx = peerdb.tx_begin().unwrap();
            for denied in self.config.node.deny_nodes.iter() {
                PeerDB::set_deny_peer(
                    &mut tx,
                    denied.addr.network_id,
                    &denied.addr.addrbytes,
                    denied.addr.port,
                    get_epoch_time_secs() + 24 * 365 * 3600,
                )
                .unwrap();
            }
            tx.commit().unwrap();
        }
        let atlas_config = AtlasConfig::default(false);
        let atlasdb =
            AtlasDB::connect(atlas_config, &self.config.get_atlas_db_file_path(), true).unwrap();

        let local_peer = match PeerDB::get_local_peer(peerdb.conn()) {
            Ok(local_peer) => local_peer,
            _ => panic!("Unable to retrieve local peer"),
        };

        let event_dispatcher = self.event_dispatcher.clone();
        let exit_at_block_height = self.config.burnchain.process_exit_at_block_height.clone();

        let p2p_net = PeerNetwork::new(
            peerdb,
            atlasdb,
            local_peer,
            self.config.burnchain.peer_version,
            burnchain,
            view,
            self.config.connection_options.clone(),
        );
        let _join_handle = spawn_peer(
            self.config.is_mainnet(),
            self.config.burnchain.chain_id,
            p2p_net,
            &p2p_sock,
            &rpc_sock,
            self.config.get_burn_db_file_path(),
            self.config.get_chainstate_path_str(),
            event_dispatcher,
            exit_at_block_height,
            Sha256Sum::from_hex(stx_genesis::GENESIS_CHAINSTATE_HASH).unwrap(),
            1000,
            attachments_rx,
        )
        .unwrap();

        info!("Start HTTP server on: {}", &self.config.node.rpc_bind);
        info!("Start P2P server on: {}", &self.config.node.p2p_bind);
    }

    pub fn setup(&mut self, burnchain_controller: &mut Box<dyn BurnchainController>) {
        // Register a new key
        let burnchain_tip = burnchain_controller.get_chain_tip();
        let vrf_pk = self
            .keychain
            .rotate_vrf_keypair(burnchain_tip.block_snapshot.block_height);
        let consensus_hash = burnchain_tip.block_snapshot.consensus_hash;
        let key_reg_op = self.generate_leader_key_register_op(vrf_pk, &consensus_hash);
        let mut op_signer = self.keychain.generate_op_signer();
        burnchain_controller.submit_operation(key_reg_op, &mut op_signer, 1);
    }

    /// Process an state coming from the burnchain, by extracting the validated KeyRegisterOp
    /// and inspecting if a sortition was won.
    pub fn process_burnchain_state(
        &mut self,
        burnchain_tip: &BurnchainTip,
    ) -> (Option<BurnchainTip>, bool) {
        let mut new_key = None;
        let mut last_sortitioned_block = None;
        let mut won_sortition = false;
        let ops = &burnchain_tip.state_transition.accepted_ops;
        let is_mainnet = self.config.is_mainnet();

        for op in ops.iter() {
            match op {
                BlockstackOperationType::LeaderKeyRegister(ref op) => {
                    if op.address == self.keychain.get_address(is_mainnet) {
                        // Registered key has been mined
                        new_key = Some(RegisteredKey {
                            vrf_public_key: op.public_key.clone(),
                            block_height: op.block_height as u64,
                            op_vtxindex: op.vtxindex as u32,
                        });
                    }
                }
                BlockstackOperationType::LeaderBlockCommit(ref op) => {
                    if op.txid == burnchain_tip.block_snapshot.winning_block_txid {
                        last_sortitioned_block = Some(burnchain_tip.clone());
                        if op.apparent_sender == self.keychain.get_burnchain_signer() {
                            won_sortition = true;
                        }
                    }
                }
                BlockstackOperationType::PreStx(_)
                | BlockstackOperationType::StackStx(_)
                | BlockstackOperationType::TransferStx(_)
                | BlockstackOperationType::UserBurnSupport(_) => {
                    // no-op, ops are not supported / produced at this point.
                }
            }
        }

        // Update the active key so we use the latest registered key.
        if new_key.is_some() {
            self.active_registered_key = new_key;
        }

        // Update last_sortitioned_block so we keep a reference to the latest
        // block including a sortition.
        if last_sortitioned_block.is_some() {
            self.last_sortitioned_block = last_sortitioned_block;
        }

        // Keep a pointer of the burnchain's chain tip.
        self.burnchain_tip = Some(burnchain_tip.clone());

        (self.last_sortitioned_block.clone(), won_sortition)
    }

    /// Prepares the node to run a tenure consisting in bootstraping the chain.
    ///
    /// Will internally call initiate_new_tenure().
    pub fn initiate_genesis_tenure(&mut self, burnchain_tip: &BurnchainTip) -> Option<Tenure> {
        // Set the `bootstraping_chain` flag, that will be unset once the
        // bootstraping tenure ran successfully (process_tenure).
        self.bootstraping_chain = true;

        self.last_sortitioned_block = Some(burnchain_tip.clone());

        self.initiate_new_tenure()
    }

    /// Constructs and returns an instance of Tenure, that can be run
    /// on an isolated thread and discarded or canceled without corrupting the
    /// chain state of the node.
    pub fn initiate_new_tenure(&mut self) -> Option<Tenure> {
        // Get the latest registered key
        let registered_key = match &self.active_registered_key {
            None => {
                // We're continuously registering new keys, as such, this branch
                // should be unreachable.
                unreachable!()
            }
            Some(ref key) => key,
        };

        let block_to_build_upon = match &self.last_sortitioned_block {
            None => unreachable!(),
            Some(block) => block.clone(),
        };

        // Generates a proof out of the sortition hash provided in the params.
        let vrf_proof = self
            .keychain
            .generate_proof(
                &registered_key.vrf_public_key,
                block_to_build_upon.block_snapshot.sortition_hash.as_bytes(),
            )
            .unwrap();

        // Generates a new secret key for signing the trail of microblocks
        // of the upcoming tenure.
        let microblock_secret_key = self
            .keychain
            .rotate_microblock_keypair(block_to_build_upon.block_snapshot.block_height);

        // Get the stack's chain tip
        let chain_tip = match self.bootstraping_chain {
            true => ChainTip::genesis(&BurnchainHeaderHash::zero(), 0, 0),
            false => match &self.chain_tip {
                Some(chain_tip) => chain_tip.clone(),
                None => unreachable!(),
            },
        };

        let mem_pool = MemPoolDB::open(
            self.config.is_mainnet(),
            self.config.burnchain.chain_id,
            &self.chain_state.root_path,
        )
        .expect("FATAL: failed to open mempool");

        // Construct the coinbase transaction - 1st txn that should be handled and included in
        // the upcoming tenure.
        let coinbase_tx = self.generate_coinbase_tx(self.config.is_mainnet());

        let burn_fee_cap = self.config.burnchain.burn_fee_cap;

        // Construct the upcoming tenure
        let tenure = Tenure::new(
            chain_tip,
            coinbase_tx,
            self.config.clone(),
            mem_pool,
            microblock_secret_key,
            block_to_build_upon,
            vrf_proof,
            burn_fee_cap,
        );

        Some(tenure)
    }

    pub fn commit_artifacts(
        &mut self,
        anchored_block_from_ongoing_tenure: &StacksBlock,
        burnchain_tip: &BurnchainTip,
        burnchain_controller: &mut Box<dyn BurnchainController>,
        burn_fee: u64,
    ) {
        if self.active_registered_key.is_some() {
            let registered_key = self.active_registered_key.clone().unwrap();

            let vrf_proof = self
                .keychain
                .generate_proof(
                    &registered_key.vrf_public_key,
                    burnchain_tip.block_snapshot.sortition_hash.as_bytes(),
                )
                .unwrap();

            let op = self.generate_block_commit_op(
                anchored_block_from_ongoing_tenure.header.block_hash(),
                burn_fee,
                &registered_key,
                &burnchain_tip,
                VRFSeed::from_proof(&vrf_proof),
            );

            let mut op_signer = self.keychain.generate_op_signer();
            burnchain_controller.submit_operation(op, &mut op_signer, 1);
        }
    }

    /// Process artifacts from the tenure.
    /// At this point, we're modifying the chainstate, and merging the artifacts from the previous tenure.
    pub fn process_tenure(
        &mut self,
        anchored_block: &StacksBlock,
        consensus_hash: &ConsensusHash,
        microblocks: Vec<StacksMicroblock>,
        db: &mut SortitionDB,
    ) -> ChainTip {
        let parent_consensus_hash = {
            // look up parent consensus hash
            let ic = db.index_conn();
            let parent_consensus_hash = StacksChainState::get_parent_consensus_hash(
                &ic,
                &anchored_block.header.parent_block,
                consensus_hash,
            )
            .expect(&format!(
                "BUG: could not query chainstate to find parent consensus hash of {}/{}",
                consensus_hash,
                &anchored_block.block_hash()
            ))
            .expect(&format!(
                "BUG: no such parent of block {}/{}",
                consensus_hash,
                &anchored_block.block_hash()
            ));

            // Preprocess the anchored block
            self.chain_state
                .preprocess_anchored_block(
                    &ic,
                    consensus_hash,
                    &anchored_block,
                    &parent_consensus_hash,
                    0,
                )
                .unwrap();

            // Preprocess the microblocks
            for microblock in microblocks.iter() {
                let res = self
                    .chain_state
                    .preprocess_streamed_microblock(
                        &consensus_hash,
                        &anchored_block.block_hash(),
                        microblock,
                    )
                    .unwrap();
                if !res {
                    warn!(
                        "Unhandled error while pre-processing microblock {}",
                        microblock.header.block_hash()
                    );
                }
            }

            parent_consensus_hash
        };

        // get previous burn block stats
        let (parent_burn_block_hash, parent_burn_block_height, parent_burn_block_timestamp) =
            if anchored_block.is_first_mined() {
                (BurnchainHeaderHash([0; 32]), 0, 0)
            } else {
                match SortitionDB::get_block_snapshot_consensus(db.conn(), &parent_consensus_hash)
                    .unwrap()
                {
                    Some(sn) => (
                        sn.burn_header_hash,
                        sn.block_height as u32,
                        sn.burn_header_timestamp,
                    ),
                    None => {
                        // shouldn't happen
                        warn!(
                            "CORRUPTION: block {}/{} does not correspond to a burn block",
                            &parent_consensus_hash, &anchored_block.header.parent_block
                        );
                        (BurnchainHeaderHash([0; 32]), 0, 0)
                    }
                }
            };

        let atlas_config = AtlasConfig::default(false);
        let mut processed_blocks = vec![];
        loop {
            let mut process_blocks_at_tip = {
                let tx = db.tx_begin_at_tip();
                self.chain_state.process_blocks(tx, 1)
            };
            match process_blocks_at_tip {
                Err(e) => panic!("Error while processing block - {:?}", e),
                Ok(ref mut blocks) => {
                    if blocks.len() == 0 {
                        break;
                    } else {
                        for block in blocks.iter() {
                            match block {
                                (Some(epoch_receipt), _) => {
                                    let attachments_instances =
                                        self.get_attachment_instances(epoch_receipt, &atlas_config);
                                    if !attachments_instances.is_empty() {
                                        match self.attachments_tx.send(attachments_instances) {
                                            Ok(_) => {}
                                            Err(e) => {
                                                error!("Error dispatching attachments {}", e);
                                                panic!();
                                            }
                                        };
                                    }
                                }
                                _ => {}
                            }
                        }

                        processed_blocks.append(blocks);
                    }
                }
            }
        }

        // todo(ludo): yikes but good enough in the context of helium:
        // we only expect 1 block.
        let processed_block = processed_blocks[0].clone().0.unwrap();

        // Handle events
        let receipts = processed_block.tx_receipts;
        let metadata = processed_block.header;
        let block: StacksBlock = {
            let block_path = StacksChainState::get_block_path(
                &self.chain_state.blocks_path,
                &metadata.consensus_hash,
                &metadata.anchored_header.block_hash(),
            )
            .unwrap();
            StacksChainState::consensus_load(&block_path).unwrap()
        };

        let parent_index_hash = StacksBlockHeader::make_index_block_hash(
            &parent_consensus_hash,
            &block.header.parent_block,
        );

        let chain_tip = ChainTip {
            metadata,
            block,
            receipts,
        };

        self.event_dispatcher.process_chain_tip(
            &chain_tip,
            &parent_index_hash,
            Txid([0; 32]),
            vec![],
            None,
            parent_burn_block_hash,
            parent_burn_block_height,
            parent_burn_block_timestamp,
        );

        self.chain_tip = Some(chain_tip.clone());

        // Unset the `bootstraping_chain` flag.
        if self.bootstraping_chain {
            self.bootstraping_chain = false;
        }

        chain_tip
    }

    pub fn get_attachment_instances(
        &self,
        epoch_receipt: &StacksEpochReceipt,
        atlas_config: &AtlasConfig,
    ) -> HashSet<AttachmentInstance> {
        let mut attachments_instances = HashSet::new();
        for receipt in epoch_receipt.tx_receipts.iter() {
            if let TransactionOrigin::Stacks(ref transaction) = receipt.transaction {
                if let TransactionPayload::ContractCall(ref contract_call) = transaction.payload {
                    let contract_id = contract_call.to_clarity_contract_id();
                    if atlas_config.contracts.contains(&contract_id) {
                        for event in receipt.events.iter() {
                            if let StacksTransactionEvent::SmartContractEvent(ref event_data) =
                                event
                            {
                                let res = AttachmentInstance::try_new_from_value(
                                    &event_data.value,
                                    &contract_id,
                                    epoch_receipt.header.index_block_hash(),
                                    epoch_receipt.header.block_height,
                                    receipt.transaction.txid(),
                                );
                                if let Some(attachment_instance) = res {
                                    attachments_instances.insert(attachment_instance);
                                }
                            }
                        }
                    }
                }
            }
        }
        attachments_instances
    }

    /// Returns the Stacks address of the node
    pub fn get_address(&self) -> StacksAddress {
        self.keychain.get_address(self.config.is_mainnet())
    }

    /// Constructs and returns a LeaderKeyRegisterOp out of the provided params
    fn generate_leader_key_register_op(
        &mut self,
        vrf_public_key: VRFPublicKey,
        consensus_hash: &ConsensusHash,
    ) -> BlockstackOperationType {
        BlockstackOperationType::LeaderKeyRegister(LeaderKeyRegisterOp {
            public_key: vrf_public_key,
            memo: vec![],
            address: self.keychain.get_address(self.config.is_mainnet()),
            consensus_hash: consensus_hash.clone(),
            vtxindex: 0,
            txid: Txid([0u8; 32]),
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        })
    }

    /// Constructs and returns a LeaderBlockCommitOp out of the provided params
    fn generate_block_commit_op(
        &mut self,
        block_header_hash: BlockHeaderHash,
        burn_fee: u64,
        key: &RegisteredKey,
        burnchain_tip: &BurnchainTip,
        vrf_seed: VRFSeed,
    ) -> BlockstackOperationType {
        let winning_tx_vtindex = burnchain_tip.get_winning_tx_index().unwrap_or(0);

        let (parent_block_ptr, parent_vtxindex) = match self.bootstraping_chain {
            true => (0, 0), // parent_block_ptr and parent_vtxindex should both be 0 on block #1
            false => (
                burnchain_tip.block_snapshot.block_height as u32,
                winning_tx_vtindex as u16,
            ),
        };

        let burnchain = Burnchain::regtest(&self.config.get_burn_db_path());
        let commit_outs = if burnchain_tip.block_snapshot.block_height + 1
            < burnchain.pox_constants.sunset_end
            && !burnchain.is_in_prepare_phase(burnchain_tip.block_snapshot.block_height + 1)
        {
            RewardSetInfo::into_commit_outs(None, self.config.is_mainnet())
        } else {
            vec![StacksAddress::burn_address(self.config.is_mainnet())]
        };
        let burn_parent_modulus =
            (burnchain_tip.block_snapshot.block_height % BURN_BLOCK_MINED_AT_MODULUS) as u8;

        BlockstackOperationType::LeaderBlockCommit(LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash,
            burn_fee,
            input: (Txid([0; 32]), 0),
            apparent_sender: self.keychain.get_burnchain_signer(),
            key_block_ptr: key.block_height as u32,
            key_vtxindex: key.op_vtxindex as u16,
            memo: vec![],
            new_seed: vrf_seed,
            parent_block_ptr,
            parent_vtxindex,
            vtxindex: 0,
            txid: Txid([0u8; 32]),
            commit_outs,
            block_height: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
            burn_parent_modulus,
        })
    }

    // Constructs a coinbase transaction
    fn generate_coinbase_tx(&mut self, is_mainnet: bool) -> StacksTransaction {
        let mut tx_auth = self.keychain.get_transaction_auth().unwrap();
        tx_auth.set_origin_nonce(self.nonce);

        let version = if is_mainnet {
            TransactionVersion::Mainnet
        } else {
            TransactionVersion::Testnet
        };
        let mut tx = StacksTransaction::new(
            version,
            tx_auth,
            TransactionPayload::Coinbase(CoinbasePayload([0u8; 32])),
        );
        tx.chain_id = self.config.burnchain.chain_id;
        tx.anchor_mode = TransactionAnchorMode::OnChainOnly;
        let mut tx_signer = StacksTransactionSigner::new(&tx);
        self.keychain.sign_as_origin(&mut tx_signer);

        // Increment nonce
        self.nonce += 1;

        tx_signer.get_tx().unwrap()
    }
}
