use std::cmp;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::sync_channel;
use std::sync::Arc;
use std::thread;

use ctrlc as termination;

use stacks::burnchains::bitcoin::address::BitcoinAddress;
use stacks::burnchains::bitcoin::address::BitcoinAddressType;
use stacks::burnchains::{Address, Burnchain};
use stacks::chainstate::burn::db::sortdb::SortitionDB;
use stacks::chainstate::coordinator::comm::{CoordinatorChannels, CoordinatorReceivers};
use stacks::chainstate::coordinator::{
    BlockEventDispatcher, ChainsCoordinator, CoordinatorCommunication,
};
use stacks::chainstate::stacks::db::{ChainStateBootData, StacksChainState};
use stacks::net::atlas::{AtlasConfig, Attachment};
use stx_genesis::GenesisData;

use crate::monitoring::start_serving_monitoring_metrics;
use crate::node::use_test_genesis_chainstate;
use crate::syncctl::PoxSyncWatchdog;
use crate::{
    node::{get_account_balances, get_account_lockups, get_names, get_namespaces},
    BitcoinRegtestController, BurnchainController, Config, EventDispatcher, Keychain,
    NeonGenesisNode,
};

use super::RunLoopCallbacks;

/// Coordinating a node running in neon mode.
#[cfg(test)]
pub struct RunLoop {
    config: Config,
    pub callbacks: RunLoopCallbacks,
    blocks_processed: std::sync::Arc<std::sync::atomic::AtomicU64>,
    microblocks_processed: std::sync::Arc<std::sync::atomic::AtomicU64>,
    coordinator_channels: Option<(CoordinatorReceivers, CoordinatorChannels)>,
}

#[cfg(not(test))]
pub struct RunLoop {
    config: Config,
    pub callbacks: RunLoopCallbacks,
    coordinator_channels: Option<(CoordinatorReceivers, CoordinatorChannels)>,
}

impl RunLoop {
    /// Sets up a runloop and node, given a config.
    #[cfg(not(test))]
    pub fn new(config: Config) -> Self {
        let channels = CoordinatorCommunication::instantiate();
        Self {
            config,
            coordinator_channels: Some(channels),
            callbacks: RunLoopCallbacks::new(),
        }
    }

    #[cfg(test)]
    pub fn new(config: Config) -> Self {
        let channels = CoordinatorCommunication::instantiate();
        Self {
            config,
            coordinator_channels: Some(channels),
            callbacks: RunLoopCallbacks::new(),
            blocks_processed: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
            microblocks_processed: std::sync::Arc::new(std::sync::atomic::AtomicU64::new(0)),
        }
    }

    pub fn get_coordinator_channel(&self) -> Option<CoordinatorChannels> {
        self.coordinator_channels.as_ref().map(|x| x.1.clone())
    }

    #[cfg(test)]
    pub fn get_blocks_processed_arc(&self) -> std::sync::Arc<std::sync::atomic::AtomicU64> {
        self.blocks_processed.clone()
    }

    #[cfg(not(test))]
    fn get_blocks_processed_arc(&self) {}

    #[cfg(test)]
    pub fn get_microblocks_processed_arc(&self) -> std::sync::Arc<std::sync::atomic::AtomicU64> {
        self.microblocks_processed.clone()
    }

    #[cfg(not(test))]
    fn get_microblocks_processed_arc(&self) {}

    #[cfg(test)]
    fn bump_blocks_processed(&self) {
        self.blocks_processed
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }

    #[cfg(not(test))]
    fn bump_blocks_processed(&self) {}

    /// Starts the testnet runloop.
    ///
    /// This function will block by looping infinitely.
    /// It will start the burnchain (separate thread), set-up a channel in
    /// charge of coordinating the new blocks coming from the burnchain and
    /// the nodes, taking turns on tenures.  
    pub fn start(&mut self, burnchain_opt: Option<Burnchain>, mut mine_start: u64) {
        let (coordinator_receivers, coordinator_senders) = self
            .coordinator_channels
            .take()
            .expect("Run loop already started, can only start once after initialization.");

        let should_keep_running = Arc::new(AtomicBool::new(true));
        let keep_running_writer = should_keep_running.clone();

        let install = termination::set_handler(move || {
            info!("Graceful termination request received, will complete the ongoing runloop cycles and terminate");
            keep_running_writer.store(false, Ordering::SeqCst);
        });
        if let Err(e) = install {
            error!("Error setting termination handler - {}", e);
        }

        // Initialize and start the burnchain.
        let mut burnchain = BitcoinRegtestController::with_burnchain(
            self.config.clone(),
            Some(coordinator_senders.clone()),
            burnchain_opt,
            Some(should_keep_running.clone()),
        );
        let pox_constants = burnchain.get_pox_constants();

        let is_miner = if self.config.node.miner {
            let keychain = Keychain::default(self.config.node.seed.clone());
            let node_address = Keychain::address_from_burnchain_signer(
                &keychain.get_burnchain_signer(),
                self.config.is_mainnet(),
            );
            let btc_addr = BitcoinAddress::from_bytes(
                self.config.burnchain.get_bitcoin_network().1,
                BitcoinAddressType::PublicKeyHash,
                &node_address.to_bytes(),
            )
            .unwrap();
            info!("Miner node: checking UTXOs at address: {}", btc_addr);

            match burnchain.create_wallet_if_dne() {
                Err(e) => warn!("Error when creating wallet: {:?}", e),
                _ => {}
            }

            let utxos =
                burnchain.get_utxos(&keychain.generate_op_signer().get_public_key(), 1, None, 0);
            if utxos.is_none() {
                if self.config.node.mock_mining {
                    info!("No UTXOs found, but configured to mock mine");
                    true
                } else {
                    error!("UTXOs not found - switching off mining, will run as a Follower node. If this is unexpected, please ensure that your bitcoind instance is indexing transactions for the address {} (importaddress)", btc_addr);
                    false
                }
            } else {
                info!("UTXOs found - will run as a Miner node");
                true
            }
        } else {
            info!("Will run as a Follower node");
            false
        };

        let burnchain_config = burnchain.get_burnchain();
        let mut target_burnchain_block_height = 1.max(burnchain_config.first_block_height);

        info!("Start syncing Bitcoin headers, feel free to grab a cup of coffee, this can take a while");
        match burnchain.start(Some(target_burnchain_block_height)) {
            Ok(_) => {}
            Err(e) => {
                error!("Burnchain controller stopped: {}", e);
                return;
            }
        };

        let mainnet = self.config.is_mainnet();
        let chainid = self.config.burnchain.chain_id;
        let block_limit = self.config.block_limit.clone();
        let initial_balances = self
            .config
            .initial_balances
            .iter()
            .map(|e| (e.address.clone(), e.amount))
            .collect();

        // setup dispatcher
        let mut event_dispatcher = EventDispatcher::new();
        for observer in self.config.events_observers.iter() {
            event_dispatcher.register_observer(observer, should_keep_running.clone());
        }

        let use_test_genesis_data = use_test_genesis_chainstate(&self.config);

        let mut atlas_config = AtlasConfig::default(false);
        let genesis_attachments = GenesisData::new(use_test_genesis_data)
            .read_name_zonefiles()
            .into_iter()
            .map(|z| Attachment::new(z.zonefile_content.as_bytes().to_vec()))
            .collect();
        atlas_config.genesis_attachments = Some(genesis_attachments);

        let mut coordinator_dispatcher = event_dispatcher.clone();

        let chainstate_path = self.config.get_chainstate_path_str();
        let coordinator_burnchain_config = burnchain_config.clone();

        let (attachments_tx, attachments_rx) = sync_channel(1);

        let mut boot_data = ChainStateBootData {
            initial_balances,
            post_flight_callback: None,
            first_burnchain_block_hash: coordinator_burnchain_config.first_block_hash,
            first_burnchain_block_height: coordinator_burnchain_config.first_block_height as u32,
            first_burnchain_block_timestamp: coordinator_burnchain_config.first_block_timestamp,
            pox_constants: coordinator_burnchain_config.pox_constants.clone(),
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

        let (chain_state_db, receipts) = StacksChainState::open_and_exec(
            mainnet,
            chainid,
            &chainstate_path,
            Some(&mut boot_data),
            block_limit,
        )
        .unwrap();
        coordinator_dispatcher.dispatch_boot_receipts(receipts);

        let atlas_config = AtlasConfig::default(mainnet);
        let moved_atlas_config = atlas_config.clone();

        let coordinator_thread_handle = thread::Builder::new()
            .name("chains-coordinator".to_string())
            .spawn(move || {
                ChainsCoordinator::run(
                    chain_state_db,
                    coordinator_burnchain_config,
                    attachments_tx,
                    &mut coordinator_dispatcher,
                    coordinator_receivers,
                    moved_atlas_config,
                );
            })
            .unwrap();

        // We announce a new burn block so that the chains coordinator
        // can resume prior work and handle eventual unprocessed sortitions
        // stored during a previous session.
        coordinator_senders.announce_new_burn_block();

        let mut burnchain_tip = burnchain
            .wait_for_sortitions(None)
            .expect("Unable to get burnchain tip");

        let chainstate_path = self.config.get_chainstate_path_str();
        let mut pox_watchdog = PoxSyncWatchdog::new(
            mainnet,
            chainid,
            chainstate_path,
            self.config.burnchain.poll_time_secs,
            self.config.connection_options.timeout,
            self.config.node.pox_sync_sample_secs,
            self.config.node.pox_sync_sample_secs == 0,
            should_keep_running.clone(),
        )
        .unwrap();

        // setup genesis
        let node = NeonGenesisNode::new(
            self.config.clone(),
            event_dispatcher,
            burnchain_config.clone(),
            Box::new(|_| {}),
        );
        let mut node = if is_miner {
            node.into_initialized_leader_node(
                burnchain_tip.clone(),
                self.get_blocks_processed_arc(),
                self.get_microblocks_processed_arc(),
                coordinator_senders.clone(),
                pox_watchdog.make_comms_handle(),
                attachments_rx,
                atlas_config,
                should_keep_running.clone(),
            )
        } else {
            node.into_initialized_node(
                burnchain_tip.clone(),
                self.get_blocks_processed_arc(),
                self.get_microblocks_processed_arc(),
                coordinator_senders.clone(),
                pox_watchdog.make_comms_handle(),
                attachments_rx,
                atlas_config,
                should_keep_running.clone(),
            )
        };

        // TODO (hack) instantiate the sortdb in the burnchain
        let sortdb = burnchain.sortdb_mut();
        let mut block_height = {
            let (stacks_ch, _) = SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn())
                .expect("BUG: failed to load canonical stacks chain tip hash");

            match SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &stacks_ch)
                .expect("BUG: failed to query sortition DB")
            {
                Some(sn) => burnchain_config.reward_cycle_to_block_height(
                    burnchain_config
                        .block_height_to_reward_cycle(sn.block_height)
                        .expect("BUG: snapshot preceeds first reward cycle"),
                ),
                None => {
                    let sn = SortitionDB::get_first_block_snapshot(&sortdb.conn())
                        .expect("BUG: failed to get first-ever block snapshot");

                    sn.block_height
                }
            }
        };

        // Start the runloop
        trace!("Begin run loop");
        self.bump_blocks_processed();

        let prometheus_bind = self.config.node.prometheus_bind.clone();
        if let Some(prometheus_bind) = prometheus_bind {
            thread::Builder::new()
                .name("prometheus".to_string())
                .spawn(move || {
                    start_serving_monitoring_metrics(prometheus_bind);
                })
                .unwrap();
        }

        let mut burnchain_height = block_height;
        let mut num_sortitions_in_last_cycle = 1;
        let mut learned_burnchain_height = false;

        // prepare to fetch the first reward cycle!
        target_burnchain_block_height = burnchain_height + pox_constants.reward_cycle_length as u64;

        debug!(
            "Begin main runloop starting a burnchain block {}",
            block_height
        );

        loop {
            // Orchestrating graceful termination
            if !should_keep_running.load(Ordering::SeqCst) {
                // The p2p thread relies on the same atomic_bool, it will
                // discontinue its execution after completing its ongoing runloop epoch.
                info!("Terminating p2p process");
                info!("Terminating relayer");
                info!("Terminating chains-coordinator");
                coordinator_senders.stop_chains_coordinator();

                coordinator_thread_handle.join().unwrap();
                node.relayer_thread_handle.join().unwrap();
                node.p2p_thread_handle.join().unwrap();

                info!("Exiting stacks-node");
                break;
            }

            // wait for the p2p state-machine to do at least one pass
            debug!("Wait until we reach steady-state before processing more burnchain blocks...");

            // wait until it's okay to process the next sortitions
            let ibd = match pox_watchdog.pox_sync_wait(
                &burnchain_config,
                &burnchain_tip,
                if learned_burnchain_height {
                    Some(burnchain_height)
                } else {
                    None
                },
                num_sortitions_in_last_cycle,
            ) {
                Ok(ibd) => ibd,
                Err(e) => {
                    debug!("Pox sync wait routine aborted: {:?}", e);
                    continue;
                }
            };
            // will recalculate this
            num_sortitions_in_last_cycle = 0;

            let (next_burnchain_tip, next_burnchain_height) =
                match burnchain.sync(Some(target_burnchain_block_height)) {
                    Ok(x) => x,
                    Err(e) => {
                        warn!("Burnchain controller stopped: {}", e);
                        continue;
                    }
                };

            target_burnchain_block_height = cmp::min(
                next_burnchain_height,
                target_burnchain_block_height + pox_constants.reward_cycle_length as u64,
            );

            // *now* we know the burnchain height
            learned_burnchain_height = true;
            burnchain_tip = next_burnchain_tip;
            burnchain_height = next_burnchain_height;

            let sortition_tip = &burnchain_tip.block_snapshot.sortition_id;
            let next_height = burnchain_tip.block_snapshot.block_height;

            info!(
                "Downloaded burnchain blocks up to height {}; new target height is {}; next_height = {}, block_height = {}",
                next_burnchain_height, target_burnchain_block_height, next_height, block_height
            );

            if next_height > block_height {
                debug!(
                    "New burnchain block height {} > {}",
                    next_height, block_height
                );

                let mut sort_count = 0;

                // first, let's process all blocks in (block_height, next_height]
                for block_to_process in (block_height + 1)..(next_height + 1) {
                    let block = {
                        let ic = burnchain.sortdb_ref().index_conn();
                        SortitionDB::get_ancestor_snapshot(&ic, block_to_process, sortition_tip)
                            .unwrap()
                            .expect("Failed to find block in fork processed by bitcoin indexer")
                    };
                    if block.sortition {
                        sort_count += 1;
                    }

                    let sortition_id = &block.sortition_id;

                    // Have the node process the new block, that can include, or not, a sortition.
                    node.process_burnchain_state(burnchain.sortdb_mut(), sortition_id, ibd);

                    // Now, tell the relayer to check if it won a sortition during this block,
                    //   and, if so, to process and advertize the block
                    //
                    // _this will block if the relayer's buffer is full_
                    if !node.relayer_sortition_notify() {
                        // relayer hung up, exit.
                        error!("Block relayer and miner hung up, exiting.");
                        return;
                    }
                }

                num_sortitions_in_last_cycle = sort_count;
                debug!(
                    "Synchronized burnchain up to block height {} from {} (chain tip height is {}); {} sortitions",
                    next_height, block_height, burnchain_height, num_sortitions_in_last_cycle;
                );

                block_height = next_height;
            } else if ibd {
                // drive block processing after we reach the burnchain tip.
                // we may have downloaded all the blocks already,
                // so we can't rely on the relayer alone to
                // drive it.
                coordinator_senders.announce_new_stacks_block();
            }

            if block_height >= burnchain_height && !ibd {
                let canonical_stacks_tip_height =
                    SortitionDB::get_canonical_burn_chain_tip(burnchain.sortdb_ref().conn())
                        .map(|snapshot| snapshot.canonical_stacks_tip_height)
                        .unwrap_or(0);
                if canonical_stacks_tip_height < mine_start {
                    info!(
                        "Synchronized full burnchain, but stacks tip height is {}, and we are trying to boot to {}, not mining until reaching chain tip",
                        canonical_stacks_tip_height,
                        mine_start
                    );
                } else {
                    // once we've synced to the chain tip once, don't apply this check again.
                    //  this prevents a possible corner case in the event of a PoX fork.
                    mine_start = 0;

                    // at tip, and not downloading. proceed to mine.
                    info!(
                        "Synchronized full burnchain up to height {}. Proceeding to mine blocks",
                        block_height
                    );
                    if !node.relayer_issue_tenure() {
                        // relayer hung up, exit.
                        error!("Block relayer and miner hung up, exiting.");
                        continue;
                    }
                }
            }
        }
    }
}
