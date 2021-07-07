use std::collections::hash_map::Entry;
use std::thread::sleep;
use std::time::Duration;
use std::{
    collections::{HashMap, HashSet},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    },
};

use async_h1::client;
use async_std::net::TcpStream;
use http_types::{Method, Request, Url};
use serde_json::json;

use stacks::burnchains::Txid;
use stacks::chainstate::coordinator::BlockEventDispatcher;
use stacks::chainstate::stacks::db::StacksHeaderInfo;
use stacks::chainstate::stacks::events::{
    FTEventType, NFTEventType, STXEventType, StacksTransactionEvent, StacksTransactionReceipt,
    TransactionOrigin,
};
use stacks::chainstate::stacks::StacksBlock;
use stacks::chainstate::stacks::{
    db::accounts::MinerReward, db::MinerRewardInfo, StacksTransaction,
};
use stacks::codec::StacksMessageCodec;
use stacks::core::mempool::{MemPoolDropReason, MemPoolEventDispatcher};
use stacks::net::atlas::{Attachment, AttachmentInstance};
use stacks::types::chainstate::{BurnchainHeaderHash, StacksAddress, StacksBlockId};
use stacks::util::hash::bytes_to_hex;
use stacks::vm::analysis::contract_interface_builder::build_contract_interface;
use stacks::vm::types::{AssetIdentifier, QualifiedContractIdentifier, Value};

use super::config::{EventKeyType, EventObserverConfig};
use super::node::ChainTip;
use stacks::chainstate::stacks::db::unconfirmed::ProcessedUnconfirmedState;

#[derive(Debug, Clone)]
struct EventObserver {
    endpoint: String,
    should_keep_running: Arc<AtomicBool>,
}

struct ReceiptPayloadInfo<'a> {
    txid: String,
    success: &'a str,
    raw_result: String,
    raw_tx: String,
    contract_interface_json: serde_json::Value,
}

const STATUS_RESP_TRUE: &str = "success";
const STATUS_RESP_NOT_COMMITTED: &str = "abort_by_response";
const STATUS_RESP_POST_CONDITION: &str = "abort_by_post_condition";

/// Update `serve()` in `neon_integrations.rs` with any new paths that need to be tested
pub const PATH_MICROBLOCK_SUBMIT: &str = "new_microblocks";
pub const PATH_MEMPOOL_TX_SUBMIT: &str = "new_mempool_tx";
pub const PATH_MEMPOOL_TX_DROP: &str = "drop_mempool_tx";
pub const PATH_BURN_BLOCK_SUBMIT: &str = "new_burn_block";
pub const PATH_BLOCK_PROCESSED: &str = "new_block";
pub const PATH_ATTACHMENT_PROCESSED: &str = "attachments/new";

impl EventObserver {
    fn send_payload(&self, payload: &serde_json::Value, path: &str) {
        let body = match serde_json::to_vec(&payload) {
            Ok(body) => body,
            Err(err) => {
                error!("Event dispatcher: serialization failed  - {:?}", err);
                return;
            }
        };

        let url = {
            let joined_components = match path.starts_with("/") {
                true => format!("{}{}", &self.endpoint, path),
                false => format!("{}/{}", &self.endpoint, path),
            };
            let url = format!("http://{}", joined_components);
            Url::parse(&url).expect(&format!(
                "Event dispatcher: unable to parse {} as a URL",
                url
            ))
        };

        let backoff = Duration::from_millis((1.0 * 1_000.0) as u64);

        loop {
            if !self.should_keep_running.load(Ordering::SeqCst) {
                info!("Terminating event observer");
                return;
            }

            let body = body.clone();
            let mut req = Request::new(Method::Post, url.clone());
            req.append_header("Content-Type", "application/json")
                .expect("Unable to set header");
            req.set_body(body);

            let response = async_std::task::block_on(async {
                let stream = match TcpStream::connect(self.endpoint.clone()).await {
                    Ok(stream) => stream,
                    Err(err) => {
                        println!("Event dispatcher: connection failed  - {:?}", err);
                        return None;
                    }
                };

                match client::connect(stream, req).await {
                    Ok(response) => Some(response),
                    Err(err) => {
                        println!("Event dispatcher: rpc invokation failed  - {:?}", err);
                        return None;
                    }
                }
            });

            if let Some(response) = response {
                if response.status().is_success() {
                    break;
                } else {
                    error!(
                        "Event dispatcher: POST {}/{} failed with error {:?}",
                        self.endpoint, &url, response
                    );
                }
            }
            sleep(backoff);
        }
    }

    fn make_new_mempool_txs_payload(transactions: Vec<StacksTransaction>) -> serde_json::Value {
        let raw_txs = transactions
            .into_iter()
            .map(|tx| {
                serde_json::Value::String(format!("0x{}", &bytes_to_hex(&tx.serialize_to_vec())))
            })
            .collect();

        serde_json::Value::Array(raw_txs)
    }

    fn make_new_burn_block_payload(
        burn_block: &BurnchainHeaderHash,
        burn_block_height: u64,
        rewards: Vec<(StacksAddress, u64)>,
        burns: u64,
        slot_holders: Vec<StacksAddress>,
    ) -> serde_json::Value {
        let reward_recipients = rewards
            .into_iter()
            .map(|(stx_addr, amt)| {
                json!({
                    "recipient": stx_addr.to_b58(),
                    "amt": amt,
                })
            })
            .collect();

        let reward_slot_holders = slot_holders
            .into_iter()
            .map(|stx_addr| json!(stx_addr.to_b58()))
            .collect();

        json!({
            "burn_block_hash": format!("0x{}", burn_block),
            "burn_block_height": burn_block_height,
            "reward_recipients": serde_json::Value::Array(reward_recipients),
            "reward_slot_holders": serde_json::Value::Array(reward_slot_holders),
            "burn_amount": burns
        })
    }

    /// Returns tuple of (txid, success, raw_result, raw_tx, contract_interface_json)
    fn generate_payload_info_for_receipt(receipt: &StacksTransactionReceipt) -> ReceiptPayloadInfo {
        let tx = &receipt.transaction;

        let success = match (receipt.post_condition_aborted, &receipt.result) {
            (false, Value::Response(response_data)) => {
                if response_data.committed {
                    STATUS_RESP_TRUE
                } else {
                    STATUS_RESP_NOT_COMMITTED
                }
            }
            (true, Value::Response(_)) => STATUS_RESP_POST_CONDITION,
            _ => unreachable!(), // Transaction results should always be a Value::Response type
        };

        let (txid, raw_tx) = match tx {
            TransactionOrigin::Burn(txid) => (txid.to_string(), "00".to_string()),
            TransactionOrigin::Stacks(ref tx) => {
                let txid = tx.txid().to_string();
                let bytes = tx.serialize_to_vec();
                (txid, bytes_to_hex(&bytes))
            }
        };

        let raw_result = {
            let bytes = receipt.result.serialize_to_vec();
            bytes_to_hex(&bytes)
        };
        let contract_interface_json = {
            match &receipt.contract_analysis {
                Some(analysis) => json!(build_contract_interface(analysis)),
                None => json!(null),
            }
        };
        ReceiptPayloadInfo {
            txid,
            success,
            raw_result,
            raw_tx,
            contract_interface_json,
        }
    }

    /// Returns json payload to send for new block or microblock event
    fn make_new_block_txs_payload(
        receipt: &StacksTransactionReceipt,
        tx_index: u32,
    ) -> serde_json::Value {
        let receipt_payload_info = EventObserver::generate_payload_info_for_receipt(receipt);

        json!({
            "txid": format!("0x{}", &receipt_payload_info.txid),
            "tx_index": tx_index,
            "status": receipt_payload_info.success,
            "raw_result": format!("0x{}", &receipt_payload_info.raw_result),
            "raw_tx": format!("0x{}", &receipt_payload_info.raw_tx),
            "contract_abi": receipt_payload_info.contract_interface_json,
            "execution_cost": receipt.execution_cost,
            "microblock_sequence": receipt.microblock_header.as_ref().map(|x| x.sequence),
            "microblock_hash": receipt.microblock_header.as_ref().map(|x| format!("0x{}", x.block_hash())),
            "microblock_parent_hash": receipt.microblock_header.as_ref().map(|x| format!("0x{}", x.prev_block)),
        })
    }

    fn make_new_attachment_payload(
        attachment: &(AttachmentInstance, Attachment),
    ) -> serde_json::Value {
        json!({
            "attachment_index": attachment.0.attachment_index,
            "index_block_hash": format!("0x{}", attachment.0.index_block_hash),
            "block_height": attachment.0.block_height,
            "content_hash": format!("0x{}", attachment.0.content_hash),
            "contract_id": format!("{}", attachment.0.contract_id),
            "metadata": format!("0x{}", attachment.0.metadata),
            "tx_id": format!("0x{}", attachment.0.tx_id),
            "content": format!("0x{}", bytes_to_hex(&attachment.1.content)),
        })
    }

    fn send_new_attachments(&self, payload: &serde_json::Value) {
        self.send_payload(payload, PATH_ATTACHMENT_PROCESSED);
    }

    fn send_new_mempool_txs(&self, payload: &serde_json::Value) {
        self.send_payload(payload, PATH_MEMPOOL_TX_SUBMIT);
    }

    /// Serializes new microblocks data into a JSON payload and sends it off to the correct path
    fn send_new_microblocks(
        &self,
        parent_index_block_hash: StacksBlockId,
        filtered_events: Vec<(usize, &(bool, Txid, &StacksTransactionEvent))>,
        serialized_txs: &Vec<serde_json::Value>,
        burn_block_hash: BurnchainHeaderHash,
        burn_block_height: u32,
        burn_block_timestamp: u64,
    ) {
        // Serialize events to JSON
        let serialized_events: Vec<serde_json::Value> = filtered_events
            .iter()
            .map(|(event_index, (committed, txid, event))| {
                event.json_serialize(*event_index, txid, *committed)
            })
            .collect();

        let payload = json!({
            "parent_index_block_hash": format!("0x{}", parent_index_block_hash),
            "events": serialized_events,
            "transactions": serialized_txs,
            "burn_block_hash": format!("0x{}", burn_block_hash),
            "burn_block_height": burn_block_height,
            "burn_block_timestamp": burn_block_timestamp,
        });

        self.send_payload(&payload, PATH_MICROBLOCK_SUBMIT);
    }

    fn send_dropped_mempool_txs(&self, payload: &serde_json::Value) {
        self.send_payload(payload, PATH_MEMPOOL_TX_DROP);
    }

    fn send_new_burn_block(&self, payload: &serde_json::Value) {
        self.send_payload(payload, PATH_BURN_BLOCK_SUBMIT);
    }

    fn send(
        &self,
        filtered_events: Vec<(usize, &(bool, Txid, &StacksTransactionEvent))>,
        chain_tip: &ChainTip,
        parent_index_hash: &StacksBlockId,
        boot_receipts: &Vec<StacksTransactionReceipt>,
        winner_txid: &Txid,
        mature_rewards: &serde_json::Value,
        parent_burn_block_hash: BurnchainHeaderHash,
        parent_burn_block_height: u32,
        parent_burn_block_timestamp: u64,
    ) {
        // Serialize events to JSON
        let serialized_events: Vec<serde_json::Value> = filtered_events
            .iter()
            .map(|(event_index, (committed, txid, event))| {
                event.json_serialize(*event_index, txid, *committed)
            })
            .collect();

        let mut tx_index: u32 = 0;
        let mut serialized_txs = vec![];

        for receipt in chain_tip.receipts.iter().chain(boot_receipts.iter()) {
            let payload = EventObserver::make_new_block_txs_payload(receipt, tx_index);
            serialized_txs.push(payload);
            tx_index += 1;
        }

        // Wrap events
        let payload = json!({
            "block_hash": format!("0x{}", chain_tip.block.block_hash()),
            "block_height": chain_tip.metadata.block_height,
            "burn_block_hash": format!("0x{}", chain_tip.metadata.burn_header_hash),
            "burn_block_height": chain_tip.metadata.burn_header_height,
            "miner_txid": format!("0x{}", winner_txid),
            "burn_block_time": chain_tip.metadata.burn_header_timestamp,
            "index_block_hash": format!("0x{}", chain_tip.metadata.index_block_hash()),
            "parent_block_hash": format!("0x{}", chain_tip.block.header.parent_block),
            "parent_index_block_hash": format!("0x{}", parent_index_hash),
            "parent_microblock": format!("0x{}", chain_tip.block.header.parent_microblock),
            "parent_microblock_sequence": chain_tip.block.header.parent_microblock_sequence,
            "matured_miner_rewards": mature_rewards.clone(),
            "events": serialized_events,
            "transactions": serialized_txs,
            "parent_burn_block_hash":  format!("0x{}", parent_burn_block_hash),
            "parent_burn_block_height": parent_burn_block_height,
            "parent_burn_block_timestamp": parent_burn_block_timestamp,
        });

        // Send payload
        self.send_payload(&payload, PATH_BLOCK_PROCESSED);
    }
}

#[derive(Clone)]
pub struct EventDispatcher {
    registered_observers: Vec<EventObserver>,
    contract_events_observers_lookup: HashMap<(QualifiedContractIdentifier, String), HashSet<u16>>,
    assets_observers_lookup: HashMap<AssetIdentifier, HashSet<u16>>,
    burn_block_observers_lookup: HashSet<u16>,
    mempool_observers_lookup: HashSet<u16>,
    microblock_observers_lookup: HashSet<u16>,
    stx_observers_lookup: HashSet<u16>,
    any_event_observers_lookup: HashSet<u16>,
    boot_receipts: Arc<Mutex<Option<Vec<StacksTransactionReceipt>>>>,
}

impl MemPoolEventDispatcher for EventDispatcher {
    fn mempool_txs_dropped(&self, txids: Vec<Txid>, reason: MemPoolDropReason) {
        if !txids.is_empty() {
            self.process_dropped_mempool_txs(txids, reason)
        }
    }
}

impl BlockEventDispatcher for EventDispatcher {
    fn announce_block(
        &self,
        block: StacksBlock,
        metadata: StacksHeaderInfo,
        receipts: Vec<StacksTransactionReceipt>,
        parent: &StacksBlockId,
        winner_txid: Txid,
        mature_rewards: Vec<MinerReward>,
        mature_rewards_info: Option<MinerRewardInfo>,
        parent_burn_block_hash: BurnchainHeaderHash,
        parent_burn_block_height: u32,
        parent_burn_block_timestamp: u64,
    ) {
        let chain_tip = ChainTip {
            metadata,
            block,
            receipts,
        };
        self.process_chain_tip(
            &chain_tip,
            parent,
            winner_txid,
            mature_rewards,
            mature_rewards_info,
            parent_burn_block_hash,
            parent_burn_block_height,
            parent_burn_block_timestamp,
        )
    }

    fn announce_burn_block(
        &self,
        burn_block: &BurnchainHeaderHash,
        burn_block_height: u64,
        rewards: Vec<(StacksAddress, u64)>,
        burns: u64,
        recipient_info: Vec<StacksAddress>,
    ) {
        self.process_burn_block(
            burn_block,
            burn_block_height,
            rewards,
            burns,
            recipient_info,
        )
    }

    fn dispatch_boot_receipts(&mut self, receipts: Vec<StacksTransactionReceipt>) {
        self.process_boot_receipts(receipts)
    }
}

impl EventDispatcher {
    pub fn new() -> EventDispatcher {
        EventDispatcher {
            registered_observers: vec![],
            contract_events_observers_lookup: HashMap::new(),
            assets_observers_lookup: HashMap::new(),
            stx_observers_lookup: HashSet::new(),
            any_event_observers_lookup: HashSet::new(),
            burn_block_observers_lookup: HashSet::new(),
            mempool_observers_lookup: HashSet::new(),
            microblock_observers_lookup: HashSet::new(),
            boot_receipts: Arc::new(Mutex::new(None)),
        }
    }

    pub fn process_burn_block(
        &self,
        burn_block: &BurnchainHeaderHash,
        burn_block_height: u64,
        rewards: Vec<(StacksAddress, u64)>,
        burns: u64,
        recipient_info: Vec<StacksAddress>,
    ) {
        // lazily assemble payload only if we have observers
        let interested_observers: Vec<_> = self
            .registered_observers
            .iter()
            .enumerate()
            .filter(|(obs_id, _observer)| {
                self.burn_block_observers_lookup.contains(&(*obs_id as u16))
                    || self.any_event_observers_lookup.contains(&(*obs_id as u16))
            })
            .collect();
        if interested_observers.len() < 1 {
            return;
        }

        let payload = EventObserver::make_new_burn_block_payload(
            burn_block,
            burn_block_height,
            rewards,
            burns,
            recipient_info,
        );

        for (_, observer) in interested_observers.iter() {
            observer.send_new_burn_block(&payload);
        }
    }

    /// Iterates through tx receipts, and then the events corresponding to each receipt to
    /// generate a dispatch matrix & event vector.
    ///
    /// # Returns
    /// - dispatch_matrix: a vector where each index corresponds to the hashset of event indexes
    ///     that each respective event observer is subscribed to
    /// - events: a vector of all events from all the tx receipts
    fn create_dispatch_matrix_and_event_vector<'a>(
        &self,
        receipts: &'a Vec<StacksTransactionReceipt>,
    ) -> (
        Vec<HashSet<usize>>,
        Vec<(bool, Txid, &'a StacksTransactionEvent)>,
    ) {
        let mut dispatch_matrix: Vec<HashSet<usize>> = self
            .registered_observers
            .iter()
            .map(|_| HashSet::new())
            .collect();
        let mut events: Vec<(bool, Txid, &StacksTransactionEvent)> = vec![];
        let mut i: usize = 0;

        for receipt in receipts {
            let tx_hash = receipt.transaction.txid();
            for event in receipt.events.iter() {
                match event {
                    StacksTransactionEvent::SmartContractEvent(event_data) => {
                        if let Some(observer_indexes) =
                            self.contract_events_observers_lookup.get(&event_data.key)
                        {
                            for o_i in observer_indexes {
                                dispatch_matrix[*o_i as usize].insert(i);
                            }
                        }
                    }
                    StacksTransactionEvent::STXEvent(STXEventType::STXTransferEvent(_))
                    | StacksTransactionEvent::STXEvent(STXEventType::STXMintEvent(_))
                    | StacksTransactionEvent::STXEvent(STXEventType::STXBurnEvent(_))
                    | StacksTransactionEvent::STXEvent(STXEventType::STXLockEvent(_)) => {
                        for o_i in &self.stx_observers_lookup {
                            dispatch_matrix[*o_i as usize].insert(i);
                        }
                    }
                    StacksTransactionEvent::NFTEvent(NFTEventType::NFTTransferEvent(
                        event_data,
                    )) => {
                        self.update_dispatch_matrix_if_observer_subscribed(
                            &event_data.asset_identifier,
                            i,
                            &mut dispatch_matrix,
                        );
                    }
                    StacksTransactionEvent::NFTEvent(NFTEventType::NFTMintEvent(event_data)) => {
                        self.update_dispatch_matrix_if_observer_subscribed(
                            &event_data.asset_identifier,
                            i,
                            &mut dispatch_matrix,
                        );
                    }
                    StacksTransactionEvent::NFTEvent(NFTEventType::NFTBurnEvent(event_data)) => {
                        self.update_dispatch_matrix_if_observer_subscribed(
                            &event_data.asset_identifier,
                            i,
                            &mut dispatch_matrix,
                        );
                    }
                    StacksTransactionEvent::FTEvent(FTEventType::FTTransferEvent(event_data)) => {
                        self.update_dispatch_matrix_if_observer_subscribed(
                            &event_data.asset_identifier,
                            i,
                            &mut dispatch_matrix,
                        );
                    }
                    StacksTransactionEvent::FTEvent(FTEventType::FTMintEvent(event_data)) => {
                        self.update_dispatch_matrix_if_observer_subscribed(
                            &event_data.asset_identifier,
                            i,
                            &mut dispatch_matrix,
                        );
                    }
                    StacksTransactionEvent::FTEvent(FTEventType::FTBurnEvent(event_data)) => {
                        self.update_dispatch_matrix_if_observer_subscribed(
                            &event_data.asset_identifier,
                            i,
                            &mut dispatch_matrix,
                        );
                    }
                }
                events.push((!receipt.post_condition_aborted, tx_hash, event));
                for o_i in &self.any_event_observers_lookup {
                    dispatch_matrix[*o_i as usize].insert(i);
                }
                i += 1;
            }
        }

        (dispatch_matrix, events)
    }

    pub fn process_chain_tip(
        &self,
        chain_tip: &ChainTip,
        parent_index_hash: &StacksBlockId,
        winner_txid: Txid,
        mature_rewards: Vec<MinerReward>,
        mature_rewards_info: Option<MinerRewardInfo>,
        parent_burn_block_hash: BurnchainHeaderHash,
        parent_burn_block_height: u32,
        parent_burn_block_timestamp: u64,
    ) {
        let boot_receipts = if chain_tip.metadata.block_height == 1 {
            let mut boot_receipts_result = self
                .boot_receipts
                .lock()
                .expect("Unexpected concurrent access to `boot_receipts` in the event dispatcher!");
            if let Some(val) = boot_receipts_result.take() {
                val
            } else {
                vec![]
            }
        } else {
            vec![]
        };
        let receipts = chain_tip
            .receipts
            .iter()
            .cloned()
            .chain(boot_receipts.iter().cloned())
            .collect();

        let (dispatch_matrix, events) = self.create_dispatch_matrix_and_event_vector(&receipts);

        if dispatch_matrix.len() > 0 {
            let mature_rewards_vec = if let Some(rewards_info) = mature_rewards_info {
                mature_rewards
                    .iter()
                    .map(|reward| {
                        json!({
                            "recipient": reward.address.to_string(),
                            "coinbase_amount": reward.coinbase.to_string(),
                            "tx_fees_anchored": reward.tx_fees_anchored.to_string(),
                            "tx_fees_streamed_confirmed": reward.tx_fees_streamed_confirmed.to_string(),
                            "tx_fees_streamed_produced": reward.tx_fees_streamed_produced.to_string(),
                            "from_stacks_block_hash": format!("0x{}", &rewards_info.from_stacks_block_hash),
                            "from_index_consensus_hash": format!("0x{}", StacksBlockId::new(&rewards_info.from_block_consensus_hash,
                                                                                            &rewards_info.from_stacks_block_hash)),
                        })
                    })
                    .collect()
            } else {
                vec![]
            };

            let mature_rewards = serde_json::Value::Array(mature_rewards_vec);

            for (observer_id, filtered_events_ids) in dispatch_matrix.iter().enumerate() {
                let filtered_events: Vec<_> = filtered_events_ids
                    .iter()
                    .map(|event_id| (*event_id, &events[*event_id]))
                    .collect();

                self.registered_observers[observer_id].send(
                    filtered_events,
                    chain_tip,
                    parent_index_hash,
                    &boot_receipts,
                    &winner_txid,
                    &mature_rewards,
                    parent_burn_block_hash,
                    parent_burn_block_height,
                    parent_burn_block_timestamp,
                );
            }
        }
    }

    /// Creates a list of observers that are interested in the new microblocks event,
    /// creates a mapping from observers to the event ids that are relevant to each, and then
    /// sends the event to each interested observer.
    pub fn process_new_microblocks(
        &self,
        parent_index_block_hash: StacksBlockId,
        processed_unconfirmed_state: ProcessedUnconfirmedState,
    ) {
        // lazily assemble payload only if we have observers
        let interested_observers: Vec<_> = self
            .registered_observers
            .iter()
            .enumerate()
            .filter(|(obs_id, _observer)| {
                self.microblock_observers_lookup.contains(&(*obs_id as u16))
                    || self.any_event_observers_lookup.contains(&(*obs_id as u16))
            })
            .collect();
        if interested_observers.len() < 1 {
            return;
        }
        let flattened_receipts = processed_unconfirmed_state
            .receipts
            .iter()
            .flat_map(|(_, _, r)| r.clone())
            .collect();
        let (dispatch_matrix, events) =
            self.create_dispatch_matrix_and_event_vector(&flattened_receipts);

        // Serialize receipts
        let mut tx_index;
        let mut serialized_txs = Vec::new();

        for (_, _, receipts) in processed_unconfirmed_state.receipts.iter() {
            tx_index = 0;
            for receipt in receipts.iter() {
                let payload = EventObserver::make_new_block_txs_payload(receipt, tx_index);
                serialized_txs.push(payload);
                tx_index += 1;
            }
        }

        for (obs_id, observer) in interested_observers.iter() {
            let filtered_events_ids = &dispatch_matrix[*obs_id];
            let filtered_events: Vec<_> = filtered_events_ids
                .iter()
                .map(|event_id| (*event_id, &events[*event_id]))
                .collect();

            observer.send_new_microblocks(
                parent_index_block_hash,
                filtered_events,
                &serialized_txs,
                processed_unconfirmed_state.burn_block_hash,
                processed_unconfirmed_state.burn_block_height,
                processed_unconfirmed_state.burn_block_timestamp,
            );
        }
    }

    pub fn process_new_mempool_txs(&self, txs: Vec<StacksTransaction>) {
        // lazily assemble payload only if we have observers
        let interested_observers: Vec<_> = self
            .registered_observers
            .iter()
            .enumerate()
            .filter(|(obs_id, _observer)| {
                self.mempool_observers_lookup.contains(&(*obs_id as u16))
                    || self.any_event_observers_lookup.contains(&(*obs_id as u16))
            })
            .collect();
        if interested_observers.len() < 1 {
            return;
        }

        let payload = EventObserver::make_new_mempool_txs_payload(txs);

        for (_, observer) in interested_observers.iter() {
            observer.send_new_mempool_txs(&payload);
        }
    }

    pub fn process_dropped_mempool_txs(&self, txs: Vec<Txid>, reason: MemPoolDropReason) {
        // lazily assemble payload only if we have observers
        let interested_observers: Vec<_> = self
            .registered_observers
            .iter()
            .enumerate()
            .filter(|(obs_id, _observer)| {
                self.mempool_observers_lookup.contains(&(*obs_id as u16))
                    || self.any_event_observers_lookup.contains(&(*obs_id as u16))
            })
            .collect();
        if interested_observers.len() < 1 {
            return;
        }

        let dropped_txids: Vec<_> = txs
            .into_iter()
            .map(|tx| serde_json::Value::String(format!("0x{}", &tx)))
            .collect();

        let payload = json!({
            "dropped_txids": serde_json::Value::Array(dropped_txids),
            "reason": reason.to_string(),
        });

        for (_, observer) in interested_observers.iter() {
            observer.send_dropped_mempool_txs(&payload);
        }
    }

    pub fn process_new_attachments(&self, attachments: &Vec<(AttachmentInstance, Attachment)>) {
        let interested_observers: Vec<_> = self.registered_observers.iter().enumerate().collect();
        if interested_observers.len() < 1 {
            return;
        }

        let mut serialized_attachments = vec![];
        for attachment in attachments.iter() {
            let payload = EventObserver::make_new_attachment_payload(attachment);
            serialized_attachments.push(payload);
        }

        for (_, observer) in interested_observers.iter() {
            observer.send_new_attachments(&json!(serialized_attachments));
        }
    }

    pub fn process_boot_receipts(&mut self, receipts: Vec<StacksTransactionReceipt>) {
        self.boot_receipts = Arc::new(Mutex::new(Some(receipts)));
    }

    fn update_dispatch_matrix_if_observer_subscribed(
        &self,
        asset_identifier: &AssetIdentifier,
        event_index: usize,
        dispatch_matrix: &mut Vec<HashSet<usize>>,
    ) {
        if let Some(observer_indexes) = self.assets_observers_lookup.get(asset_identifier) {
            for o_i in observer_indexes {
                dispatch_matrix[*o_i as usize].insert(event_index);
            }
        }
    }

    pub fn register_observer(
        &mut self,
        conf: &EventObserverConfig,
        should_keep_running: Arc<AtomicBool>,
    ) {
        info!("Registering event observer at: {}", conf.endpoint);
        let event_observer = EventObserver {
            endpoint: conf.endpoint.clone(),
            should_keep_running,
        };

        let observer_index = self.registered_observers.len() as u16;

        for event_key_type in conf.events_keys.iter() {
            match event_key_type {
                EventKeyType::SmartContractEvent(event_key) => {
                    match self
                        .contract_events_observers_lookup
                        .entry(event_key.clone())
                    {
                        Entry::Occupied(observer_indexes) => {
                            observer_indexes.into_mut().insert(observer_index);
                        }
                        Entry::Vacant(v) => {
                            let mut observer_indexes = HashSet::new();
                            observer_indexes.insert(observer_index);
                            v.insert(observer_indexes);
                        }
                    };
                }
                EventKeyType::BurnchainBlocks => {
                    self.burn_block_observers_lookup.insert(observer_index);
                }
                EventKeyType::MemPoolTransactions => {
                    self.mempool_observers_lookup.insert(observer_index);
                }
                EventKeyType::Microblocks => {
                    self.microblock_observers_lookup.insert(observer_index);
                }
                EventKeyType::STXEvent => {
                    self.stx_observers_lookup.insert(observer_index);
                }
                EventKeyType::AssetEvent(event_key) => {
                    match self.assets_observers_lookup.entry(event_key.clone()) {
                        Entry::Occupied(observer_indexes) => {
                            observer_indexes.into_mut().insert(observer_index);
                        }
                        Entry::Vacant(v) => {
                            let mut observer_indexes = HashSet::new();
                            observer_indexes.insert(observer_index);
                            v.insert(observer_indexes);
                        }
                    };
                }
                EventKeyType::AnyEvent => {
                    self.any_event_observers_lookup.insert(observer_index);
                }
            }
        }

        self.registered_observers.push(event_observer);
    }
}
