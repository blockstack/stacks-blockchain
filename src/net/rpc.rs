/*
 copyright: (c) 2013-2020 by Blockstack PBC, a public benefit corporation.

 This file is part of Blockstack.

 Blockstack is free software. You may redistribute or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License or
 (at your option) any later version.

 Blockstack is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY, including without the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with Blockstack. If not, see <http://www.gnu.org/licenses/>.
*/

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::io;
use std::io::prelude::*;
use std::io::{Read, Seek, SeekFrom, Write};
use std::net::SocketAddr;
use std::{convert::TryFrom, fmt};

use rand::prelude::*;
use rand::thread_rng;
use rusqlite::{DatabaseName, NO_PARAMS};

use crate::codec::StacksMessageCodec;
use burnchains::Burnchain;
use burnchains::BurnchainView;
use burnchains::*;
use chainstate::burn::db::sortdb::SortitionDB;
use chainstate::burn::ConsensusHash;
use chainstate::stacks::db::blocks::CheckError;
use chainstate::stacks::db::{
    blocks::MINIMUM_TX_FEE_RATE_PER_BYTE, BlockStreamData, StacksChainState,
};
use chainstate::stacks::Error as chain_error;
use chainstate::stacks::*;
use clarity_vm::clarity::ClarityConnection;
use core::mempool::*;
use monitoring;
use net::atlas::{AtlasDB, Attachment, MAX_ATTACHMENT_INV_PAGES_PER_REQUEST};
use net::connection::ConnectionHttp;
use net::connection::ConnectionOptions;
use net::connection::ReplyHandleHttp;
use net::db::PeerDB;
use net::http::*;
use net::p2p::PeerMap;
use net::p2p::PeerNetwork;
use net::relay::Relayer;
use net::ClientError;
use net::Error as net_error;
use net::HttpRequestMetadata;
use net::HttpRequestType;
use net::HttpResponseMetadata;
use net::HttpResponseType;
use net::MicroblocksData;
use net::NeighborAddress;
use net::NeighborsData;
use net::PeerAddress;
use net::PeerHost;
use net::ProtocolFamily;
use net::StacksHttp;
use net::StacksHttpMessage;
use net::StacksMessageType;
use net::UnconfirmedTransactionResponse;
use net::UnconfirmedTransactionStatus;
use net::UrlString;
use net::HTTP_REQUEST_ID_RESERVED;
use net::MAX_NEIGHBORS_DATA_LEN;
use net::{
    AccountEntryResponse, AttachmentPage, CallReadOnlyResponse, ContractSrcResponse,
    GetAttachmentResponse, GetAttachmentsInvResponse, MapEntryResponse,
};
use net::{BlocksData, GetIsTraitImplementedResponse};
use net::{RPCNeighbor, RPCNeighborsInfo};
use net::{RPCPeerInfoData, RPCPoxInfoData};
use util::db::DBConn;
use util::db::Error as db_error;
use util::get_epoch_time_secs;
use util::hash::Hash160;
use util::hash::{hex_bytes, to_hex};
use vm::database::clarity_store::make_contract_hash_key;
use vm::types::TraitIdentifier;
use vm::{
    analysis::errors::CheckErrors,
    costs::{ExecutionCost, LimitedCostTracker},
    database::{
        clarity_store::ContractCommitment, ClarityDatabase, ClaritySerializable, STXBalance,
    },
    errors::Error as ClarityRuntimeError,
    errors::Error::Unchecked,
    errors::InterpreterError,
    types::{PrincipalData, QualifiedContractIdentifier, StandardPrincipalData},
    ClarityName, ContractName, SymbolicExpression, Value,
};

use crate::clarity_vm::database::marf::MarfedKV;
use crate::types::chainstate::BlockHeaderHash;
use crate::types::chainstate::{
    BurnchainHeaderHash, StacksAddress, StacksBlockHeader, StacksBlockId,
};
use crate::{
    chainstate::burn::operations::leader_block_commit::OUTPUTS_PER_COMMIT, types, util,
    util::hash::Sha256Sum, version_string,
};

use super::{RPCPoxCurrentCycleInfo, RPCPoxNextCycleInfo};

pub const STREAM_CHUNK_SIZE: u64 = 4096;

#[derive(Default)]
pub struct RPCHandlerArgs<'a> {
    pub exit_at_block_height: Option<&'a u64>,
    pub genesis_chainstate_hash: Sha256Sum,
    pub event_observer: Option<&'a dyn MemPoolEventDispatcher>,
}

pub struct ConversationHttp {
    connection: ConnectionHttp,
    conn_id: usize,
    timeout: u64,
    peer_host: PeerHost,
    outbound_url: Option<UrlString>,
    peer_addr: SocketAddr,
    keep_alive: bool,
    total_request_count: u64,     // number of messages taken from the inbox
    total_reply_count: u64,       // number of messages responsed to
    last_request_timestamp: u64, // absolute timestamp of the last time we received at least 1 byte in a request
    last_response_timestamp: u64, // absolute timestamp of the last time we sent at least 1 byte in a response
    connection_time: u64,         // when this converation was instantiated

    // ongoing block streams
    reply_streams: VecDeque<(
        ReplyHandleHttp,
        Option<(HttpChunkedTransferWriterState, BlockStreamData)>,
        bool,
    )>,

    // our outstanding request/response to the remote peer, if any
    pending_request: Option<ReplyHandleHttp>,
    pending_response: Option<HttpResponseType>,
    pending_error_response: Option<HttpResponseType>,
}

impl fmt::Display for ConversationHttp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "http:id={},request={:?}",
            self.conn_id,
            self.pending_request.is_some()
        )
    }
}

impl fmt::Debug for ConversationHttp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "http:id={},request={:?}",
            self.conn_id,
            self.pending_request.is_some()
        )
    }
}

impl RPCPeerInfoData {
    pub fn from_network(
        network: &PeerNetwork,
        chainstate: &StacksChainState,
        exit_at_block_height: &Option<&u64>,
        genesis_chainstate_hash: &Sha256Sum,
    ) -> RPCPeerInfoData {
        let server_version = version_string(
            "stacks-node",
            option_env!("STACKS_NODE_VERSION")
                .or(option_env!("CARGO_PKG_VERSION"))
                .unwrap_or("0.0.0.0"),
        );
        let (unconfirmed_tip, unconfirmed_seq) = match chainstate.unconfirmed_state {
            Some(ref unconfirmed) => {
                if unconfirmed.num_mined_txs() > 0 {
                    (
                        unconfirmed.unconfirmed_chain_tip.clone(),
                        unconfirmed.last_mblock_seq,
                    )
                } else {
                    (StacksBlockId([0x00; 32]), 0)
                }
            }
            None => (StacksBlockId([0x00; 32]), 0),
        };

        RPCPeerInfoData {
            peer_version: network.burnchain.peer_version,
            pox_consensus: network.burnchain_tip.consensus_hash.clone(),
            burn_block_height: network.chain_view.burn_block_height,
            stable_pox_consensus: network.chain_view_stable_consensus_hash.clone(),
            stable_burn_block_height: network.chain_view.burn_stable_block_height,
            server_version,
            network_id: network.local_peer.network_id,
            parent_network_id: network.local_peer.parent_network_id,
            stacks_tip_height: network.burnchain_tip.canonical_stacks_tip_height,
            stacks_tip: network.burnchain_tip.canonical_stacks_tip_hash.clone(),
            stacks_tip_consensus_hash: network
                .burnchain_tip
                .canonical_stacks_tip_consensus_hash
                .clone(),
            unanchored_tip: unconfirmed_tip,
            unanchored_seq: unconfirmed_seq,
            exit_at_block_height: exit_at_block_height.cloned(),
            genesis_chainstate_hash: genesis_chainstate_hash.clone(),
        }
    }
}

impl RPCPoxInfoData {
    pub fn from_db(
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        burnchain: &Burnchain,
    ) -> Result<RPCPoxInfoData, net_error> {
        let mainnet = chainstate.mainnet;
        let contract_identifier = util::boot::boot_code_id("pox", mainnet);
        let function = "get-pox-info";
        let cost_track = LimitedCostTracker::new_free();
        let sender = PrincipalData::Standard(StandardPrincipalData::transient());

        let data = chainstate
            .maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                clarity_tx.with_readonly_clarity_env(mainnet, sender, cost_track, |env| {
                    env.execute_contract(&contract_identifier, function, &vec![], true)
                })
            })
            .map_err(|_| net_error::NotFoundError)?;

        let res = match data {
            Some(Ok(res)) => res.expect_result_ok().expect_tuple(),
            _ => return Err(net_error::DBError(db_error::NotFoundError)),
        };

        let first_burnchain_block_height = res
            .get("first-burnchain-block-height")
            .expect(&format!("FATAL: no 'first-burnchain-block-height'"))
            .to_owned()
            .expect_u128() as u64;

        let min_stacking_increment_ustx = res
            .get("min-amount-ustx")
            .expect(&format!("FATAL: no 'min-amount-ustx'"))
            .to_owned()
            .expect_u128() as u64;

        let prepare_cycle_length = res
            .get("prepare-cycle-length")
            .expect(&format!("FATAL: no 'prepare-cycle-length'"))
            .to_owned()
            .expect_u128() as u64;

        let rejection_fraction = res
            .get("rejection-fraction")
            .expect(&format!("FATAL: no 'rejection-fraction'"))
            .to_owned()
            .expect_u128() as u64;

        let reward_cycle_id = res
            .get("reward-cycle-id")
            .expect(&format!("FATAL: no 'reward-cycle-id'"))
            .to_owned()
            .expect_u128() as u64;

        let reward_cycle_length = res
            .get("reward-cycle-length")
            .expect(&format!("FATAL: no 'reward-cycle-length'"))
            .to_owned()
            .expect_u128() as u64;

        let current_rejection_votes = res
            .get("current-rejection-votes")
            .expect(&format!("FATAL: no 'current-rejection-votes'"))
            .to_owned()
            .expect_u128() as u64;

        let total_liquid_supply_ustx = res
            .get("total-liquid-supply-ustx")
            .expect(&format!("FATAL: no 'total-liquid-supply-ustx'"))
            .to_owned()
            .expect_u128() as u64;

        let total_required = (total_liquid_supply_ustx as u128 / 100)
            .checked_mul(rejection_fraction as u128)
            .ok_or_else(|| net_error::DBError(db_error::Overflow))?
            as u64;

        let rejection_votes_left_required = total_required.saturating_sub(current_rejection_votes);

        let burnchain_tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn())?;

        let pox_consts = &burnchain.pox_constants;

        if prepare_cycle_length != pox_consts.prepare_length as u64 {
            error!(
                "PoX Constants in config mismatched with PoX contract constants: {} != {}",
                prepare_cycle_length, pox_consts.prepare_length
            );
            return Err(net_error::DBError(db_error::Corruption));
        }

        if reward_cycle_length != pox_consts.reward_cycle_length as u64 {
            error!(
                "PoX Constants in config mismatched with PoX contract constants: {} != {}",
                reward_cycle_length, pox_consts.reward_cycle_length
            );
            return Err(net_error::DBError(db_error::Corruption));
        }

        let effective_height = burnchain_tip.block_height - first_burnchain_block_height;
        let next_reward_cycle_in = reward_cycle_length - (effective_height % reward_cycle_length);

        let next_rewards_start = burnchain_tip.block_height + next_reward_cycle_in;
        let next_prepare_phase_start = next_rewards_start - prepare_cycle_length;

        let next_prepare_phase_in = i64::try_from(next_prepare_phase_start)
            .map_err(|_| net_error::ChainstateError("Burn block height overflowed i64".into()))?
            - i64::try_from(burnchain_tip.block_height).map_err(|_| {
                net_error::ChainstateError("Burn block height overflowed i64".into())
            })?;

        let cur_cycle_stacked_ustx =
            chainstate.get_total_ustx_stacked(&sortdb, tip, reward_cycle_id as u128)?;
        let next_cycle_stacked_ustx =
            chainstate.get_total_ustx_stacked(&sortdb, tip, reward_cycle_id as u128 + 1)?;

        let reward_slots = pox_consts.reward_slots() as u64;

        let cur_cycle_threshold = StacksChainState::get_threshold_from_participation(
            total_liquid_supply_ustx as u128,
            cur_cycle_stacked_ustx,
            reward_slots as u128,
        ) as u64;

        let next_threshold = StacksChainState::get_threshold_from_participation(
            total_liquid_supply_ustx as u128,
            next_cycle_stacked_ustx,
            reward_slots as u128,
        ) as u64;

        let pox_activation_threshold_ustx = (total_liquid_supply_ustx as u128)
            .checked_mul(pox_consts.pox_participation_threshold_pct as u128)
            .map(|x| x / 100)
            .ok_or_else(|| net_error::DBError(db_error::Overflow))?
            as u64;

        let cur_cycle_pox_active = sortdb.is_pox_active(burnchain, &burnchain_tip)?;

        Ok(RPCPoxInfoData {
            contract_id: util::boot::boot_code_id("pox", chainstate.mainnet).to_string(),
            pox_activation_threshold_ustx,
            first_burnchain_block_height,
            prepare_phase_block_length: prepare_cycle_length,
            reward_phase_block_length: reward_cycle_length - prepare_cycle_length,
            reward_slots,
            rejection_fraction,
            total_liquid_supply_ustx,
            current_cycle: RPCPoxCurrentCycleInfo {
                id: reward_cycle_id,
                min_threshold_ustx: cur_cycle_threshold,
                stacked_ustx: cur_cycle_stacked_ustx as u64,
                is_pox_active: cur_cycle_pox_active,
            },
            next_cycle: RPCPoxNextCycleInfo {
                id: reward_cycle_id + 1,
                min_threshold_ustx: next_threshold,
                min_increment_ustx: min_stacking_increment_ustx,
                stacked_ustx: next_cycle_stacked_ustx as u64,
                prepare_phase_start_block_height: next_prepare_phase_start,
                blocks_until_prepare_phase: next_prepare_phase_in,
                reward_phase_start_block_height: next_rewards_start,
                blocks_until_reward_phase: next_reward_cycle_in,
                ustx_until_pox_rejection: rejection_votes_left_required,
            },
            min_amount_ustx: next_threshold,
            prepare_cycle_length,
            reward_cycle_id,
            reward_cycle_length,
            rejection_votes_left_required,
            next_reward_cycle_in,
        })
    }
}

impl RPCNeighborsInfo {
    /// Load neighbor address information from the peer network
    pub fn from_p2p(
        network_id: u32,
        peers: &PeerMap,
        chain_view: &BurnchainView,
        peerdb: &PeerDB,
    ) -> Result<RPCNeighborsInfo, net_error> {
        let neighbor_sample = PeerDB::get_random_neighbors(
            peerdb.conn(),
            network_id,
            MAX_NEIGHBORS_DATA_LEN,
            chain_view.burn_block_height,
            false,
        )
        .map_err(net_error::DBError)?;

        let sample: Vec<RPCNeighbor> = neighbor_sample
            .into_iter()
            .map(|n| {
                RPCNeighbor::from_neighbor_key_and_pubkh(
                    n.addr.clone(),
                    Hash160::from_node_public_key(&n.public_key),
                    true,
                )
            })
            .collect();

        let mut inbound = vec![];
        let mut outbound = vec![];
        for (_, convo) in peers.iter() {
            let nk = convo.to_neighbor_key();
            let naddr = convo.to_neighbor_address();
            if convo.is_outbound() {
                outbound.push(RPCNeighbor::from_neighbor_key_and_pubkh(
                    nk,
                    naddr.public_key_hash,
                    convo.is_authenticated(),
                ));
            } else {
                inbound.push(RPCNeighbor::from_neighbor_key_and_pubkh(
                    nk,
                    naddr.public_key_hash,
                    convo.is_authenticated(),
                ));
            }
        }

        Ok(RPCNeighborsInfo {
            sample: sample,
            inbound: inbound,
            outbound: outbound,
        })
    }
}

impl ConversationHttp {
    pub fn new(
        peer_addr: SocketAddr,
        outbound_url: Option<UrlString>,
        peer_host: PeerHost,
        conn_opts: &ConnectionOptions,
        conn_id: usize,
    ) -> ConversationHttp {
        let mut stacks_http = StacksHttp::new(peer_addr.clone());
        stacks_http.maximum_call_argument_size = conn_opts.maximum_call_argument_size;
        ConversationHttp {
            connection: ConnectionHttp::new(stacks_http, conn_opts, None),
            conn_id: conn_id,
            timeout: conn_opts.timeout,
            reply_streams: VecDeque::new(),
            peer_addr: peer_addr,
            outbound_url: outbound_url,
            peer_host: peer_host,
            pending_request: None,
            pending_response: None,
            pending_error_response: None,
            keep_alive: true,
            total_request_count: 0,
            total_reply_count: 0,
            last_request_timestamp: 0,
            last_response_timestamp: 0,
            connection_time: get_epoch_time_secs(),
        }
    }

    /// How many ongoing requests do we have on this conversation?
    pub fn num_pending_outbound(&self) -> usize {
        self.reply_streams.len()
    }

    /// What's our outbound URL?
    pub fn get_url(&self) -> Option<&UrlString> {
        self.outbound_url.as_ref()
    }

    /// What's our peer IP address?
    pub fn get_peer_addr(&self) -> &SocketAddr {
        &self.peer_addr
    }

    /// Is a request in-progress?
    pub fn is_request_inflight(&self) -> bool {
        self.pending_request.is_some()
    }

    /// Start a HTTP request from this peer, and expect a response.
    /// Returns the request handle; does not set the handle into this connection.
    fn start_request(&mut self, req: HttpRequestType) -> Result<ReplyHandleHttp, net_error> {
        test_debug!(
            "{:?},id={}: Start HTTP request {:?}",
            &self.peer_host,
            self.conn_id,
            &req
        );
        let mut handle = self.connection.make_request_handle(
            HTTP_REQUEST_ID_RESERVED,
            get_epoch_time_secs() + self.timeout,
            self.conn_id,
        )?;
        let stacks_msg = StacksHttpMessage::Request(req);
        self.connection.send_message(&mut handle, &stacks_msg)?;
        Ok(handle)
    }

    /// Start a HTTP request from this peer, and expect a response.
    /// Non-blocking.
    /// Only one request in-flight is allowed.
    pub fn send_request(&mut self, req: HttpRequestType) -> Result<(), net_error> {
        if self.is_request_inflight() {
            test_debug!(
                "{:?},id={}: Request in progress still",
                &self.peer_host,
                self.conn_id
            );
            return Err(net_error::InProgress);
        }
        if self.pending_error_response.is_some() {
            test_debug!(
                "{:?},id={}: Error response is inflight",
                &self.peer_host,
                self.conn_id
            );
            return Err(net_error::InProgress);
        }

        let handle = self.start_request(req)?;

        self.pending_request = Some(handle);
        self.pending_response = None;
        Ok(())
    }

    /// Send a HTTP error response.
    /// Discontinues and disables sending a non-error response
    pub fn reply_error<W: Write>(
        &mut self,
        fd: &mut W,
        res: HttpResponseType,
    ) -> Result<(), net_error> {
        if self.is_request_inflight() || self.pending_response.is_some() {
            test_debug!(
                "{:?},id={}: Request or response is already in progress",
                &self.peer_host,
                self.conn_id
            );
            return Err(net_error::InProgress);
        }
        if self.pending_error_response.is_some() {
            // error already in-flight
            return Ok(());
        }

        res.send(&mut self.connection.protocol, fd)?;

        let reply = self.connection.make_relay_handle(self.conn_id)?;

        self.pending_error_response = Some(res);
        self.reply_streams.push_back((reply, None, false));
        Ok(())
    }

    /// Handle a GET peer info.
    /// The response will be synchronously written to the given fd (so use a fd that can buffer!)
    fn handle_getinfo<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        network: &PeerNetwork,
        chainstate: &StacksChainState,
        handler_args: &RPCHandlerArgs,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let pi = RPCPeerInfoData::from_network(
            network,
            chainstate,
            &handler_args.exit_at_block_height,
            &handler_args.genesis_chainstate_hash,
        );
        let response = HttpResponseType::PeerInfo(response_metadata, pi);
        // timer.observe_duration();
        response.send(http, fd)
    }

    /// Handle a GET pox info.
    /// The response will be synchronously written to the given fd (so use a fd that can buffer!)
    fn handle_getpoxinfo<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        burnchain: &Burnchain,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);

        match RPCPoxInfoData::from_db(sortdb, chainstate, tip, burnchain) {
            Ok(pi) => {
                let response = HttpResponseType::PoxInfo(response_metadata, pi);
                response.send(http, fd)
            }
            Err(net_error::NotFoundError) => {
                debug!("Chain tip not found during get PoX info: {:?}", req);
                let response = HttpResponseType::NotFound(
                    response_metadata,
                    "Failed to find chain tip".to_string(),
                );
                response.send(http, fd)
            }
            Err(e) => {
                warn!("Failed to get PoX info {:?}: {:?}", req, &e);
                let response = HttpResponseType::ServerError(
                    response_metadata,
                    "Failed to query peer info".to_string(),
                );
                response.send(http, fd)
            }
        }
    }

    fn handle_getattachmentsinv<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        atlasdb: &AtlasDB,
        index_block_hash: &StacksBlockId,
        pages_indexes: &HashSet<u32>,
        _options: &ConnectionOptions,
    ) -> Result<(), net_error> {
        // We are receiving a list of page indexes with a chain tip hash.
        // The amount of pages_indexes is capped by MAX_ATTACHMENT_INV_PAGES_PER_REQUEST (8)
        // Pages sizes are controlled by the constant ATTACHMENTS_INV_PAGE_SIZE (8), which
        // means that a `GET v2/attachments/inv` request can be requesting for a 64 bit vector
        // at once.
        // Since clients can be asking for non-consecutive pages indexes (1, 5_000, 10_000, ...),
        // we will be handling each page index separately.
        // We could also add the notion of "budget" so that a client could only get a limited number
        // of pages when they are spanning over many blocks.
        let response_metadata = HttpResponseMetadata::from(req);
        if pages_indexes.len() > MAX_ATTACHMENT_INV_PAGES_PER_REQUEST {
            let msg = format!(
                "Number of attachment inv pages is limited by {} per request",
                MAX_ATTACHMENT_INV_PAGES_PER_REQUEST
            );
            warn!("{}", msg);
            let response = HttpResponseType::NotFound(response_metadata, msg);
            response.send(http, fd)?;
            return Ok(());
        }
        if pages_indexes.len() == 0 {
            let msg = format!("Page indexes missing");
            warn!("{}", msg);
            let response = HttpResponseType::NotFound(response_metadata, msg.clone());
            response.send(http, fd)?;
            return Ok(());
        }

        let mut pages_indexes = pages_indexes.iter().map(|i| *i).collect::<Vec<u32>>();
        pages_indexes.sort();

        let mut pages = vec![];

        for page_index in pages_indexes.iter() {
            match atlasdb.get_attachments_available_at_page_index(*page_index, &index_block_hash) {
                Ok(inventory) => {
                    pages.push(AttachmentPage {
                        inventory,
                        index: *page_index,
                    });
                }
                Err(e) => {
                    let msg = format!("Unable to read Atlas DB - {}", e);
                    warn!("{}", msg);
                    let response = HttpResponseType::NotFound(response_metadata, msg);
                    return response.send(http, fd);
                }
            }
        }

        let content = GetAttachmentsInvResponse {
            block_id: index_block_hash.clone(),
            pages,
        };
        let response = HttpResponseType::GetAttachmentsInv(response_metadata, content);
        response.send(http, fd)
    }

    fn handle_getattachment<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        atlasdb: &mut AtlasDB,
        content_hash: Hash160,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        match atlasdb.find_attachment(&content_hash) {
            Ok(Some(attachment)) => {
                let content = GetAttachmentResponse { attachment };
                let response = HttpResponseType::GetAttachment(response_metadata, content);
                response.send(http, fd)
            }
            _ => {
                let msg = format!("Unable to find attachment");
                warn!("{}", msg);
                let response = HttpResponseType::NotFound(response_metadata, msg);
                response.send(http, fd)
            }
        }
    }

    /// Handle a GET neighbors
    /// The response will be synchronously written to the given fd (so use a fd that can buffer!)
    fn handle_getneighbors<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        network: &PeerNetwork,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let neighbor_data = RPCNeighborsInfo::from_p2p(
            network.local_peer.network_id,
            &network.peers,
            &network.chain_view,
            &network.peerdb,
        )?;
        let response = HttpResponseType::Neighbors(response_metadata, neighbor_data);
        response.send(http, fd)
    }

    /// Handle a not-found
    fn handle_notfound<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        response_metadata: HttpResponseMetadata,
        msg: String,
    ) -> Result<Option<BlockStreamData>, net_error> {
        let response = HttpResponseType::NotFound(response_metadata, msg);
        return response.send(http, fd).and_then(|_| Ok(None));
    }

    /// Handle a server error
    fn handle_server_error<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        response_metadata: HttpResponseMetadata,
        msg: String,
    ) -> Result<Option<BlockStreamData>, net_error> {
        // oops
        warn!("{}", &msg);
        let response = HttpResponseType::ServerError(response_metadata, msg);
        return response.send(http, fd).and_then(|_| Ok(None));
    }

    /// Handle a GET block.  Start streaming the reply.
    /// The response's preamble (but not the block data) will be synchronously written to the fd
    /// (so use a fd that can buffer!)
    /// Return a BlockStreamData struct for the block that we're sending, so we can continue to
    /// make progress sending it.
    fn handle_getblock<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        index_block_hash: &StacksBlockId,
        chainstate: &StacksChainState,
    ) -> Result<Option<BlockStreamData>, net_error> {
        monitoring::increment_stx_blocks_served_counter();
        let response_metadata = HttpResponseMetadata::from(req);

        // do we have this block?
        match StacksChainState::has_block_indexed(&chainstate.blocks_path, index_block_hash) {
            Ok(false) => {
                return ConversationHttp::handle_notfound(
                    http,
                    fd,
                    response_metadata,
                    format!("No such block {}", index_block_hash.to_hex()),
                );
            }
            Err(e) => {
                // nope -- error trying to check
                warn!("Failed to serve block {:?}: {:?}", req, &e);
                let response = HttpResponseType::ServerError(
                    response_metadata,
                    format!("Failed to query block {}", index_block_hash.to_hex()),
                );
                response.send(http, fd).and_then(|_| Ok(None))
            }
            Ok(true) => {
                // yup! start streaming it back
                let stream = BlockStreamData::new_block(index_block_hash.clone());
                let response = HttpResponseType::BlockStream(response_metadata);
                response.send(http, fd).and_then(|_| Ok(Some(stream)))
            }
        }
    }

    /// Handle a GET confirmed microblock stream, by _anchor block hash_.  Start streaming the reply.
    /// The response's preamble (but not the block data) will be synchronously written to the fd
    /// (so use a fd that can buffer!)
    /// Return a BlockStreamData struct for the block that we're sending, so we can continue to
    /// make progress sending it.
    fn handle_getmicroblocks_confirmed<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        index_anchor_block_hash: &StacksBlockId,
        chainstate: &StacksChainState,
    ) -> Result<Option<BlockStreamData>, net_error> {
        monitoring::increment_stx_confirmed_micro_blocks_served_counter();
        let response_metadata = HttpResponseMetadata::from(req);

        match chainstate.has_processed_microblocks(index_anchor_block_hash) {
            Ok(true) => {}
            Ok(false) => {
                return ConversationHttp::handle_notfound(
                    http,
                    fd,
                    response_metadata,
                    format!(
                        "No such confirmed microblock stream for anchor block {}",
                        &index_anchor_block_hash
                    ),
                );
            }
            Err(e) => {
                return ConversationHttp::handle_server_error(
                    http,
                    fd,
                    response_metadata,
                    format!(
                        "Failed to query confirmed microblock stream {:?}: {:?}",
                        req, &e
                    ),
                );
            }
        }

        match chainstate.get_confirmed_microblock_index_hash(index_anchor_block_hash) {
            Err(e) => {
                return ConversationHttp::handle_server_error(
                    http,
                    fd,
                    response_metadata,
                    format!(
                        "Failed to serve confirmed microblock stream {:?}: {:?}",
                        req, &e
                    ),
                );
            }
            Ok(None) => {
                return ConversationHttp::handle_notfound(
                    http,
                    fd,
                    response_metadata,
                    format!(
                        "No such confirmed microblock stream for anchor block {}",
                        &index_anchor_block_hash
                    ),
                );
            }
            Ok(Some(tail_index_microblock_hash)) => {
                let (response, stream_opt) = match BlockStreamData::new_microblock_confirmed(
                    chainstate,
                    tail_index_microblock_hash.clone(),
                ) {
                    Ok(stream) => (
                        HttpResponseType::MicroblockStream(response_metadata),
                        Some(stream),
                    ),
                    Err(chain_error::NoSuchBlockError) => (
                        HttpResponseType::NotFound(
                            response_metadata,
                            format!(
                                "No such confirmed microblock stream ending with {}",
                                tail_index_microblock_hash.to_hex()
                            ),
                        ),
                        None,
                    ),
                    Err(_e) => {
                        debug!(
                            "Failed to load confirmed microblock stream {}: {:?}",
                            &tail_index_microblock_hash, &_e
                        );
                        (
                            HttpResponseType::ServerError(
                                response_metadata,
                                format!(
                                    "Failed to query confirmed microblock stream {}",
                                    tail_index_microblock_hash.to_hex()
                                ),
                            ),
                            None,
                        )
                    }
                };
                response.send(http, fd).and_then(|_| Ok(stream_opt))
            }
        }
    }

    /// Handle a GET confirmed microblock stream, by last _index microblock hash_ in the stream.  Start streaming the reply.
    /// The response's preamble (but not the block data) will be synchronously written to the fd
    /// (so use a fd that can buffer!)
    /// Return a BlockStreamData struct for the block that we're sending, so we can continue to
    /// make progress sending it.
    fn handle_getmicroblocks_indexed<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        tail_index_microblock_hash: &StacksBlockId,
        chainstate: &StacksChainState,
    ) -> Result<Option<BlockStreamData>, net_error> {
        monitoring::increment_stx_micro_blocks_served_counter();
        let response_metadata = HttpResponseMetadata::from(req);

        // do we have this processed microblock stream?
        match StacksChainState::has_processed_microblocks_indexed(
            chainstate.db(),
            tail_index_microblock_hash,
        ) {
            Ok(false) => {
                // nope
                return ConversationHttp::handle_notfound(
                    http,
                    fd,
                    response_metadata,
                    format!(
                        "No such confirmed microblock stream ending with {}",
                        &tail_index_microblock_hash
                    ),
                );
            }
            Err(e) => {
                // nope
                return ConversationHttp::handle_server_error(
                    http,
                    fd,
                    response_metadata,
                    format!(
                        "Failed to serve confirmed microblock stream {:?}: {:?}",
                        req, &e
                    ),
                );
            }
            Ok(true) => {
                // yup! start streaming it back
                let (response, stream_opt) = match BlockStreamData::new_microblock_confirmed(
                    chainstate,
                    tail_index_microblock_hash.clone(),
                ) {
                    Ok(stream) => (
                        HttpResponseType::MicroblockStream(response_metadata),
                        Some(stream),
                    ),
                    Err(chain_error::NoSuchBlockError) => (
                        HttpResponseType::NotFound(
                            response_metadata,
                            format!(
                                "No such confirmed microblock stream ending with {}",
                                tail_index_microblock_hash.to_hex()
                            ),
                        ),
                        None,
                    ),
                    Err(_e) => {
                        debug!(
                            "Failed to load confirmed indexed microblock stream {}: {:?}",
                            &tail_index_microblock_hash, &_e
                        );
                        (
                            HttpResponseType::ServerError(
                                response_metadata,
                                format!(
                                    "Failed to query confirmed microblock stream {}",
                                    tail_index_microblock_hash.to_hex()
                                ),
                            ),
                            None,
                        )
                    }
                };
                response.send(http, fd).and_then(|_| Ok(stream_opt))
            }
        }
    }

    /// Handle a GET token transfer cost.  Reply the entire response.
    /// TODO: accurately estimate the cost/length fee for token transfers, based on mempool
    /// pressure.
    fn handle_token_transfer_cost<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);

        // todo -- need to actually estimate the cost / length for token transfers
        //   right now, it just uses the minimum.
        let fee = MINIMUM_TX_FEE_RATE_PER_BYTE;
        let response = HttpResponseType::TokenTransferCost(response_metadata, fee);
        response.send(http, fd).map(|_| ())
    }

    /// Handle a GET on an existing account, given the current chain tip.  Optionally supplies a
    /// MARF proof for each account detail loaded from the chain tip.
    fn handle_get_account_entry<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        account: &PrincipalData,
        with_proof: bool,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);

        let response =
            match chainstate.maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                clarity_tx.with_clarity_db_readonly(|clarity_db| {
                    let key = ClarityDatabase::make_key_for_account_balance(&account);
                    let burn_block_height = clarity_db.get_current_burnchain_block_height() as u64;
                    let (balance, balance_proof) = clarity_db
                        .get_with_proof::<STXBalance>(&key)
                        .map(|(a, b)| (a, format!("0x{}", b.to_hex())))
                        .unwrap_or_else(|| (STXBalance::zero(), "".into()));
                    let balance_proof = if with_proof {
                        Some(balance_proof)
                    } else {
                        None
                    };
                    let key = ClarityDatabase::make_key_for_account_nonce(&account);
                    let (nonce, nonce_proof) = clarity_db
                        .get_with_proof(&key)
                        .map(|(a, b)| (a, format!("0x{}", b.to_hex())))
                        .unwrap_or_else(|| (0, "".into()));
                    let nonce_proof = if with_proof { Some(nonce_proof) } else { None };

                    let unlocked = balance.get_available_balance_at_burn_block(burn_block_height);
                    let (locked, unlock_height) =
                        balance.get_locked_balance_at_burn_block(burn_block_height);

                    let balance = format!("0x{}", to_hex(&unlocked.to_be_bytes()));
                    let locked = format!("0x{}", to_hex(&locked.to_be_bytes()));

                    AccountEntryResponse {
                        balance,
                        locked,
                        unlock_height,
                        nonce,
                        balance_proof,
                        nonce_proof,
                    }
                })
            }) {
                Ok(Some(data)) => HttpResponseType::GetAccount(response_metadata, data),
                Ok(None) | Err(_) => {
                    HttpResponseType::NotFound(response_metadata, "Chain tip not found".into())
                }
            };

        response.send(http, fd).map(|_| ())
    }

    /// Handle a GET on a smart contract's data map, given the current chain tip.  Optionally
    /// supplies a MARF proof for the value.
    fn handle_get_map_entry<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        contract_addr: &StacksAddress,
        contract_name: &ContractName,
        map_name: &ClarityName,
        key: &Value,
        with_proof: bool,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let contract_identifier =
            QualifiedContractIdentifier::new(contract_addr.clone().into(), contract_name.clone());

        let response =
            match chainstate.maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                clarity_tx.with_clarity_db_readonly(|clarity_db| {
                    let key = ClarityDatabase::make_key_for_data_map_entry(
                        &contract_identifier,
                        map_name,
                        key,
                    );
                    let (value, marf_proof) = clarity_db
                        .get_with_proof::<Value>(&key)
                        .map(|(a, b)| (a, format!("0x{}", b.to_hex())))
                        .unwrap_or_else(|| {
                            test_debug!("No value for '{}' in {}", &key, tip);
                            (Value::none(), "".into())
                        });
                    let marf_proof = if with_proof {
                        test_debug!(
                            "Return a MARF proof of '{}' of {} bytes",
                            &key,
                            marf_proof.as_bytes().len()
                        );
                        Some(marf_proof)
                    } else {
                        None
                    };

                    let data = format!("0x{}", value.serialize());
                    MapEntryResponse { data, marf_proof }
                })
            }) {
                Ok(Some(data)) => HttpResponseType::GetMapEntry(response_metadata, data),
                Ok(None) | Err(_) => {
                    HttpResponseType::NotFound(response_metadata, "Chain tip not found".into())
                }
            };

        response.send(http, fd).map(|_| ())
    }

    /// Handle a POST to run a read-only function call with the given parameters on the given chain
    /// tip.  Returns the result of the function call.  Returns a CallReadOnlyResponse on success.
    fn handle_readonly_function_call<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        contract_addr: &StacksAddress,
        contract_name: &ContractName,
        function: &ClarityName,
        sender: &PrincipalData,
        args: &[Value],
        options: &ConnectionOptions,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let contract_identifier =
            QualifiedContractIdentifier::new(contract_addr.clone().into(), contract_name.clone());

        let args: Vec<_> = args
            .iter()
            .map(|x| SymbolicExpression::atom_value(x.clone()))
            .collect();
        let mainnet = chainstate.mainnet;
        let mut cost_limit = options.read_only_call_limit.clone();
        cost_limit.write_length = 0;
        cost_limit.write_count = 0;

        let data_opt_res =
            chainstate.maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                let cost_track = clarity_tx
                    .with_clarity_db_readonly(|clarity_db| {
                        LimitedCostTracker::new_mid_block(mainnet, cost_limit, clarity_db)
                    })
                    .map_err(|_| {
                        ClarityRuntimeError::from(InterpreterError::CostContractLoadFailure)
                    })?;

                clarity_tx.with_readonly_clarity_env(mainnet, sender.clone(), cost_track, |env| {
                    // we want to execute any function as long as no actual writes are made as
                    // opposed to be limited to purely calling `define-read-only` functions,
                    // so use `read_only = false`.  This broadens the number of functions that
                    // can be called, and also circumvents limitations on `define-read-only`
                    // functions that can not use `contrac-call?`, even when calling other
                    // read-only functions
                    env.execute_contract(&contract_identifier, function.as_str(), &args, false)
                })
            });

        let response = match data_opt_res {
            Ok(Some(Ok(data))) => HttpResponseType::CallReadOnlyFunction(
                response_metadata,
                CallReadOnlyResponse {
                    okay: true,
                    result: Some(format!("0x{}", data.serialize())),
                    cause: None,
                },
            ),
            Ok(Some(Err(e))) => match e {
                Unchecked(CheckErrors::CostBalanceExceeded(actual_cost, _))
                    if actual_cost.write_count > 0 =>
                {
                    HttpResponseType::CallReadOnlyFunction(
                        response_metadata,
                        CallReadOnlyResponse {
                            okay: false,
                            result: None,
                            cause: Some("NotReadOnly".to_string()),
                        },
                    )
                }
                _ => HttpResponseType::CallReadOnlyFunction(
                    response_metadata,
                    CallReadOnlyResponse {
                        okay: false,
                        result: None,
                        cause: Some(e.to_string()),
                    },
                ),
            },
            Ok(None) | Err(_) => {
                HttpResponseType::NotFound(response_metadata, "Chain tip not found".into())
            }
        };
        response.send(http, fd).map(|_| ())
    }

    /// Handle a GET to fetch a contract's source code, given the chain tip.  Optionally returns a
    /// MARF proof as well.
    fn handle_get_contract_src<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        contract_addr: &StacksAddress,
        contract_name: &ContractName,
        with_proof: bool,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let contract_identifier =
            QualifiedContractIdentifier::new(contract_addr.clone().into(), contract_name.clone());

        let response =
            match chainstate.maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                clarity_tx.with_clarity_db_readonly(|db| {
                    let source = db.get_contract_src(&contract_identifier)?;
                    let contract_commit_key = make_contract_hash_key(&contract_identifier);
                    let (contract_commit, proof) = db
                        .get_with_proof::<ContractCommitment>(&contract_commit_key)
                        .expect("BUG: obtained source, but couldn't get MARF proof.");
                    let marf_proof = if with_proof {
                        Some(proof.to_hex())
                    } else {
                        None
                    };
                    let publish_height = contract_commit.block_height;
                    Some(ContractSrcResponse {
                        source,
                        publish_height,
                        marf_proof,
                    })
                })
            }) {
                Ok(Some(Some(data))) => HttpResponseType::GetContractSrc(response_metadata, data),
                Ok(Some(None)) => HttpResponseType::NotFound(
                    response_metadata,
                    "No contract source data found".into(),
                ),
                Ok(None) | Err(_) => {
                    HttpResponseType::NotFound(response_metadata, "Chain tip not found".into())
                }
            };

        response.send(http, fd).map(|_| ())
    }

    /// Handle a GET to fetch whether or not a contract implements a certain trait
    fn handle_get_is_trait_implemented<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        contract_addr: &StacksAddress,
        contract_name: &ContractName,
        trait_id: &TraitIdentifier,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let contract_identifier =
            QualifiedContractIdentifier::new(contract_addr.clone().into(), contract_name.clone());

        let response =
            match chainstate.maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                clarity_tx.with_clarity_db_readonly(|db| {
                    let analysis = db.load_contract_analysis(&contract_identifier)?;
                    if analysis.implemented_traits.contains(trait_id) {
                        Some(GetIsTraitImplementedResponse {
                            is_implemented: true,
                        })
                    } else {
                        let trait_defining_contract =
                            db.load_contract_analysis(&trait_id.contract_identifier)?;
                        let trait_definition =
                            trait_defining_contract.get_defined_trait(&trait_id.name)?;
                        let is_implemented = analysis
                            .check_trait_compliance(trait_id, trait_definition)
                            .is_ok();
                        Some(GetIsTraitImplementedResponse { is_implemented })
                    }
                })
            }) {
                Ok(Some(Some(data))) => {
                    HttpResponseType::GetIsTraitImplemented(response_metadata, data)
                }
                Ok(Some(None)) => HttpResponseType::NotFound(
                    response_metadata,
                    "No contract analysis found or trait definition not found".into(),
                ),
                Ok(None) | Err(_) => {
                    HttpResponseType::NotFound(response_metadata, "Chain tip not found".into())
                }
            };

        response.send(http, fd).map(|_| ())
    }

    /// Handle a GET to fetch a contract's analysis data, given the chain tip.  Note that this isn't
    /// something that's anchored to the blockchain, and can be different across different versions
    /// of Stacks -- callers must trust the Stacks node to return correct analysis data.
    /// Callers who don't trust the Stacks node should just fetch the contract source
    /// code and analyze it offline.
    fn handle_get_contract_abi<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        tip: &StacksBlockId,
        contract_addr: &StacksAddress,
        contract_name: &ContractName,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let contract_identifier =
            QualifiedContractIdentifier::new(contract_addr.clone().into(), contract_name.clone());

        let response =
            match chainstate.maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                clarity_tx.with_analysis_db_readonly(|db| {
                    let contract = db.load_contract(&contract_identifier)?;
                    contract.contract_interface
                })
            }) {
                Ok(Some(Some(data))) => HttpResponseType::GetContractABI(response_metadata, data),
                Ok(Some(None)) => HttpResponseType::NotFound(
                    response_metadata,
                    "No contract interface data found".into(),
                ),
                Ok(None) | Err(_) => {
                    HttpResponseType::NotFound(response_metadata, "Chain tip not found".into())
                }
            };

        response.send(http, fd).map(|_| ())
    }

    /// Handle a GET unconfirmed microblock stream.  Start streaming the reply.
    /// The response's preamble (but not the block data) will be synchronously written to the fd
    /// (so use a fd that can buffer!)
    /// Return a BlockStreamData struct for the block that we're sending, so we can continue to
    /// make progress sending it.
    fn handle_getmicroblocks_unconfirmed<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        index_anchor_block_hash: &StacksBlockId,
        min_seq: u16,
        chainstate: &StacksChainState,
    ) -> Result<Option<BlockStreamData>, net_error> {
        let response_metadata = HttpResponseMetadata::from(req);

        // do we have this unconfirmed microblock stream?
        match chainstate.has_any_staging_microblock_indexed(index_anchor_block_hash, min_seq) {
            Ok(false) => {
                // nope
                let response = HttpResponseType::NotFound(
                    response_metadata,
                    format!(
                        "No such unconfirmed microblock stream for {} at or after {}",
                        index_anchor_block_hash.to_hex(),
                        min_seq
                    ),
                );
                response.send(http, fd).and_then(|_| Ok(None))
            }
            Err(e) => {
                // nope
                warn!(
                    "Failed to serve confirmed microblock stream {:?}: {:?}",
                    req, &e
                );
                let response = HttpResponseType::ServerError(
                    response_metadata,
                    format!(
                        "Failed to query unconfirmed microblock stream for {} at or after {}",
                        index_anchor_block_hash.to_hex(),
                        min_seq
                    ),
                );
                response.send(http, fd).and_then(|_| Ok(None))
            }
            Ok(true) => {
                // yup! start streaming it back
                let (response, stream_opt) = match BlockStreamData::new_microblock_unconfirmed(
                    chainstate,
                    index_anchor_block_hash.clone(),
                    min_seq,
                ) {
                    Ok(stream) => (
                        HttpResponseType::MicroblockStream(response_metadata),
                        Some(stream),
                    ),
                    Err(chain_error::NoSuchBlockError) => (
                        HttpResponseType::NotFound(
                            response_metadata,
                            format!(
                                "No such unconfirmed microblock stream starting with {}",
                                index_anchor_block_hash.to_hex()
                            ),
                        ),
                        None,
                    ),
                    Err(_e) => {
                        debug!(
                            "Failed to load unconfirmed microblock stream {}: {:?}",
                            &index_anchor_block_hash, &_e
                        );
                        (
                            HttpResponseType::ServerError(
                                response_metadata,
                                format!(
                                    "Failed to query unconfirmed microblock stream {}",
                                    index_anchor_block_hash.to_hex()
                                ),
                            ),
                            None,
                        )
                    }
                };
                response.send(http, fd).and_then(|_| Ok(stream_opt))
            }
        }
    }

    /// Handle a GET unconfirmed transaction.
    /// The response will be synchronously written to the fd.
    fn handle_gettransaction_unconfirmed<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        chainstate: &StacksChainState,
        mempool: &MemPoolDB,
        txid: &Txid,
    ) -> Result<(), net_error> {
        let response_metadata = HttpResponseMetadata::from(req);

        // present in the unconfirmed state?
        if let Some(ref unconfirmed) = chainstate.unconfirmed_state.as_ref() {
            if let Some((transaction, mblock_hash, seq)) =
                unconfirmed.get_unconfirmed_transaction(txid)
            {
                let response = HttpResponseType::UnconfirmedTransaction(
                    response_metadata,
                    UnconfirmedTransactionResponse {
                        status: UnconfirmedTransactionStatus::Microblock {
                            block_hash: mblock_hash,
                            seq: seq,
                        },
                        tx: to_hex(&transaction.serialize_to_vec()),
                    },
                );
                return response.send(http, fd).map(|_| ());
            }
        }

        // present in the mempool?
        if let Some(txinfo) = MemPoolDB::get_tx(mempool.conn(), txid)? {
            let response = HttpResponseType::UnconfirmedTransaction(
                response_metadata,
                UnconfirmedTransactionResponse {
                    status: UnconfirmedTransactionStatus::Mempool,
                    tx: to_hex(&txinfo.tx.serialize_to_vec()),
                },
            );
            return response.send(http, fd).map(|_| ());
        }

        // not found
        let response = HttpResponseType::NotFound(
            response_metadata,
            format!("No such unconfirmed transaction {}", txid),
        );
        return response.send(http, fd).map(|_| ());
    }

    /// Load up the canonical Stacks chain tip.  Note that this is subject to both burn chain block
    /// Stacks block availability -- different nodes with different partial replicas of the Stacks chain state
    /// will return different values here.
    /// tip_opt is given by the HTTP request as the optional query parameter for the chain tip
    /// hash.  It will be None if there was no paramter given.
    /// The order of chain tips this method prefers is as follows:
    /// * tip_opt, if it's Some(..),
    /// * the unconfirmed canonical stacks chain tip, if initialized
    /// * the confirmed canonical stacks chain tip
    fn handle_load_stacks_chain_tip<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        tip_opt: Option<&StacksBlockId>,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
    ) -> Result<Option<StacksBlockId>, net_error> {
        match tip_opt {
            Some(tip) => Ok(Some(*tip).clone()),
            None => match chainstate.get_stacks_chain_tip(sortdb)? {
                Some(tip) => Ok(Some(StacksBlockHeader::make_index_block_hash(
                    &tip.consensus_hash,
                    &tip.anchored_block_hash,
                ))),
                None => {
                    let response_metadata = HttpResponseMetadata::from(req);
                    warn!("Failed to load Stacks chain tip");
                    let response = HttpResponseType::ServerError(
                        response_metadata,
                        format!("Failed to load Stacks chain tip"),
                    );
                    response.send(http, fd).and_then(|_| Ok(None))
                }
            },
        }
    }

    fn handle_load_stacks_chain_tip_hashes<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        tip_opt: Option<&StacksBlockId>,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash)>, net_error> {
        match tip_opt {
            Some(tip) => match chainstate.get_block_header_hashes(&tip)? {
                Some((ch, bl)) => {
                    return Ok(Some((ch, bl)));
                }
                None => {}
            },
            None => match chainstate.get_stacks_chain_tip(sortdb)? {
                Some(tip) => {
                    return Ok(Some((tip.consensus_hash, tip.anchored_block_hash)));
                }
                None => {}
            },
        }
        let response_metadata = HttpResponseMetadata::from(req);
        warn!("Failed to load Stacks chain tip");
        let response = HttpResponseType::ServerError(
            response_metadata,
            format!("Failed to load Stacks chain tip"),
        );
        response.send(http, fd).and_then(|_| Ok(None))
    }

    /// Handle a transaction.  Directly submit it to the mempool so the client can see any
    /// rejection reasons up-front (different from how the peer network handles it).  Indicate
    /// whether or not the transaction was accepted (and thus needs to be forwarded) in the return
    /// value.
    fn handle_post_transaction<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        chainstate: &mut StacksChainState,
        consensus_hash: ConsensusHash,
        block_hash: BlockHeaderHash,
        mempool: &mut MemPoolDB,
        tx: StacksTransaction,
        atlasdb: &mut AtlasDB,
        attachment: Option<Attachment>,
        event_observer: Option<&dyn MemPoolEventDispatcher>,
    ) -> Result<bool, net_error> {
        let txid = tx.txid();
        let response_metadata = HttpResponseMetadata::from(req);
        let (response, accepted) = if mempool.has_tx(&txid) {
            (
                HttpResponseType::TransactionID(response_metadata, txid),
                false,
            )
        } else {
            match mempool.submit(
                chainstate,
                &consensus_hash,
                &block_hash,
                &tx,
                event_observer,
            ) {
                Ok(_) => (
                    HttpResponseType::TransactionID(response_metadata, txid),
                    true,
                ),
                Err(e) => (
                    HttpResponseType::BadRequestJSON(response_metadata, e.into_json(&txid)),
                    false,
                ),
            }
        };

        if let Some(ref attachment) = attachment {
            if let TransactionPayload::ContractCall(ref contract_call) = tx.payload {
                if atlasdb
                    .should_keep_attachment(&contract_call.to_clarity_contract_id(), &attachment)
                {
                    atlasdb
                        .insert_uninstantiated_attachment(attachment)
                        .map_err(|e| net_error::DBError(e))?;
                }
            }
        }

        response.send(http, fd).and_then(|_| Ok(accepted))
    }

    /// Handle a block.  Directly submit a Stacks block to this node's chain state.
    /// Indicate whether or not the block was accepted (i.e. it was new, and valid)
    fn handle_post_block<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        block: &StacksBlock,
    ) -> Result<bool, net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        // is this a consensus hash we recognize?
        let (response, accepted) =
            match SortitionDB::get_sortition_id_by_consensus(&sortdb.conn(), consensus_hash) {
                Ok(Some(_)) => {
                    // we recognize this consensus hash
                    let ic = sortdb.index_conn();
                    match Relayer::process_new_anchored_block(
                        &ic,
                        chainstate,
                        consensus_hash,
                        block,
                        0,
                    ) {
                        Ok(true) => {
                            debug!(
                                "Accepted Stacks block {}/{}",
                                consensus_hash,
                                &block.block_hash()
                            );
                            (
                                HttpResponseType::StacksBlockAccepted(
                                    response_metadata,
                                    StacksBlockHeader::make_index_block_hash(
                                        consensus_hash,
                                        &block.block_hash(),
                                    ),
                                    true,
                                ),
                                true,
                            )
                        }
                        Ok(false) => {
                            debug!(
                                "Did not accept Stacks block {}/{}",
                                consensus_hash,
                                &block.block_hash()
                            );
                            (
                                HttpResponseType::StacksBlockAccepted(
                                    response_metadata,
                                    StacksBlockHeader::make_index_block_hash(
                                        consensus_hash,
                                        &block.block_hash(),
                                    ),
                                    false,
                                ),
                                false,
                            )
                        }
                        Err(e) => {
                            error!(
                                "Failed to process anchored block {}/{}: {:?}",
                                consensus_hash,
                                &block.block_hash(),
                                &e
                            );
                            (
                                HttpResponseType::ServerError(
                                    response_metadata,
                                    format!(
                                        "Failed to process anchored block {}/{}: {:?}",
                                        consensus_hash,
                                        &block.block_hash(),
                                        &e
                                    ),
                                ),
                                false,
                            )
                        }
                    }
                }
                Ok(None) => {
                    debug!(
                        "Unrecognized consensus hash {} for block {}",
                        consensus_hash,
                        &block.block_hash()
                    );
                    (
                        HttpResponseType::NotFound(
                            response_metadata,
                            format!("No such consensus hash '{}'", consensus_hash),
                        ),
                        false,
                    )
                }
                Err(e) => {
                    error!(
                        "Failed to query sortition ID by consensus '{}'",
                        consensus_hash
                    );
                    (
                        HttpResponseType::ServerError(
                            response_metadata,
                            format!(
                                "Failed to query sortition ID for consensus hash '{}': {:?}",
                                consensus_hash, &e
                            ),
                        ),
                        false,
                    )
                }
            };

        response.send(http, fd).and_then(|_| Ok(accepted))
    }

    /// Handle a microblock.  Directly submit it to the microblock store so the client can see any
    /// rejection reasons up-front (different from how the peer network handles it).  Indicate
    /// whether or not the microblock was accepted (and thus needs to be forwarded) in the return
    /// value.
    fn handle_post_microblock<W: Write>(
        http: &mut StacksHttp,
        fd: &mut W,
        req: &HttpRequestType,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
        chainstate: &mut StacksChainState,
        microblock: &StacksMicroblock,
    ) -> Result<bool, net_error> {
        let response_metadata = HttpResponseMetadata::from(req);
        let (response, accepted) =
            match chainstate.preprocess_streamed_microblock(consensus_hash, block_hash, microblock)
            {
                Ok(accepted) => {
                    if accepted {
                        debug!(
                            "Accepted uploaded microblock {}/{}-{}",
                            &consensus_hash,
                            &block_hash,
                            &microblock.block_hash()
                        );
                    } else {
                        debug!(
                            "Did not accept microblock {}/{}-{}",
                            &consensus_hash,
                            &block_hash,
                            &microblock.block_hash()
                        );
                    }

                    (
                        HttpResponseType::MicroblockHash(
                            response_metadata,
                            microblock.block_hash(),
                        ),
                        accepted,
                    )
                }
                Err(e) => (
                    HttpResponseType::BadRequestJSON(response_metadata, e.into_json()),
                    false,
                ),
            };

        response.send(http, fd).and_then(|_| Ok(accepted))
    }

    /// Handle an external HTTP request.
    /// Some requests, such as those for blocks, will create new reply streams.  This method adds
    /// those new streams into the `reply_streams` set.
    /// Returns a StacksMessageType option -- it's Some(...) if we need to forward a message to the
    /// peer network (like a transaction or a block or microblock)
    pub fn handle_request(
        &mut self,
        req: HttpRequestType,
        network: &mut PeerNetwork,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        mempool: &mut MemPoolDB,
        handler_opts: &RPCHandlerArgs,
    ) -> Result<Option<StacksMessageType>, net_error> {
        let mut reply = self.connection.make_relay_handle(self.conn_id)?;
        let keep_alive = req.metadata().keep_alive;
        let mut ret = None;

        let stream_opt = match req {
            HttpRequestType::GetInfo(ref _md) => {
                ConversationHttp::handle_getinfo(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    network,
                    chainstate,
                    handler_opts,
                )?;
                None
            }
            HttpRequestType::GetPoxInfo(ref _md, ref tip_opt) => {
                if let Some(tip) = ConversationHttp::handle_load_stacks_chain_tip(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    tip_opt.as_ref(),
                    sortdb,
                    chainstate,
                )? {
                    ConversationHttp::handle_getpoxinfo(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        sortdb,
                        chainstate,
                        &tip,
                        &network.burnchain,
                    )?;
                }
                None
            }
            HttpRequestType::GetNeighbors(ref _md) => {
                ConversationHttp::handle_getneighbors(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    network,
                )?;
                None
            }
            HttpRequestType::GetBlock(ref _md, ref index_block_hash) => {
                ConversationHttp::handle_getblock(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    index_block_hash,
                    chainstate,
                )?
            }
            HttpRequestType::GetMicroblocksIndexed(ref _md, ref index_head_hash) => {
                ConversationHttp::handle_getmicroblocks_indexed(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    index_head_hash,
                    chainstate,
                )?
            }
            HttpRequestType::GetMicroblocksConfirmed(ref _md, ref anchor_index_block_hash) => {
                ConversationHttp::handle_getmicroblocks_confirmed(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    anchor_index_block_hash,
                    chainstate,
                )?
            }
            HttpRequestType::GetMicroblocksUnconfirmed(
                ref _md,
                ref index_anchor_block_hash,
                ref min_seq,
            ) => ConversationHttp::handle_getmicroblocks_unconfirmed(
                &mut self.connection.protocol,
                &mut reply,
                &req,
                index_anchor_block_hash,
                *min_seq,
                chainstate,
            )?,
            HttpRequestType::GetTransactionUnconfirmed(ref _md, ref txid) => {
                ConversationHttp::handle_gettransaction_unconfirmed(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    chainstate,
                    mempool,
                    txid,
                )?;
                None
            }
            HttpRequestType::GetAccount(ref _md, ref principal, ref tip_opt, ref with_proof) => {
                if let Some(tip) = ConversationHttp::handle_load_stacks_chain_tip(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    tip_opt.as_ref(),
                    sortdb,
                    chainstate,
                )? {
                    ConversationHttp::handle_get_account_entry(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        sortdb,
                        chainstate,
                        &tip,
                        principal,
                        *with_proof,
                    )?;
                }
                None
            }
            HttpRequestType::GetMapEntry(
                ref _md,
                ref contract_addr,
                ref contract_name,
                ref map_name,
                ref key,
                ref tip_opt,
                ref with_proof,
            ) => {
                if let Some(tip) = ConversationHttp::handle_load_stacks_chain_tip(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    tip_opt.as_ref(),
                    sortdb,
                    chainstate,
                )? {
                    ConversationHttp::handle_get_map_entry(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        sortdb,
                        chainstate,
                        &tip,
                        contract_addr,
                        contract_name,
                        map_name,
                        key,
                        *with_proof,
                    )?;
                }
                None
            }
            HttpRequestType::GetTransferCost(ref _md) => {
                ConversationHttp::handle_token_transfer_cost(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                )?;
                None
            }
            HttpRequestType::GetContractABI(
                ref _md,
                ref contract_addr,
                ref contract_name,
                ref tip_opt,
            ) => {
                if let Some(tip) = ConversationHttp::handle_load_stacks_chain_tip(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    tip_opt.as_ref(),
                    sortdb,
                    chainstate,
                )? {
                    ConversationHttp::handle_get_contract_abi(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        sortdb,
                        chainstate,
                        &tip,
                        contract_addr,
                        contract_name,
                    )?;
                }
                None
            }
            HttpRequestType::CallReadOnlyFunction(
                ref _md,
                ref ctrct_addr,
                ref ctrct_name,
                ref as_sender,
                ref func_name,
                ref args,
                ref tip_opt,
            ) => {
                if let Some(tip) = ConversationHttp::handle_load_stacks_chain_tip(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    tip_opt.as_ref(),
                    sortdb,
                    chainstate,
                )? {
                    ConversationHttp::handle_readonly_function_call(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        sortdb,
                        chainstate,
                        &tip,
                        ctrct_addr,
                        ctrct_name,
                        func_name,
                        as_sender,
                        args,
                        &self.connection.options,
                    )?;
                }
                None
            }
            HttpRequestType::GetContractSrc(
                ref _md,
                ref contract_addr,
                ref contract_name,
                ref tip_opt,
                ref with_proof,
            ) => {
                if let Some(tip) = ConversationHttp::handle_load_stacks_chain_tip(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    tip_opt.as_ref(),
                    sortdb,
                    chainstate,
                )? {
                    ConversationHttp::handle_get_contract_src(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        sortdb,
                        chainstate,
                        &tip,
                        contract_addr,
                        contract_name,
                        *with_proof,
                    )?;
                }
                None
            }
            HttpRequestType::PostTransaction(ref _md, ref tx, ref attachment) => {
                match chainstate.get_stacks_chain_tip(sortdb)? {
                    Some(tip) => {
                        let accepted = ConversationHttp::handle_post_transaction(
                            &mut self.connection.protocol,
                            &mut reply,
                            &req,
                            chainstate,
                            tip.consensus_hash,
                            tip.anchored_block_hash,
                            mempool,
                            tx.clone(),
                            &mut network.atlasdb,
                            attachment.clone(),
                            handler_opts.event_observer.as_deref(),
                        )?;
                        if accepted {
                            // forward to peer network
                            ret = Some(StacksMessageType::Transaction(tx.clone()));
                        }
                    }
                    None => {
                        let response_metadata = HttpResponseMetadata::from(&req);
                        warn!("Failed to load Stacks chain tip");
                        let response = HttpResponseType::ServerError(
                            response_metadata,
                            format!("Failed to load Stacks chain tip"),
                        );
                        response.send(&mut self.connection.protocol, &mut reply)?;
                    }
                }
                None
            }
            HttpRequestType::GetAttachment(ref _md, ref content_hash) => {
                ConversationHttp::handle_getattachment(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    &mut network.atlasdb,
                    content_hash.clone(),
                )?;
                None
            }
            HttpRequestType::GetAttachmentsInv(
                ref _md,
                ref index_block_hash,
                ref pages_indexes,
            ) => {
                ConversationHttp::handle_getattachmentsinv(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    &mut network.atlasdb,
                    &index_block_hash,
                    pages_indexes,
                    &self.connection.options,
                )?;
                None
            }
            HttpRequestType::PostBlock(ref _md, ref consensus_hash, ref block) => {
                let accepted = ConversationHttp::handle_post_block(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    sortdb,
                    chainstate,
                    consensus_hash,
                    block,
                )?;
                if accepted {
                    // inform the peer network so it can announce its presence
                    ret = Some(StacksMessageType::Blocks(BlocksData {
                        blocks: vec![(consensus_hash.clone(), block.clone())],
                    }));
                }
                None
            }
            HttpRequestType::PostMicroblock(ref _md, ref mblock, ref tip_opt) => {
                if let Some((consensus_hash, block_hash)) =
                    ConversationHttp::handle_load_stacks_chain_tip_hashes(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        tip_opt.as_ref(),
                        sortdb,
                        chainstate,
                    )?
                {
                    let accepted = ConversationHttp::handle_post_microblock(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        &consensus_hash,
                        &block_hash,
                        chainstate,
                        mblock,
                    )?;
                    if accepted {
                        // forward to peer network
                        let tip =
                            StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_hash);
                        ret = Some(StacksMessageType::Microblocks(MicroblocksData {
                            index_anchor_block: tip,
                            microblocks: vec![(*mblock).clone()],
                        }));
                    }
                }
                None
            }
            HttpRequestType::OptionsPreflight(ref _md, ref _path) => {
                let response_metadata = HttpResponseMetadata::from(&req);
                let response = HttpResponseType::OptionsPreflight(response_metadata);
                response
                    .send(&mut self.connection.protocol, &mut reply)
                    .map(|_| ())?;
                None
            }
            HttpRequestType::GetIsTraitImplemented(
                ref _md,
                ref contract_addr,
                ref contract_name,
                ref trait_id,
                ref tip_opt,
            ) => {
                if let Some(tip) = ConversationHttp::handle_load_stacks_chain_tip(
                    &mut self.connection.protocol,
                    &mut reply,
                    &req,
                    tip_opt.as_ref(),
                    sortdb,
                    chainstate,
                )? {
                    ConversationHttp::handle_get_is_trait_implemented(
                        &mut self.connection.protocol,
                        &mut reply,
                        &req,
                        sortdb,
                        chainstate,
                        &tip,
                        contract_addr,
                        contract_name,
                        trait_id,
                    )?;
                }
                None
            }
            HttpRequestType::ClientError(ref _md, ref err) => {
                let response_metadata = HttpResponseMetadata::from(&req);
                let response = match err {
                    ClientError::Message(s) => HttpResponseType::BadRequestJSON(
                        response_metadata,
                        serde_json::Value::String(s.to_string()),
                    ),
                    ClientError::NotFound(path) => {
                        HttpResponseType::NotFound(response_metadata, path.clone())
                    }
                };

                response
                    .send(&mut self.connection.protocol, &mut reply)
                    .map(|_| ())?;
                None
            }
        };

        match stream_opt {
            None => {
                self.reply_streams.push_back((reply, None, keep_alive));
            }
            Some(stream) => {
                self.reply_streams.push_back((
                    reply,
                    Some((
                        HttpChunkedTransferWriterState::new(STREAM_CHUNK_SIZE as usize),
                        stream,
                    )),
                    keep_alive,
                ));
            }
        }
        Ok(ret)
    }

    /// Make progress on outbound requests.
    /// Return true if the connection should be kept alive after all messages are drained.
    /// If we process a request with "Connection: close", then return false (indicating that the
    /// connection should be severed once the conversation is drained)
    fn send_outbound_responses(
        &mut self,
        chainstate: &mut StacksChainState,
    ) -> Result<(), net_error> {
        // send out streamed responses in the order they were requested
        let mut drained_handle = false;
        let mut drained_stream = false;
        let mut broken = false;
        let mut do_keep_alive = true;

        test_debug!(
            "{:?}: {} HTTP replies pending",
            &self,
            self.reply_streams.len()
        );
        match self.reply_streams.front_mut() {
            Some((ref mut reply, ref mut stream_opt, ref keep_alive)) => {
                do_keep_alive = *keep_alive;

                // if we're streaming, make some progress on the stream
                match stream_opt {
                    Some((ref mut http_chunk_state, ref mut stream)) => {
                        let mut encoder =
                            HttpChunkedTransferWriter::from_writer_state(reply, http_chunk_state);
                        match stream.stream_to(chainstate, &mut encoder, STREAM_CHUNK_SIZE) {
                            Ok(nw) => {
                                test_debug!("streamed {} bytes", nw);
                                if nw == 0 {
                                    // EOF -- finish chunk and stop sending.
                                    if !encoder.corked() {
                                        encoder.flush().map_err(|e| {
                                            test_debug!("Write error on encoder flush: {:?}", &e);
                                            net_error::WriteError(e)
                                        })?;

                                        encoder.cork();

                                        test_debug!("stream indicates EOF");
                                    }

                                    // try moving some data to the connection only once we're done
                                    // streaming
                                    match reply.try_flush() {
                                        Ok(res) => {
                                            test_debug!("Streamed reply is drained");
                                            drained_handle = res;
                                        }
                                        Err(e) => {
                                            // dead
                                            warn!("Broken HTTP connection: {:?}", &e);
                                            broken = true;
                                        }
                                    }
                                    drained_stream = true;
                                }
                            }
                            Err(e) => {
                                // broken -- terminate the stream.
                                // For example, if we're streaming an unconfirmed block or
                                // microblock, the data can get moved to the chunk store out from
                                // under the stream.
                                warn!("Failed to send to HTTP connection: {:?}", &e);
                                broken = true;
                            }
                        }
                    }
                    None => {
                        // not streamed; all data is buffered
                        drained_stream = true;

                        // try moving some data to the connection
                        match reply.try_flush() {
                            Ok(res) => {
                                test_debug!("Reply is drained");
                                drained_handle = res;
                            }
                            Err(e) => {
                                // dead
                                warn!("Broken HTTP connection: {:?}", &e);
                                broken = true;
                            }
                        }
                    }
                }
            }
            None => {}
        }

        if broken || (drained_handle && drained_stream) {
            // done with this stream
            test_debug!(
                "{:?}: done with stream (broken={}, drained_handle={}, drained_stream={})",
                &self,
                broken,
                drained_handle,
                drained_stream
            );
            self.total_reply_count += 1;
            self.reply_streams.pop_front();

            if !do_keep_alive {
                // encountered "Connection: close"
                self.keep_alive = false;
            }
        }

        Ok(())
    }

    pub fn try_send_recv_response(
        req: ReplyHandleHttp,
    ) -> Result<HttpResponseType, Result<ReplyHandleHttp, net_error>> {
        match req.try_send_recv() {
            Ok(message) => match message {
                StacksHttpMessage::Request(_) => {
                    warn!("Received response: not a HTTP response");
                    return Err(Err(net_error::InvalidMessage));
                }
                StacksHttpMessage::Response(http_response) => Ok(http_response),
            },
            Err(res) => Err(res),
        }
    }

    /// Make progress on our request/response
    fn recv_inbound_response(&mut self) -> Result<(), net_error> {
        // make progress on our pending request (if it exists).
        let inprogress = self.pending_request.is_some();
        let is_pending = self.pending_response.is_none();

        let pending_request = self.pending_request.take();
        let response = match pending_request {
            None => Ok(self.pending_response.take()),
            Some(req) => match ConversationHttp::try_send_recv_response(req) {
                Ok(response) => Ok(Some(response)),
                Err(res) => match res {
                    Ok(handle) => {
                        // try again
                        self.pending_request = Some(handle);
                        Ok(self.pending_response.take())
                    }
                    Err(e) => Err(e),
                },
            },
        }?;

        self.pending_response = response;

        if inprogress && self.pending_request.is_none() {
            test_debug!(
                "{:?},id={}: HTTP request finished",
                &self.peer_host,
                self.conn_id
            );
        }

        if is_pending && self.pending_response.is_some() {
            test_debug!(
                "{:?},id={}: HTTP response finished",
                &self.peer_host,
                self.conn_id
            );
        }

        Ok(())
    }

    /// Try to get our response
    pub fn try_get_response(&mut self) -> Option<HttpResponseType> {
        self.pending_response.take()
    }

    /// Make progress on in-flight messages.
    pub fn try_flush(&mut self, chainstate: &mut StacksChainState) -> Result<(), net_error> {
        self.send_outbound_responses(chainstate)?;
        self.recv_inbound_response()?;
        Ok(())
    }

    /// Is the connection idle?
    pub fn is_idle(&self) -> bool {
        self.pending_response.is_none()
            && self.connection.inbox_len() == 0
            && self.connection.outbox_len() == 0
            && self.reply_streams.len() == 0
    }

    /// Is the conversation out of pending data?
    /// Don't consider it drained if we haven't received anything yet
    pub fn is_drained(&self) -> bool {
        ((self.total_request_count > 0 && self.total_reply_count > 0)
            || self.pending_error_response.is_some())
            && self.is_idle()
    }

    /// Should the connection be kept alive even if drained?
    pub fn is_keep_alive(&self) -> bool {
        self.keep_alive
    }

    /// When was the last time we got an inbound request?
    pub fn get_last_request_time(&self) -> u64 {
        self.last_request_timestamp
    }

    /// When was the last time we sent data as part of an outbound response?
    pub fn get_last_response_time(&self) -> u64 {
        self.last_response_timestamp
    }

    /// When was this converation conencted?
    pub fn get_connection_time(&self) -> u64 {
        self.connection_time
    }

    /// Make progress on in-flight requests and replies.
    /// Returns the list of transactions we'll need to forward to the peer network
    pub fn chat(
        &mut self,
        network: &mut PeerNetwork,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        mempool: &mut MemPoolDB,
        handler_args: &RPCHandlerArgs,
    ) -> Result<Vec<StacksMessageType>, net_error> {
        // if we have an in-flight error, then don't take any more requests.
        if self.pending_error_response.is_some() {
            return Ok(vec![]);
        }

        // handle in-bound HTTP request(s)
        let num_inbound = self.connection.inbox_len();
        let mut ret = vec![];
        test_debug!("{:?}: {} HTTP requests pending", &self, num_inbound);

        for _i in 0..num_inbound {
            let msg = match self.connection.next_inbox_message() {
                None => {
                    continue;
                }
                Some(m) => m,
            };

            match msg {
                StacksHttpMessage::Request(req) => {
                    // new request
                    self.total_request_count += 1;
                    self.last_request_timestamp = get_epoch_time_secs();
                    let msg_opt = monitoring::instrument_http_request_handler(req, |req| {
                        self.handle_request(req, network, sortdb, chainstate, mempool, handler_args)
                    })?;
                    if let Some(msg) = msg_opt {
                        ret.push(msg);
                    }
                }
                StacksHttpMessage::Response(resp) => {
                    // Is there someone else waiting for this message?  If so, pass it along.
                    // (this _should_ be our pending_request handle)
                    match self
                        .connection
                        .fulfill_request(StacksHttpMessage::Response(resp))
                    {
                        None => {
                            test_debug!("{:?}: Fulfilled pending HTTP request", &self);
                        }
                        Some(_msg) => {
                            // unsolicited; discard
                            test_debug!("{:?}: Dropping unsolicited HTTP response", &self);
                        }
                    }
                }
            }
        }

        Ok(ret)
    }

    /// Remove all timed-out messages, and ding the remote peer as unhealthy
    pub fn clear_timeouts(&mut self) -> () {
        self.connection.drain_timeouts();
    }

    /// Load data into our HTTP connection
    pub fn recv<R: Read>(&mut self, r: &mut R) -> Result<usize, net_error> {
        let mut total_recv = 0;
        loop {
            let nrecv = match self.connection.recv_data(r) {
                Ok(nr) => nr,
                Err(e) => {
                    debug!("{:?}: failed to recv: {:?}", self, &e);
                    return Err(e);
                }
            };

            total_recv += nrecv;
            if nrecv > 0 {
                self.last_request_timestamp = get_epoch_time_secs();
            } else {
                break;
            }
        }
        monitoring::update_inbound_rpc_bandwidth(total_recv as i64);
        Ok(total_recv)
    }

    /// Write data out of our HTTP connection.  Write as much as we can
    pub fn send<W: Write>(
        &mut self,
        w: &mut W,
        chainstate: &mut StacksChainState,
    ) -> Result<usize, net_error> {
        let mut total_sz = 0;
        loop {
            // prime the Write
            self.try_flush(chainstate)?;

            let sz = match self.connection.send_data(w) {
                Ok(sz) => sz,
                Err(e) => {
                    info!("{:?}: failed to send on HTTP conversation: {:?}", self, &e);
                    return Err(e);
                }
            };

            total_sz += sz;
            if sz > 0 {
                self.last_response_timestamp = get_epoch_time_secs();
            } else {
                break;
            }
        }
        monitoring::update_inbound_rpc_bandwidth(total_sz as i64);
        Ok(total_sz)
    }

    /// Make a new getinfo request to this endpoint
    pub fn new_getinfo(&self) -> HttpRequestType {
        HttpRequestType::GetInfo(HttpRequestMetadata::from_host(self.peer_host.clone()))
    }

    /// Make a new getinfo request to this endpoint
    pub fn new_getpoxinfo(&self, tip_opt: Option<StacksBlockId>) -> HttpRequestType {
        HttpRequestType::GetPoxInfo(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            tip_opt,
        )
    }

    /// Make a new getneighbors request to this endpoint
    pub fn new_getneighbors(&self) -> HttpRequestType {
        HttpRequestType::GetNeighbors(HttpRequestMetadata::from_host(self.peer_host.clone()))
    }

    /// Make a new getblock request to this endpoint
    pub fn new_getblock(&self, index_block_hash: StacksBlockId) -> HttpRequestType {
        HttpRequestType::GetBlock(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            index_block_hash,
        )
    }

    /// Make a new get-microblocks request to this endpoint
    pub fn new_getmicroblocks_indexed(
        &self,
        index_microblock_hash: StacksBlockId,
    ) -> HttpRequestType {
        HttpRequestType::GetMicroblocksIndexed(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            index_microblock_hash,
        )
    }

    /// Make a new get-microblocks-confirmed request to this endpoint
    pub fn new_getmicroblocks_confirmed(
        &self,
        index_anchor_block_hash: StacksBlockId,
    ) -> HttpRequestType {
        HttpRequestType::GetMicroblocksConfirmed(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            index_anchor_block_hash,
        )
    }

    /// Make a new get-microblocks request for unconfirmed microblocks
    pub fn new_getmicroblocks_unconfirmed(
        &self,
        anchored_index_block_hash: StacksBlockId,
        min_seq: u16,
    ) -> HttpRequestType {
        HttpRequestType::GetMicroblocksUnconfirmed(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            anchored_index_block_hash,
            min_seq,
        )
    }

    /// Make a new get-unconfirmed-tx request
    pub fn new_gettransaction_unconfirmed(&self, txid: Txid) -> HttpRequestType {
        HttpRequestType::GetTransactionUnconfirmed(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            txid,
        )
    }

    /// Make a new post-transaction request
    pub fn new_post_transaction(&self, tx: StacksTransaction) -> HttpRequestType {
        HttpRequestType::PostTransaction(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            tx,
            None,
        )
    }

    /// Make a new post-block request
    pub fn new_post_block(&self, ch: ConsensusHash, block: StacksBlock) -> HttpRequestType {
        HttpRequestType::PostBlock(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            ch,
            block,
        )
    }

    /// Make a new post-microblock request
    pub fn new_post_microblock(
        &self,
        mblock: StacksMicroblock,
        tip_opt: Option<StacksBlockId>,
    ) -> HttpRequestType {
        HttpRequestType::PostMicroblock(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            mblock,
            tip_opt,
        )
    }

    /// Make a new request for an account
    pub fn new_getaccount(
        &self,
        principal: PrincipalData,
        tip_opt: Option<StacksBlockId>,
        with_proof: bool,
    ) -> HttpRequestType {
        HttpRequestType::GetAccount(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            principal,
            tip_opt,
            with_proof,
        )
    }

    /// Make a new request for a data map
    pub fn new_getmapentry(
        &self,
        contract_addr: StacksAddress,
        contract_name: ContractName,
        map_name: ClarityName,
        key: Value,
        tip_opt: Option<StacksBlockId>,
        with_proof: bool,
    ) -> HttpRequestType {
        HttpRequestType::GetMapEntry(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            contract_addr,
            contract_name,
            map_name,
            key,
            tip_opt,
            with_proof,
        )
    }

    /// Make a new request to get a contract's source
    pub fn new_getcontractsrc(
        &self,
        contract_addr: StacksAddress,
        contract_name: ContractName,
        tip_opt: Option<StacksBlockId>,
        with_proof: bool,
    ) -> HttpRequestType {
        HttpRequestType::GetContractSrc(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            contract_addr,
            contract_name,
            tip_opt,
            with_proof,
        )
    }

    /// Make a new request to get a contract's ABI
    pub fn new_getcontractabi(
        &self,
        contract_addr: StacksAddress,
        contract_name: ContractName,
        tip_opt: Option<StacksBlockId>,
    ) -> HttpRequestType {
        HttpRequestType::GetContractABI(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            contract_addr,
            contract_name,
            tip_opt,
        )
    }

    /// Make a new request to run a read-only function
    pub fn new_callreadonlyfunction(
        &self,
        contract_addr: StacksAddress,
        contract_name: ContractName,
        sender: PrincipalData,
        function_name: ClarityName,
        function_args: Vec<Value>,
        tip_opt: Option<StacksBlockId>,
    ) -> HttpRequestType {
        HttpRequestType::CallReadOnlyFunction(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            contract_addr,
            contract_name,
            sender,
            function_name,
            function_args,
            tip_opt,
        )
    }

    /// Make a new request for attachment inventory page
    pub fn new_getattachmentsinv(
        &self,
        index_block_hash: StacksBlockId,
        pages_indexes: HashSet<u32>,
    ) -> HttpRequestType {
        HttpRequestType::GetAttachmentsInv(
            HttpRequestMetadata::from_host(self.peer_host.clone()),
            index_block_hash,
            pages_indexes,
        )
    }
}

#[cfg(test)]
mod test {
    use std::cell::RefCell;
    use std::convert::TryInto;
    use std::iter::FromIterator;

    use address::*;
    use burnchains::Burnchain;
    use burnchains::BurnchainView;
    use burnchains::*;
    use chainstate::burn::ConsensusHash;
    use chainstate::stacks::db::blocks::test::*;
    use chainstate::stacks::db::BlockStreamData;
    use chainstate::stacks::db::StacksChainState;
    use chainstate::stacks::miner::*;
    use chainstate::stacks::test::*;
    use chainstate::stacks::Error as chain_error;
    use chainstate::stacks::*;
    use net::codec::*;
    use net::http::*;
    use net::test::*;
    use net::*;
    use util::get_epoch_time_secs;
    use util::hash::hex_bytes;
    use util::pipe::*;
    use vm::types::*;

    use crate::types::chainstate::BlockHeaderHash;
    use crate::types::chainstate::BurnchainHeaderHash;
    use chainstate::stacks::C32_ADDRESS_VERSION_TESTNET_SINGLESIG;

    use super::*;

    const TEST_CONTRACT: &'static str = "
        (define-data-var bar int 0)
        (define-map unit-map { account: principal } { units: int })
        (define-public (get-bar) (ok (var-get bar)))
        (define-public (set-bar (x int) (y int))
          (begin (var-set bar (/ x y)) (ok (var-get bar))))
        (define-public (add-unit)
          (begin
            (map-set unit-map { account: tx-sender } { units: 1 } )
            (ok 1)))
        (begin
          (map-set unit-map { account: 'ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R } { units: 123 }))";

    fn convo_send_recv(
        sender: &mut ConversationHttp,
        sender_chainstate: &mut StacksChainState,
        receiver: &mut ConversationHttp,
        receiver_chainstate: &mut StacksChainState,
    ) -> () {
        let (mut pipe_read, mut pipe_write) = Pipe::new();
        pipe_read.set_nonblocking(true);

        loop {
            let res = true;

            sender.try_flush(sender_chainstate).unwrap();
            receiver.try_flush(receiver_chainstate).unwrap();

            pipe_write.try_flush().unwrap();

            let all_relays_flushed =
                receiver.num_pending_outbound() == 0 && sender.num_pending_outbound() == 0;

            let nw = sender.send(&mut pipe_write, sender_chainstate).unwrap();
            let nr = receiver.recv(&mut pipe_read).unwrap();

            test_debug!(
                "res = {}, all_relays_flushed = {} ({},{}), nr = {}, nw = {}",
                res,
                all_relays_flushed,
                receiver.num_pending_outbound(),
                sender.num_pending_outbound(),
                nr,
                nw
            );
            if res && all_relays_flushed && nr == 0 && nw == 0 {
                test_debug!("Breaking send_recv");
                break;
            }
        }
    }

    fn test_rpc<F, C>(
        test_name: &str,
        peer_1_p2p: u16,
        peer_1_http: u16,
        peer_2_p2p: u16,
        peer_2_http: u16,
        make_request: F,
        check_result: C,
    ) -> ()
    where
        F: FnOnce(
            &mut TestPeer,
            &mut ConversationHttp,
            &mut TestPeer,
            &mut ConversationHttp,
        ) -> HttpRequestType,
        C: FnOnce(&HttpRequestType, &HttpResponseType, &mut TestPeer, &mut TestPeer) -> bool,
    {
        let mut peer_1_config = TestPeerConfig::new(test_name, peer_1_p2p, peer_1_http);
        let mut peer_2_config = TestPeerConfig::new(test_name, peer_2_p2p, peer_2_http);

        // ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R
        let privk1 = StacksPrivateKey::from_hex(
            "9f1f85a512a96a244e4c0d762788500687feb97481639572e3bffbd6860e6ab001",
        )
        .unwrap();

        // STVN97YYA10MY5F6KQJHKNYJNM24C4A1AT39WRW
        let privk2 = StacksPrivateKey::from_hex(
            "94c319327cc5cd04da7147d32d836eb2e4c44f4db39aa5ede7314a761183d0c701",
        )
        .unwrap();
        let microblock_privkey = StacksPrivateKey::new();
        let microblock_pubkeyhash =
            Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));

        let addr1 = StacksAddress::from_public_keys(
            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
            &AddressHashMode::SerializeP2PKH,
            1,
            &vec![StacksPublicKey::from_private(&privk1)],
        )
        .unwrap();
        let addr2 = StacksAddress::from_public_keys(
            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
            &AddressHashMode::SerializeP2PKH,
            1,
            &vec![StacksPublicKey::from_private(&privk2)],
        )
        .unwrap();

        peer_1_config.initial_balances = vec![
            (addr1.to_account_principal(), 1000000000),
            (addr2.to_account_principal(), 1000000000),
        ];

        peer_2_config.initial_balances = vec![
            (addr1.to_account_principal(), 1000000000),
            (addr2.to_account_principal(), 1000000000),
        ];

        peer_1_config.add_neighbor(&peer_2_config.to_neighbor());
        peer_2_config.add_neighbor(&peer_1_config.to_neighbor());

        let mut peer_1 = TestPeer::new(peer_1_config);
        let mut peer_2 = TestPeer::new(peer_2_config);

        // mine one block with a contract in it
        // first the coinbase
        // make a coinbase for this miner
        let mut tx_coinbase = StacksTransaction::new(
            TransactionVersion::Testnet,
            TransactionAuth::from_p2pkh(&privk1).unwrap(),
            TransactionPayload::Coinbase(CoinbasePayload([0x00; 32])),
        );
        tx_coinbase.chain_id = 0x80000000;
        tx_coinbase.anchor_mode = TransactionAnchorMode::OnChainOnly;
        tx_coinbase.auth.set_origin_nonce(0);

        let mut tx_signer = StacksTransactionSigner::new(&tx_coinbase);
        tx_signer.sign_origin(&privk1).unwrap();
        let tx_coinbase_signed = tx_signer.get_tx().unwrap();

        // next the contract
        let contract = TEST_CONTRACT.clone();
        let mut tx_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            TransactionAuth::from_p2pkh(&privk1).unwrap(),
            TransactionPayload::new_smart_contract(&format!("hello-world"), &contract.to_string())
                .unwrap(),
        );

        tx_contract.chain_id = 0x80000000;
        tx_contract.auth.set_origin_nonce(1);
        tx_contract.set_tx_fee(0);

        let mut tx_signer = StacksTransactionSigner::new(&tx_contract);
        tx_signer.sign_origin(&privk1).unwrap();
        let tx_contract_signed = tx_signer.get_tx().unwrap();

        // update account and state in a microblock that will be unconfirmed
        let mut tx_cc = StacksTransaction::new(
            TransactionVersion::Testnet,
            TransactionAuth::from_p2pkh(&privk1).unwrap(),
            TransactionPayload::new_contract_call(addr1.clone(), "hello-world", "add-unit", vec![])
                .unwrap(),
        );

        tx_cc.chain_id = 0x80000000;
        tx_cc.auth.set_origin_nonce(2);
        tx_cc.set_tx_fee(123);

        let mut tx_signer = StacksTransactionSigner::new(&tx_cc);
        tx_signer.sign_origin(&privk1).unwrap();
        let tx_cc_signed = tx_signer.get_tx().unwrap();
        let tx_cc_len = {
            let mut bytes = vec![];
            tx_cc_signed.consensus_serialize(&mut bytes).unwrap();
            bytes.len() as u64
        };

        // make an unconfirmed contract
        let unconfirmed_contract = "(define-read-only (ro-test) (ok 1))";
        let mut tx_unconfirmed_contract = StacksTransaction::new(
            TransactionVersion::Testnet,
            TransactionAuth::from_p2pkh(&privk1).unwrap(),
            TransactionPayload::new_smart_contract(
                &format!("hello-world-unconfirmed"),
                &unconfirmed_contract.to_string(),
            )
            .unwrap(),
        );

        tx_unconfirmed_contract.chain_id = 0x80000000;
        tx_unconfirmed_contract.auth.set_origin_nonce(3);
        tx_unconfirmed_contract.set_tx_fee(0);

        let mut tx_signer = StacksTransactionSigner::new(&tx_unconfirmed_contract);
        tx_signer.sign_origin(&privk1).unwrap();
        let tx_unconfirmed_contract_signed = tx_signer.get_tx().unwrap();
        let tx_unconfirmed_contract_len = {
            let mut bytes = vec![];
            tx_unconfirmed_contract_signed
                .consensus_serialize(&mut bytes)
                .unwrap();
            bytes.len() as u64
        };

        let tip =
            SortitionDB::get_canonical_burn_chain_tip(&peer_1.sortdb.as_ref().unwrap().conn())
                .unwrap();
        let mut anchor_cost = ExecutionCost::zero();
        let mut anchor_size = 0;

        // make a block and a microblock.
        // Put the coinbase and smart-contract in the anchored block.
        // Put the contract-call in the microblock
        let (burn_ops, stacks_block, microblocks) = peer_1.make_tenure(
            |ref mut miner, ref mut sortdb, ref mut chainstate, vrf_proof, ref parent_opt, _| {
                let parent_tip = match parent_opt {
                    None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
                    Some(block) => {
                        let ic = sortdb.index_conn();
                        let snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
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

                let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                    &parent_tip,
                    vrf_proof,
                    tip.total_burn,
                    microblock_pubkeyhash,
                )
                .unwrap();
                let (anchored_block, anchored_block_size, anchored_block_cost) =
                    StacksBlockBuilder::make_anchored_block_from_txs(
                        block_builder,
                        chainstate,
                        &sortdb.index_conn(),
                        vec![tx_coinbase_signed.clone(), tx_contract_signed.clone()],
                    )
                    .unwrap();

                anchor_size = anchored_block_size;
                anchor_cost = anchored_block_cost;

                (anchored_block, vec![])
            },
        );

        let (_, _, consensus_hash) = peer_1.next_burnchain_block(burn_ops.clone());
        peer_2.next_burnchain_block(burn_ops.clone());

        peer_1.process_stacks_epoch_at_tip(&stacks_block, &vec![]);
        peer_2.process_stacks_epoch_at_tip(&stacks_block, &vec![]);

        // build 1-block microblock stream with the contract-call and the unconfirmed contract
        let microblock = {
            let sortdb = peer_1.sortdb.take().unwrap();
            Relayer::setup_unconfirmed_state(peer_1.chainstate(), &sortdb).unwrap();
            let mblock = {
                let sort_iconn = sortdb.index_conn();
                let mut microblock_builder = StacksMicroblockBuilder::new(
                    stacks_block.block_hash(),
                    consensus_hash.clone(),
                    peer_1.chainstate(),
                    &sort_iconn,
                )
                .unwrap();
                let microblock = microblock_builder
                    .mine_next_microblock_from_txs(
                        vec![
                            (tx_cc_signed, tx_cc_len),
                            (tx_unconfirmed_contract_signed, tx_unconfirmed_contract_len),
                        ],
                        &microblock_privkey,
                    )
                    .unwrap();
                microblock
            };
            peer_1.sortdb = Some(sortdb);
            mblock
        };

        // store microblock stream
        peer_1
            .chainstate()
            .preprocess_streamed_microblock(
                &consensus_hash,
                &stacks_block.block_hash(),
                &microblock,
            )
            .unwrap();
        peer_2
            .chainstate()
            .preprocess_streamed_microblock(
                &consensus_hash,
                &stacks_block.block_hash(),
                &microblock,
            )
            .unwrap();

        // process microblock stream to generate unconfirmed state
        let canonical_tip =
            StacksBlockHeader::make_index_block_hash(&consensus_hash, &stacks_block.block_hash());
        let sortdb1 = peer_1.sortdb.take().unwrap();
        let sortdb2 = peer_2.sortdb.take().unwrap();
        peer_1
            .chainstate()
            .reload_unconfirmed_state(&sortdb1.index_conn(), canonical_tip.clone())
            .unwrap();
        peer_2
            .chainstate()
            .reload_unconfirmed_state(&sortdb2.index_conn(), canonical_tip.clone())
            .unwrap();
        peer_1.sortdb = Some(sortdb1);
        peer_2.sortdb = Some(sortdb2);

        let view_1 = peer_1.get_burnchain_view().unwrap();
        let view_2 = peer_2.get_burnchain_view().unwrap();

        let mut convo_1 = ConversationHttp::new(
            format!("127.0.0.1:{}", peer_1_http)
                .parse::<SocketAddr>()
                .unwrap(),
            Some(UrlString::try_from(format!("http://peer1.com")).unwrap()),
            peer_1.to_peer_host(),
            &peer_1.config.connection_opts,
            0,
        );

        let mut convo_2 = ConversationHttp::new(
            format!("127.0.0.1:{}", peer_2_http)
                .parse::<SocketAddr>()
                .unwrap(),
            Some(UrlString::try_from(format!("http://peer2.com")).unwrap()),
            peer_2.to_peer_host(),
            &peer_2.config.connection_opts,
            1,
        );

        let req = make_request(&mut peer_1, &mut convo_1, &mut peer_2, &mut convo_2);

        convo_1.send_request(req.clone()).unwrap();

        test_debug!("convo1 sends to convo2");
        convo_send_recv(
            &mut convo_1,
            peer_1.chainstate(),
            &mut convo_2,
            peer_2.chainstate(),
        );

        // hack around the borrow-checker
        let mut peer_1_sortdb = peer_1.sortdb.take().unwrap();
        let mut peer_1_stacks_node = peer_1.stacks_node.take().unwrap();
        let mut peer_1_mempool = peer_1.mempool.take().unwrap();

        Relayer::setup_unconfirmed_state(&mut peer_1_stacks_node.chainstate, &peer_1_sortdb)
            .unwrap();

        convo_1
            .chat(
                &mut peer_1.network,
                &mut peer_1_sortdb,
                &mut peer_1_stacks_node.chainstate,
                &mut peer_1_mempool,
                &RPCHandlerArgs::default(),
            )
            .unwrap();

        peer_1.sortdb = Some(peer_1_sortdb);
        peer_1.stacks_node = Some(peer_1_stacks_node);
        peer_1.mempool = Some(peer_1_mempool);

        test_debug!("convo2 sends to convo1");

        // hack around the borrow-checker
        let mut peer_2_sortdb = peer_2.sortdb.take().unwrap();
        let mut peer_2_stacks_node = peer_2.stacks_node.take().unwrap();
        let mut peer_2_mempool = peer_2.mempool.take().unwrap();

        Relayer::setup_unconfirmed_state(&mut peer_2_stacks_node.chainstate, &peer_2_sortdb)
            .unwrap();

        convo_2
            .chat(
                &mut peer_2.network,
                &mut peer_2_sortdb,
                &mut peer_2_stacks_node.chainstate,
                &mut peer_2_mempool,
                &RPCHandlerArgs::default(),
            )
            .unwrap();

        peer_2.sortdb = Some(peer_2_sortdb);
        peer_2.stacks_node = Some(peer_2_stacks_node);
        peer_2.mempool = Some(peer_2_mempool);

        convo_send_recv(
            &mut convo_2,
            peer_2.chainstate(),
            &mut convo_1,
            peer_1.chainstate(),
        );

        test_debug!("flush convo1");

        // hack around the borrow-checker
        convo_send_recv(
            &mut convo_1,
            peer_1.chainstate(),
            &mut convo_2,
            peer_2.chainstate(),
        );

        let mut peer_1_sortdb = peer_1.sortdb.take().unwrap();
        let mut peer_1_stacks_node = peer_1.stacks_node.take().unwrap();
        let mut peer_1_mempool = peer_1.mempool.take().unwrap();

        Relayer::setup_unconfirmed_state(&mut peer_1_stacks_node.chainstate, &peer_1_sortdb)
            .unwrap();

        convo_1
            .chat(
                &mut peer_1.network,
                &mut peer_1_sortdb,
                &mut peer_1_stacks_node.chainstate,
                &mut peer_1_mempool,
                &RPCHandlerArgs::default(),
            )
            .unwrap();

        peer_1.sortdb = Some(peer_1_sortdb);
        peer_1.stacks_node = Some(peer_1_stacks_node);
        peer_1.mempool = Some(peer_1_mempool);

        convo_1.try_flush(peer_1.chainstate()).unwrap();

        // should have gotten a reply
        let resp_opt = convo_1.try_get_response();
        assert!(resp_opt.is_some());

        let resp = resp_opt.unwrap();
        assert!(check_result(&req, &resp, &mut peer_1, &mut peer_2));
    }

    #[test]
    #[ignore]
    fn test_rpc_getinfo() {
        let peer_server_info = RefCell::new(None);
        test_rpc(
            "test_rpc_getinfo",
            40000,
            40001,
            50000,
            50001,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let peer_info = RPCPeerInfoData::from_network(
                    &peer_server.network,
                    &peer_server.stacks_node.as_ref().unwrap().chainstate,
                    &None,
                    &Sha256Sum::zero(),
                );

                *peer_server_info.borrow_mut() = Some(peer_info);

                convo_client.new_getinfo()
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::PeerInfo(response_md, peer_data) => {
                        assert_eq!(Some((*peer_data).clone()), *peer_server_info.borrow());
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_getpoxinfo() {
        let pox_server_info = RefCell::new(None);
        test_rpc(
            "test_rpc_getpoxinfo",
            40000,
            40001,
            50000,
            50001,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let mut sortdb = peer_server.sortdb.as_mut().unwrap();
                let chainstate = &mut peer_server.stacks_node.as_mut().unwrap().chainstate;
                let stacks_block_id = {
                    let tip = chainstate.get_stacks_chain_tip(sortdb).unwrap().unwrap();
                    StacksBlockHeader::make_index_block_hash(
                        &tip.consensus_hash,
                        &tip.anchored_block_hash,
                    )
                };
                let pox_info = RPCPoxInfoData::from_db(
                    &mut sortdb,
                    chainstate,
                    &stacks_block_id,
                    &peer_client.config.burnchain,
                )
                .unwrap();
                *pox_server_info.borrow_mut() = Some(pox_info);
                convo_client.new_getpoxinfo(None)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::PoxInfo(response_md, pox_data) => {
                        assert_eq!(Some((*pox_data).clone()), *pox_server_info.borrow());
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_getneighbors() {
        test_rpc(
            "test_rpc_getneighbors",
            40010,
            40011,
            50010,
            50011,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| { convo_client.new_getneighbors() },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::Neighbors(response_md, neighbor_info) => {
                        assert_eq!(neighbor_info.sample.len(), 1);
                        assert_eq!(neighbor_info.sample[0].port, peer_client.config.server_port); // we see ourselves as the neighbor
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_unconfirmed_getblock() {
        let server_block_cell = RefCell::new(None);

        test_rpc(
            "test_rpc_unconfirmed_getblock",
            40020,
            40021,
            50020,
            50021,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                // have "server" peer store a block to staging
                let peer_server_block = make_codec_test_block(25);
                let peer_server_consensus_hash = ConsensusHash([0x02; 20]);
                let index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &peer_server_consensus_hash,
                    &peer_server_block.block_hash(),
                );

                test_debug!("Store peer server index block {:?}", &index_block_hash);
                store_staging_block(
                    peer_server.chainstate(),
                    &peer_server_consensus_hash,
                    &peer_server_block,
                    &ConsensusHash([0x03; 20]),
                    456,
                    123,
                );

                *server_block_cell.borrow_mut() = Some(peer_server_block);

                // now ask for it
                convo_client.new_getblock(index_block_hash)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::Block(response_md, block_info) => {
                        assert_eq!(
                            block_info.block_hash(),
                            (*server_block_cell.borrow()).as_ref().unwrap().block_hash()
                        );
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_confirmed_getblock() {
        let server_block_cell = RefCell::new(None);

        test_rpc(
            "test_rpc_confirmed_getblock",
            40030,
            40031,
            50030,
            50031,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                // have "server" peer store a block to staging
                let peer_server_block = make_codec_test_block(25);
                let peer_server_consensus_hash = ConsensusHash([0x02; 20]);
                let index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &peer_server_consensus_hash,
                    &peer_server_block.block_hash(),
                );

                test_debug!("Store peer server index block {:?}", &index_block_hash);
                store_staging_block(
                    peer_server.chainstate(),
                    &peer_server_consensus_hash,
                    &peer_server_block,
                    &ConsensusHash([0x03; 20]),
                    456,
                    123,
                );
                set_block_processed(
                    peer_server.chainstate(),
                    &peer_server_consensus_hash,
                    &peer_server_block.block_hash(),
                    true,
                );

                *server_block_cell.borrow_mut() = Some(peer_server_block);

                // now ask for it
                convo_client.new_getblock(index_block_hash)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::Block(response_md, block_info) => {
                        assert_eq!(
                            block_info.block_hash(),
                            (*server_block_cell.borrow()).as_ref().unwrap().block_hash()
                        );
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_indexed_microblocks() {
        let server_microblocks_cell = RefCell::new(vec![]);

        test_rpc(
            "test_rpc_indexed_microblocks",
            40040,
            40041,
            50040,
            50041,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let privk = StacksPrivateKey::from_hex(
                    "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
                )
                .unwrap();

                let parent_block = make_codec_test_block(25);
                let parent_consensus_hash = ConsensusHash([0x02; 20]);
                let parent_index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &parent_block.block_hash(),
                );

                let mut mblocks = make_sample_microblock_stream(&privk, &parent_block.block_hash());
                mblocks.truncate(15);

                let mut child_block = make_codec_test_block(25);
                let child_consensus_hash = ConsensusHash([0x03; 20]);

                child_block.header.parent_block = parent_block.block_hash();
                child_block.header.parent_microblock =
                    mblocks.last().as_ref().unwrap().block_hash();
                child_block.header.parent_microblock_sequence =
                    mblocks.last().as_ref().unwrap().header.sequence;

                store_staging_block(
                    peer_server.chainstate(),
                    &parent_consensus_hash,
                    &parent_block,
                    &ConsensusHash([0x01; 20]),
                    456,
                    123,
                );
                set_block_processed(
                    peer_server.chainstate(),
                    &parent_consensus_hash,
                    &parent_block.block_hash(),
                    true,
                );

                store_staging_block(
                    peer_server.chainstate(),
                    &child_consensus_hash,
                    &child_block,
                    &parent_consensus_hash,
                    456,
                    123,
                );
                set_block_processed(
                    peer_server.chainstate(),
                    &child_consensus_hash,
                    &child_block.block_hash(),
                    true,
                );

                let index_microblock_hash = StacksBlockHeader::make_index_block_hash(
                    &parent_consensus_hash,
                    &mblocks.last().as_ref().unwrap().block_hash(),
                );

                for mblock in mblocks.iter() {
                    store_staging_microblock(
                        peer_server.chainstate(),
                        &parent_consensus_hash,
                        &parent_block.block_hash(),
                        &mblock,
                    );
                }

                set_microblocks_processed(
                    peer_server.chainstate(),
                    &child_consensus_hash,
                    &child_block.block_hash(),
                    &mblocks.last().as_ref().unwrap().block_hash(),
                );

                *server_microblocks_cell.borrow_mut() = mblocks;

                convo_client.new_getmicroblocks_indexed(index_microblock_hash)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match (*http_response).clone() {
                    HttpResponseType::Microblocks(_, mut microblocks) => {
                        microblocks.reverse();
                        assert_eq!(microblocks.len(), (*server_microblocks_cell.borrow()).len());
                        assert_eq!(microblocks, *server_microblocks_cell.borrow());
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_confirmed_microblocks() {
        let server_microblocks_cell = RefCell::new(vec![]);

        test_rpc(
            "test_rpc_confirmed_microblocks",
            40042,
            40043,
            50042,
            50043,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let privk = StacksPrivateKey::from_hex(
                    "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
                )
                .unwrap();

                let parent_block = make_codec_test_block(25);
                let parent_consensus_hash = ConsensusHash([0x02; 20]);

                let mut mblocks = make_sample_microblock_stream(&privk, &parent_block.block_hash());
                mblocks.truncate(15);

                let mut child_block = make_codec_test_block(25);
                let child_consensus_hash = ConsensusHash([0x03; 20]);

                child_block.header.parent_block = parent_block.block_hash();
                child_block.header.parent_microblock =
                    mblocks.last().as_ref().unwrap().block_hash();
                child_block.header.parent_microblock_sequence =
                    mblocks.last().as_ref().unwrap().header.sequence;

                let child_index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &child_consensus_hash,
                    &child_block.block_hash(),
                );

                store_staging_block(
                    peer_server.chainstate(),
                    &parent_consensus_hash,
                    &parent_block,
                    &ConsensusHash([0x01; 20]),
                    456,
                    123,
                );
                set_block_processed(
                    peer_server.chainstate(),
                    &parent_consensus_hash,
                    &parent_block.block_hash(),
                    true,
                );

                store_staging_block(
                    peer_server.chainstate(),
                    &child_consensus_hash,
                    &child_block,
                    &parent_consensus_hash,
                    456,
                    123,
                );
                set_block_processed(
                    peer_server.chainstate(),
                    &child_consensus_hash,
                    &child_block.block_hash(),
                    true,
                );

                for mblock in mblocks.iter() {
                    store_staging_microblock(
                        peer_server.chainstate(),
                        &parent_consensus_hash,
                        &parent_block.block_hash(),
                        &mblock,
                    );
                }

                set_microblocks_processed(
                    peer_server.chainstate(),
                    &child_consensus_hash,
                    &child_block.block_hash(),
                    &mblocks.last().as_ref().unwrap().block_hash(),
                );

                *server_microblocks_cell.borrow_mut() = mblocks;

                convo_client.new_getmicroblocks_confirmed(child_index_block_hash)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match (*http_response).clone() {
                    HttpResponseType::Microblocks(_, mut microblocks) => {
                        microblocks.reverse();
                        assert_eq!(microblocks.len(), (*server_microblocks_cell.borrow()).len());
                        assert_eq!(microblocks, *server_microblocks_cell.borrow());
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_unconfirmed_microblocks() {
        let server_microblocks_cell = RefCell::new(vec![]);

        test_rpc(
            "test_rpc_unconfirmed_microblocks",
            40050,
            40051,
            50050,
            50051,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let privk = StacksPrivateKey::from_hex(
                    "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
                )
                .unwrap();

                let consensus_hash = ConsensusHash([0x02; 20]);
                let anchored_block_hash = BlockHeaderHash([0x03; 32]);
                let index_block_hash =
                    StacksBlockHeader::make_index_block_hash(&consensus_hash, &anchored_block_hash);

                let mut mblocks = make_sample_microblock_stream(&privk, &anchored_block_hash);
                mblocks.truncate(15);

                for mblock in mblocks.iter() {
                    store_staging_microblock(
                        peer_server.chainstate(),
                        &consensus_hash,
                        &anchored_block_hash,
                        &mblock,
                    );
                }

                *server_microblocks_cell.borrow_mut() = mblocks;

                // start at seq 5
                convo_client.new_getmicroblocks_unconfirmed(index_block_hash, 5)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::Microblocks(response_md, microblocks) => {
                        assert_eq!(microblocks.len(), 10);
                        assert_eq!(
                            *microblocks,
                            (*server_microblocks_cell.borrow())[5..].to_vec()
                        );
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_unconfirmed_transaction() {
        let last_txid = RefCell::new(Txid([0u8; 32]));
        let last_mblock = RefCell::new(BlockHeaderHash([0u8; 32]));

        test_rpc(
            "test_rpc_unconfirmed_transaction",
            40052,
            40053,
            50052,
            50053,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let privk = StacksPrivateKey::from_hex(
                    "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
                )
                .unwrap();

                let sortdb = peer_server.sortdb.take().unwrap();
                Relayer::setup_unconfirmed_state(peer_server.chainstate(), &sortdb).unwrap();
                peer_server.sortdb = Some(sortdb);

                assert!(peer_server.chainstate().unconfirmed_state.is_some());
                let (txid, mblock_hash) = match peer_server.chainstate().unconfirmed_state {
                    Some(ref unconfirmed) => {
                        assert!(unconfirmed.mined_txs.len() > 0);
                        let mut txid = Txid([0u8; 32]);
                        let mut mblock_hash = BlockHeaderHash([0u8; 32]);
                        for (next_txid, (_, mbh, ..)) in unconfirmed.mined_txs.iter() {
                            txid = next_txid.clone();
                            mblock_hash = mbh.clone();
                            break;
                        }
                        (txid, mblock_hash)
                    }
                    None => {
                        panic!("No unconfirmed state");
                    }
                };

                *last_txid.borrow_mut() = txid.clone();
                *last_mblock.borrow_mut() = mblock_hash.clone();

                convo_client.new_gettransaction_unconfirmed(txid)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::UnconfirmedTransaction(response_md, unconfirmed_resp) => {
                        assert_eq!(
                            unconfirmed_resp.status,
                            UnconfirmedTransactionStatus::Microblock {
                                block_hash: (*last_mblock.borrow()).clone(),
                                seq: 0
                            }
                        );
                        let tx = StacksTransaction::consensus_deserialize(
                            &mut &hex_bytes(&unconfirmed_resp.tx).unwrap()[..],
                        )
                        .unwrap();
                        assert_eq!(tx.txid(), *last_txid.borrow());
                        true
                    }
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_missing_getblock() {
        test_rpc(
            "test_rpc_missing_getblock",
            40060,
            40061,
            50060,
            50061,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let peer_server_block_hash = BlockHeaderHash([0x04; 32]);
                let peer_server_consensus_hash = ConsensusHash([0x02; 20]);
                let index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &peer_server_consensus_hash,
                    &peer_server_block_hash,
                );

                // now ask for it
                convo_client.new_getblock(index_block_hash)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::NotFound(response_md, msg) => true,
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_missing_index_getmicroblocks() {
        test_rpc(
            "test_rpc_missing_index_getmicroblocks",
            40070,
            40071,
            50070,
            50071,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let peer_server_block_hash = BlockHeaderHash([0x04; 32]);
                let peer_server_consensus_hash = ConsensusHash([0x02; 20]);
                let index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &peer_server_consensus_hash,
                    &peer_server_block_hash,
                );

                // now ask for it
                convo_client.new_getmicroblocks_indexed(index_block_hash)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::NotFound(response_md, msg) => true,
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_missing_confirmed_getmicroblocks() {
        test_rpc(
            "test_rpc_missing_confirmed_getmicroblocks",
            40070,
            40071,
            50070,
            50071,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let peer_server_block_hash = BlockHeaderHash([0x04; 32]);
                let peer_server_consensus_hash = ConsensusHash([0x02; 20]);
                let index_block_hash = StacksBlockHeader::make_index_block_hash(
                    &peer_server_consensus_hash,
                    &peer_server_block_hash,
                );

                // now ask for it
                convo_client.new_getmicroblocks_confirmed(index_block_hash)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::NotFound(response_md, msg) => true,
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_missing_unconfirmed_microblocks() {
        let server_microblocks_cell = RefCell::new(vec![]);

        test_rpc(
            "test_rpc_missing_unconfirmed_microblocks",
            40080,
            40081,
            50080,
            50081,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let privk = StacksPrivateKey::from_hex(
                    "eb05c83546fdd2c79f10f5ad5434a90dd28f7e3acb7c092157aa1bc3656b012c01",
                )
                .unwrap();

                let consensus_hash = ConsensusHash([0x02; 20]);
                let anchored_block_hash = BlockHeaderHash([0x03; 32]);
                let index_block_hash =
                    StacksBlockHeader::make_index_block_hash(&consensus_hash, &anchored_block_hash);

                let mut mblocks = make_sample_microblock_stream(&privk, &anchored_block_hash);
                mblocks.truncate(15);

                for mblock in mblocks.iter() {
                    store_staging_microblock(
                        peer_server.chainstate(),
                        &consensus_hash,
                        &anchored_block_hash,
                        &mblock,
                    );
                }

                *server_microblocks_cell.borrow_mut() = mblocks;

                // start at seq 16 (which doesn't exist)
                convo_client.new_getmicroblocks_unconfirmed(index_block_hash, 16)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::NotFound(response_md, msg) => true,
                    _ => {
                        error!("Invalid response: {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_contract_src() {
        test_rpc(
            "test_rpc_get_contract_src",
            40090,
            40091,
            50090,
            50091,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                convo_client.new_getcontractsrc(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world".try_into().unwrap(),
                    None,
                    false,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::GetContractSrc(response_md, data) => {
                        assert_eq!(data.source, TEST_CONTRACT);
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_contract_src_unconfirmed() {
        test_rpc(
            "test_rpc_get_contract_src_unconfirmed",
            40100,
            40101,
            50100,
            50101,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let unconfirmed_tip = peer_client
                    .chainstate()
                    .unconfirmed_state
                    .as_ref()
                    .unwrap()
                    .unconfirmed_chain_tip
                    .clone();
                convo_client.new_getcontractsrc(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world".try_into().unwrap(),
                    Some(unconfirmed_tip),
                    false,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::GetContractSrc(response_md, data) => {
                        assert_eq!(data.source, TEST_CONTRACT);
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_account() {
        test_rpc(
            "test_rpc_get_account",
            40110,
            40111,
            50110,
            50111,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                convo_client.new_getaccount(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap()
                        .to_account_principal(),
                    None,
                    false,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::GetAccount(response_md, data) => {
                        assert_eq!(data.nonce, 2);
                        let balance = u128::from_str_radix(&data.balance[2..], 16).unwrap();
                        assert_eq!(balance, 1000000000);
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_account_unconfirmed() {
        test_rpc(
            "test_rpc_get_account_unconfirmed",
            40120,
            40121,
            50120,
            50121,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let unconfirmed_tip = peer_client
                    .chainstate()
                    .unconfirmed_state
                    .as_ref()
                    .unwrap()
                    .unconfirmed_chain_tip
                    .clone();
                convo_client.new_getaccount(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap()
                        .to_account_principal(),
                    Some(unconfirmed_tip),
                    false,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::GetAccount(response_md, data) => {
                        assert_eq!(data.nonce, 4);
                        let balance = u128::from_str_radix(&data.balance[2..], 16).unwrap();
                        assert_eq!(balance, 1000000000 - 123);
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_map_entry() {
        test_rpc(
            "test_rpc_get_map_entry",
            40130,
            40131,
            50130,
            50131,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let principal =
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap()
                        .to_account_principal();
                convo_client.new_getmapentry(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world".try_into().unwrap(),
                    "unit-map".try_into().unwrap(),
                    Value::Tuple(
                        TupleData::from_data(vec![("account".into(), Value::Principal(principal))])
                            .unwrap(),
                    ),
                    None,
                    false,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::GetMapEntry(response_md, data) => {
                        assert_eq!(
                            Value::try_deserialize_hex_untyped(&data.data).unwrap(),
                            Value::some(Value::Tuple(
                                TupleData::from_data(vec![("units".into(), Value::Int(123))])
                                    .unwrap()
                            ))
                            .unwrap()
                        );
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_map_entry_unconfirmed() {
        test_rpc(
            "test_rpc_get_map_entry_unconfirmed",
            40140,
            40141,
            50140,
            50141,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let unconfirmed_tip = peer_client
                    .chainstate()
                    .unconfirmed_state
                    .as_ref()
                    .unwrap()
                    .unconfirmed_chain_tip
                    .clone();
                let principal =
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap()
                        .to_account_principal();
                convo_client.new_getmapentry(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world".try_into().unwrap(),
                    "unit-map".try_into().unwrap(),
                    Value::Tuple(
                        TupleData::from_data(vec![("account".into(), Value::Principal(principal))])
                            .unwrap(),
                    ),
                    Some(unconfirmed_tip),
                    false,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::GetMapEntry(response_md, data) => {
                        assert_eq!(
                            Value::try_deserialize_hex_untyped(&data.data).unwrap(),
                            Value::some(Value::Tuple(
                                TupleData::from_data(vec![("units".into(), Value::Int(1))])
                                    .unwrap()
                            ))
                            .unwrap()
                        );
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_contract_abi() {
        test_rpc(
            "test_rpc_get_contract_abi",
            40150,
            40151,
            50150,
            50151,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                convo_client.new_getcontractabi(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world-unconfirmed".try_into().unwrap(),
                    None,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::NotFound(..) => {
                        // not confirmed yet
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_get_contract_abi_unconfirmed() {
        test_rpc(
            "test_rpc_get_contract_abi_unconfirmed",
            40160,
            40161,
            50160,
            50161,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let unconfirmed_tip = peer_client
                    .chainstate()
                    .unconfirmed_state
                    .as_ref()
                    .unwrap()
                    .unconfirmed_chain_tip
                    .clone();
                convo_client.new_getcontractabi(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world-unconfirmed".try_into().unwrap(),
                    Some(unconfirmed_tip),
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::GetContractABI(response_md, data) => true,
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_call_read_only() {
        test_rpc(
            "test_rpc_call_read_only",
            40170,
            40171,
            50170,
            50171,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                convo_client.new_callreadonlyfunction(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world-unconfirmed".try_into().unwrap(),
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap()
                        .to_account_principal(),
                    "ro-test".try_into().unwrap(),
                    vec![],
                    None,
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::CallReadOnlyFunction(response_md, data) => {
                        assert!(data.cause.is_some());
                        assert!(data.cause.clone().unwrap().find("NoSuchContract").is_some());
                        assert!(!data.okay);
                        assert!(data.result.is_none());
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_call_read_only_unconfirmed() {
        test_rpc(
            "test_rpc_call_read_only_unconfirmed",
            40180,
            40181,
            50180,
            50181,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let unconfirmed_tip = peer_client
                    .chainstate()
                    .unconfirmed_state
                    .as_ref()
                    .unwrap()
                    .unconfirmed_chain_tip
                    .clone();
                convo_client.new_callreadonlyfunction(
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap(),
                    "hello-world-unconfirmed".try_into().unwrap(),
                    StacksAddress::from_string("ST2DS4MSWSGJ3W9FBC6BVT0Y92S345HY8N3T6AV7R")
                        .unwrap()
                        .to_account_principal(),
                    "ro-test".try_into().unwrap(),
                    vec![],
                    Some(unconfirmed_tip),
                )
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                match http_response {
                    HttpResponseType::CallReadOnlyFunction(response_md, data) => {
                        assert!(data.okay);
                        assert_eq!(
                            Value::try_deserialize_hex_untyped(&data.result.clone().unwrap())
                                .unwrap(),
                            Value::okay(Value::Int(1)).unwrap()
                        );
                        assert!(data.cause.is_none());
                        true
                    }
                    _ => {
                        error!("Invalid response; {:?}", &http_response);
                        false
                    }
                }
            },
        );
    }

    #[test]
    #[ignore]
    fn test_rpc_getattachmentsinv_limit_reached() {
        test_rpc(
            "test_rpc_getattachmentsinv",
            40000,
            40001,
            50000,
            50001,
            |ref mut peer_client,
             ref mut convo_client,
             ref mut peer_server,
             ref mut convo_server| {
                let pages_indexes = HashSet::from_iter(vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
                convo_client.new_getattachmentsinv(StacksBlockId([0x00; 32]), pages_indexes)
            },
            |ref http_request, ref http_response, ref mut peer_client, ref mut peer_server| {
                let req_md = http_request.metadata().clone();
                println!("{:?}", http_response);
                match http_response {
                    HttpResponseType::ServerError(_, msg) => {
                        assert_eq!(
                            msg,
                            "Number of attachment inv pages is limited by 8 per request"
                        );
                        true
                    }
                    _ => false,
                }
            },
        );
    }
}
