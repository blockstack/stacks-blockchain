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
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::mem;
use std::net::SocketAddr;
use std::sync::mpsc::sync_channel;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::RecvError;
use std::sync::mpsc::SendError;
use std::sync::mpsc::SyncSender;
use std::sync::mpsc::TryRecvError;
use std::sync::mpsc::TrySendError;

use mio;
use mio::net as mio_net;
use rand::prelude::*;
use rand::thread_rng;

use burnchains::Address;
use burnchains::Burnchain;
use burnchains::BurnchainView;
use burnchains::PublicKey;
use chainstate::burn::db::sortdb::{BlockHeaderCache, SortitionDB};
use chainstate::burn::BlockSnapshot;
use chainstate::stacks::db::StacksChainState;
use chainstate::stacks::{MAX_BLOCK_LEN, MAX_TRANSACTION_LEN};
use monitoring::{update_inbound_neighbors, update_outbound_neighbors};
use net::asn::ASEntry4;
use net::atlas::AtlasDB;
use net::atlas::{AttachmentInstance, AttachmentsDownloader};
use net::chat::ConversationP2P;
use net::chat::NeighborStats;
use net::connection::ConnectionOptions;
use net::connection::NetworkReplyHandle;
use net::connection::ReplyHandleHttp;
use net::connection::ReplyHandleP2P;
use net::db::LocalPeer;
use net::db::PeerDB;
use net::download::BlockDownloader;
use net::inv::*;
use net::neighbors::*;
use net::poll::NetworkPollState;
use net::poll::NetworkState;
use net::prune::*;
use net::relay::RelayerStats;
use net::relay::*;
use net::relay::*;
use net::rpc::RPCHandlerArgs;
use net::server::*;
use net::Error as net_error;
use net::Neighbor;
use net::NeighborKey;
use net::PeerAddress;
use net::*;
use util::db::DBConn;
use util::db::Error as db_error;
use util::get_epoch_time_secs;
use util::hash::to_hex;
use util::log;
use util::secp256k1::Secp256k1PublicKey;

use crate::types::chainstate::{PoxId, SortitionId, StacksBlockHeader};

/// inter-thread request to send a p2p message from another thread in this program.
#[derive(Debug)]
pub enum NetworkRequest {
    Ban(Vec<NeighborKey>),
    AdvertizeBlocks(BlocksAvailableMap), // announce to all wanting neighbors that we have these blocks
    AdvertizeMicroblocks(BlocksAvailableMap), // announce to all wanting neighbors that we have these confirmed microblock streams
    Relay(NeighborKey, StacksMessage),
    Broadcast(Vec<RelayData>, StacksMessageType),
}

/// Handle for other threads to use to issue p2p network requests.
/// The "main loop" for sending/receiving data is a select/poll loop, and runs outside of other
/// threads that need a synchronous RPC or a multi-RPC interface.  This object gives those threads
/// a way to issue commands and hear back replies from them.
pub struct NetworkHandle {
    chan_in: SyncSender<NetworkRequest>,
}

/// Internal handle for receiving requests from a NetworkHandle.
/// This is the 'other end' of a NetworkHandle inside the peer network struct.
#[derive(Debug)]
struct NetworkHandleServer {
    chan_in: Receiver<NetworkRequest>,
}

impl NetworkHandle {
    pub fn new(chan_in: SyncSender<NetworkRequest>) -> NetworkHandle {
        NetworkHandle { chan_in: chan_in }
    }

    /// Send out a command to the p2p thread.  Do not bother waiting for the response.
    /// Error out if the channel buffer is out of space
    fn send_request(&mut self, req: NetworkRequest) -> Result<(), net_error> {
        match self.chan_in.try_send(req) {
            Ok(_) => Ok(()),
            Err(TrySendError::Full(_)) => {
                warn!("P2P handle channel is full");
                Err(net_error::FullHandle)
            }
            Err(TrySendError::Disconnected(_)) => {
                warn!("P2P handle channel is disconnected");
                Err(net_error::InvalidHandle)
            }
        }
    }

    /// Ban a peer
    pub fn ban_peers(&mut self, neighbor_keys: Vec<NeighborKey>) -> Result<(), net_error> {
        let req = NetworkRequest::Ban(neighbor_keys);
        self.send_request(req)
    }

    /// Advertize blocks
    pub fn advertize_blocks(&mut self, blocks: BlocksAvailableMap) -> Result<(), net_error> {
        let req = NetworkRequest::AdvertizeBlocks(blocks);
        self.send_request(req)
    }

    /// Advertize microblocks
    pub fn advertize_microblocks(&mut self, blocks: BlocksAvailableMap) -> Result<(), net_error> {
        let req = NetworkRequest::AdvertizeMicroblocks(blocks);
        self.send_request(req)
    }

    /// Relay a message to a peer via the p2p network thread, expecting no reply.
    /// Called from outside the p2p thread by other threads.
    pub fn relay_signed_message(
        &mut self,
        neighbor_key: NeighborKey,
        msg: StacksMessage,
    ) -> Result<(), net_error> {
        let req = NetworkRequest::Relay(neighbor_key, msg);
        self.send_request(req)
    }

    /// Broadcast a message to our neighbors via the p2p network thread.
    /// Add relay information for each one.
    pub fn broadcast_message(
        &mut self,
        relay_hints: Vec<RelayData>,
        msg: StacksMessageType,
    ) -> Result<(), net_error> {
        let req = NetworkRequest::Broadcast(relay_hints, msg);
        self.send_request(req)
    }
}

impl NetworkHandleServer {
    pub fn new(chan_in: Receiver<NetworkRequest>) -> NetworkHandleServer {
        NetworkHandleServer { chan_in: chan_in }
    }

    pub fn pair(bufsz: usize) -> (NetworkHandleServer, NetworkHandle) {
        let (msg_send, msg_recv) = sync_channel(bufsz);
        let server = NetworkHandleServer::new(msg_recv);
        let client = NetworkHandle::new(msg_send);
        (server, client)
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum PeerNetworkWorkState {
    GetPublicIP,
    BlockInvSync,
    BlockDownload,
    AntiEntropy,
    Prune,
}

pub type PeerMap = HashMap<usize, ConversationP2P>;

#[derive(Debug)]
pub struct PeerNetwork {
    pub local_peer: LocalPeer,
    pub peer_version: u32,
    pub chain_view: BurnchainView,
    pub burnchain_tip: BlockSnapshot,
    pub chain_view_stable_consensus_hash: ConsensusHash,

    pub peerdb: PeerDB,
    pub atlasdb: AtlasDB,

    // ongoing p2p conversations (either they reached out to us, or we to them)
    pub peers: PeerMap,
    pub sockets: HashMap<usize, mio_net::TcpStream>,
    pub events: HashMap<NeighborKey, usize>,
    pub connecting: HashMap<usize, (mio_net::TcpStream, bool, u64)>, // (socket, outbound?, connection sent timestamp)
    pub bans: HashSet<usize>,

    // ongoing messages the network is sending via the p2p interface (not bound to a specific
    // conversation).
    pub relay_handles: HashMap<usize, VecDeque<ReplyHandleP2P>>,
    pub relayer_stats: RelayerStats,

    // handles for other threads to send/receive data to peers
    handles: VecDeque<NetworkHandleServer>,

    // network I/O
    pub network: Option<NetworkState>,
    p2p_network_handle: usize,
    http_network_handle: usize,

    // info on the burn chain we're tracking
    pub burnchain: Burnchain,

    // connection options
    pub connection_opts: ConnectionOptions,

    // work state -- we can be walking, fetching block inventories, fetching blocks, pruning, etc.
    pub work_state: PeerNetworkWorkState,

    // neighbor walk state
    pub walk: Option<NeighborWalk>,
    pub walk_deadline: u64,
    pub walk_count: u64,
    pub walk_attempts: u64,
    pub walk_retries: u64,
    pub walk_resets: u64,
    pub walk_total_step_count: u64,
    pub walk_pingbacks: HashMap<NeighborAddress, NeighborPingback>, // inbound peers for us to try to ping back and add to our frontier, mapped to (peer_version, network_id, timeout, pubkey)
    pub walk_result: NeighborWalkResult, // last successful neighbor walk result

    // peer block inventory state
    pub inv_state: Option<InvState>,

    // cached view of PoX database
    // (maintained by the inv state machine)
    pub tip_sort_id: SortitionId,
    pub pox_id: PoxId,

    // cached block header hashes, for handling inventory requests
    // (maintained by the downloader state machine)
    pub header_cache: BlockHeaderCache,

    // peer block download state
    pub block_downloader: Option<BlockDownloader>,

    // peer attachment downloader
    pub attachments_downloader: Option<AttachmentsDownloader>,

    // how often we pruned a given inbound/outbound peer
    pub prune_outbound_counts: HashMap<NeighborKey, u64>,
    pub prune_inbound_counts: HashMap<NeighborKey, u64>,

    // http endpoint, used for driving HTTP conversations (some of which we initiate)
    pub http: Option<HttpPeer>,

    // our own neighbor address that we bind on
    bind_nk: NeighborKey,

    // our public IP address that we give out in our handshakes
    pub public_ip_learned: bool, // was the IP address given to us, or did we have to go learn it?
    pub public_ip_confirmed: bool, // once we learned the IP address, were we able to confirm it by self-connecting?
    public_ip_requested_at: u64,
    public_ip_learned_at: u64,
    public_ip_reply_handle: Option<ReplyHandleP2P>,
    public_ip_retries: u64,

    // how many loops of the state-machine have occured?
    // Used to coordinate with the chain synchronization logic to ensure that the node has at least
    // begun to download blocks after fetching the next reward cycles' sortitions.
    pub num_state_machine_passes: u64,

    // how many inv syncs have we done?
    pub num_inv_sync_passes: u64,

    // how many downloader passes have we done?
    pub num_downloader_passes: u64,

    // to whom did we send a block or microblock stream as part of our anti-entropy protocol, and
    // when did we send it?
    antientropy_blocks: HashMap<NeighborKey, HashMap<StacksBlockId, u64>>,
    antientropy_microblocks: HashMap<NeighborKey, HashMap<StacksBlockId, u64>>,
    antientropy_start_reward_cycle: u64,
    pub antientropy_last_push_ts: u64,

    // pending messages (BlocksAvailable, MicroblocksAvailable, BlocksData, Microblocks) that we
    // can't process yet, but might be able to process on the next chain view update
    pub pending_messages: HashMap<usize, Vec<StacksMessage>>,

    // fault injection -- force disconnects
    fault_last_disconnect: u64,
}

impl PeerNetwork {
    pub fn new(
        peerdb: PeerDB,
        atlasdb: AtlasDB,
        mut local_peer: LocalPeer,
        peer_version: u32,
        burnchain: Burnchain,
        chain_view: BurnchainView,
        connection_opts: ConnectionOptions,
    ) -> PeerNetwork {
        let http = HttpPeer::new(connection_opts.clone(), 0);
        let pub_ip = connection_opts.public_ip_address.clone();
        let pub_ip_learned = pub_ip.is_none();
        local_peer.public_ip_address = pub_ip.clone();

        if connection_opts.disable_inbound_handshakes {
            debug!("{:?}: disable inbound handshakes", &local_peer);
        }
        if connection_opts.disable_inbound_walks {
            debug!("{:?}: disable inbound neighbor walks", &local_peer);
        }

        let first_block_height = burnchain.first_block_height;
        let first_burn_header_hash = burnchain.first_block_hash.clone();
        let first_burn_header_ts = burnchain.first_block_timestamp;

        let mut network = PeerNetwork {
            local_peer: local_peer,
            peer_version: peer_version,
            chain_view: chain_view,
            chain_view_stable_consensus_hash: ConsensusHash([0u8; 20]),
            burnchain_tip: BlockSnapshot::initial(
                first_block_height,
                &first_burn_header_hash,
                first_burn_header_ts as u64,
            ),

            peerdb: peerdb,
            atlasdb: atlasdb,

            peers: PeerMap::new(),
            sockets: HashMap::new(),
            events: HashMap::new(),
            connecting: HashMap::new(),
            bans: HashSet::new(),

            relay_handles: HashMap::new(),
            relayer_stats: RelayerStats::new(),

            handles: VecDeque::new(),
            network: None,
            p2p_network_handle: 0,
            http_network_handle: 0,

            burnchain: burnchain,
            connection_opts: connection_opts,

            work_state: PeerNetworkWorkState::GetPublicIP,

            walk: None,
            walk_deadline: 0,
            walk_attempts: 0,
            walk_retries: 0,
            walk_resets: 0,
            walk_count: 0,
            walk_total_step_count: 0,
            walk_pingbacks: HashMap::new(),
            walk_result: NeighborWalkResult::new(),

            inv_state: None,
            pox_id: PoxId::initial(),
            tip_sort_id: SortitionId([0x00; 32]),
            header_cache: BlockHeaderCache::new(),

            block_downloader: None,
            attachments_downloader: None,

            prune_outbound_counts: HashMap::new(),
            prune_inbound_counts: HashMap::new(),

            http: Some(http),
            bind_nk: NeighborKey {
                network_id: 0,
                peer_version: 0,
                addrbytes: PeerAddress([0u8; 16]),
                port: 0,
            },

            public_ip_learned: pub_ip_learned,
            public_ip_requested_at: 0,
            public_ip_learned_at: 0,
            public_ip_confirmed: false,
            public_ip_reply_handle: None,
            public_ip_retries: 0,

            num_state_machine_passes: 0,
            num_inv_sync_passes: 0,
            num_downloader_passes: 0,

            antientropy_blocks: HashMap::new(),
            antientropy_microblocks: HashMap::new(),
            antientropy_last_push_ts: 0,
            antientropy_start_reward_cycle: 0,

            pending_messages: HashMap::new(),

            fault_last_disconnect: 0,
        };

        network.init_block_downloader();
        network.init_attachments_downloader(vec![]);

        network
    }

    /// Do something with the HTTP peer.
    /// NOTE: the HTTP peer is *always* instantiated; it's just an Option<..> so its methods can
    /// receive a ref to the PeerNetwork that contains it.
    pub fn with_http<F, R>(network: &mut PeerNetwork, to_do: F) -> R
    where
        F: FnOnce(&mut PeerNetwork, &mut HttpPeer) -> R,
    {
        let mut http = network
            .http
            .take()
            .expect("BUG: HTTP peer is not instantiated");
        let res = to_do(network, &mut http);
        network.http = Some(http);
        res
    }

    /// start serving.
    pub fn bind(&mut self, my_addr: &SocketAddr, http_addr: &SocketAddr) -> Result<(), net_error> {
        let mut net = NetworkState::new(self.connection_opts.max_sockets)?;

        let p2p_handle = net.bind(my_addr)?;
        let http_handle = net.bind(http_addr)?;

        test_debug!(
            "{:?}: bound on p2p {:?}, http {:?}",
            &self.local_peer,
            my_addr,
            http_addr
        );

        self.network = Some(net);
        self.p2p_network_handle = p2p_handle;
        self.http_network_handle = http_handle;

        PeerNetwork::with_http(self, |_, ref mut http| {
            http.set_server_handle(http_handle);
        });

        self.bind_nk = NeighborKey {
            network_id: self.local_peer.network_id,
            peer_version: self.peer_version,
            addrbytes: PeerAddress::from_socketaddr(my_addr),
            port: my_addr.port(),
        };

        Ok(())
    }

    /// Run a closure with the network state
    pub fn with_network_state<F, R>(
        peer_network: &mut PeerNetwork,
        closure: F,
    ) -> Result<R, net_error>
    where
        F: FnOnce(&mut PeerNetwork, &mut NetworkState) -> Result<R, net_error>,
    {
        let mut net = peer_network.network.take();
        let res = match net {
            Some(ref mut network_state) => closure(peer_network, network_state),
            None => {
                return Err(net_error::NotConnected);
            }
        };
        peer_network.network = net;
        res
    }

    /// Run a closure with the attachments_downloader
    pub fn with_attachments_downloader<F, R>(
        peer_network: &mut PeerNetwork,
        closure: F,
    ) -> Result<R, net_error>
    where
        F: FnOnce(&mut PeerNetwork, &mut AttachmentsDownloader) -> Result<R, net_error>,
    {
        let mut attachments_downloader = peer_network.attachments_downloader.take();
        let res = match attachments_downloader {
            Some(ref mut attachments_downloader) => closure(peer_network, attachments_downloader),
            None => {
                return Err(net_error::NotConnected);
            }
        };
        peer_network.attachments_downloader = attachments_downloader;
        res
    }

    /// Create a network handle for another thread to use to communicate with remote peers
    pub fn new_handle(&mut self, bufsz: usize) -> NetworkHandle {
        let (server, client) = NetworkHandleServer::pair(bufsz);
        self.handles.push_back(server);
        client
    }

    /// Saturate a socket with a reply handle
    /// Return (number of bytes sent, whether or not there's more to send)
    fn do_saturate_p2p_socket(
        convo: &mut ConversationP2P,
        client_sock: &mut mio::net::TcpStream,
        handle: &mut ReplyHandleP2P,
    ) -> Result<(usize, bool), net_error> {
        let mut total_sent = 0;
        let mut flushed;

        loop {
            flushed = handle.try_flush()?;
            let send_res = convo.send(client_sock);
            match send_res {
                Err(e) => {
                    debug!("Failed to send data to socket {:?}: {:?}", client_sock, &e);
                    return Err(e);
                }
                Ok(sz) => {
                    total_sent += sz;
                    if sz == 0 {
                        break;
                    }
                }
            }
        }

        Ok((total_sent, flushed))
    }

    /// Saturate a socket with a reply handle.
    /// Return (number of bytes sent, whether or not there's more to send)
    pub fn saturate_p2p_socket(
        &mut self,
        event_id: usize,
        handle: &mut ReplyHandleP2P,
    ) -> Result<(usize, bool), net_error> {
        let convo_opt = self.peers.get_mut(&event_id);
        if convo_opt.is_none() {
            debug!("No open socket for {}", event_id);
            return Err(net_error::PeerNotConnected);
        }

        let socket_opt = self.sockets.get_mut(&event_id);
        if socket_opt.is_none() {
            debug!("No open socket for {}", event_id);
            return Err(net_error::PeerNotConnected);
        }

        let convo = convo_opt.unwrap();
        let client_sock = socket_opt.unwrap();

        PeerNetwork::do_saturate_p2p_socket(convo, client_sock, handle)
    }

    /// Send a message to a peer.
    /// Non-blocking -- caller has to call .try_flush() or .flush() on the resulting handle to make sure the data is
    /// actually sent.
    pub fn send_message(
        &mut self,
        neighbor_key: &NeighborKey,
        message: StacksMessage,
        ttl: u64,
    ) -> Result<ReplyHandleP2P, net_error> {
        let event_id_opt = self.events.get(&neighbor_key);
        if event_id_opt.is_none() {
            info!("Not connected to {:?}", &neighbor_key);
            return Err(net_error::NoSuchNeighbor);
        }

        let event_id = *(event_id_opt.unwrap());
        let convo_opt = self.peers.get_mut(&event_id);
        if convo_opt.is_none() {
            info!("No ongoing conversation with {:?}", &neighbor_key);
            return Err(net_error::PeerNotConnected);
        }

        let convo = convo_opt.unwrap();

        let mut rh = convo.send_signed_request(message, ttl)?;
        self.saturate_p2p_socket(event_id, &mut rh)?;

        // caller must send the remainder
        Ok(rh)
    }

    fn add_relay_handle(&mut self, event_id: usize, relay_handle: ReplyHandleP2P) -> () {
        if let Some(handle_list) = self.relay_handles.get_mut(&event_id) {
            handle_list.push_back(relay_handle);
        } else {
            let mut handle_list = VecDeque::new();
            handle_list.push_back(relay_handle);
            self.relay_handles.insert(event_id, handle_list);
        }
    }

    /// Relay a signed message to a peer.
    /// The peer network will take care of sending the data; no need to deal with a reply handle.
    /// Called from _within_ the p2p thread.
    pub fn relay_signed_message(
        &mut self,
        neighbor_key: &NeighborKey,
        message: StacksMessage,
    ) -> Result<(), net_error> {
        let event_id = {
            let event_id_opt = self.events.get(&neighbor_key);
            if event_id_opt.is_none() {
                info!("Not connected to {:?}", &neighbor_key);
                return Err(net_error::NoSuchNeighbor);
            }

            *(event_id_opt.unwrap())
        };

        let convo_opt = self.peers.get_mut(&event_id);
        if convo_opt.is_none() {
            info!("No ongoing conversation with {:?}", &neighbor_key);
            return Err(net_error::PeerNotConnected);
        }

        let convo = convo_opt.unwrap();
        let mut reply_handle = convo.relay_signed_message(message)?;

        let (num_sent, flushed) = self.saturate_p2p_socket(event_id, &mut reply_handle)?;
        if num_sent > 0 || !flushed {
            // keep trying to send
            self.add_relay_handle(event_id, reply_handle);
        }
        Ok(())
    }

    /// Broadcast a message to a list of neighbors
    pub fn broadcast_message(
        &mut self,
        mut neighbor_keys: Vec<NeighborKey>,
        relay_hints: Vec<RelayData>,
        message_payload: StacksMessageType,
    ) -> () {
        debug!(
            "{:?}: Will broadcast '{}' to up to {} neighbors; relayed by {:?}",
            &self.local_peer,
            message_payload.get_message_description(),
            neighbor_keys.len(),
            &relay_hints
        );
        for nk in neighbor_keys.drain(..) {
            if let Some(event_id) = self.events.get(&nk) {
                let event_id = *event_id;
                if let Some(convo) = self.peers.get_mut(&event_id) {
                    // safety check -- don't send to someone who has already been a relayer
                    let mut do_relay = true;
                    if let Some(pubkey) = convo.ref_public_key() {
                        let pubkey_hash = Hash160::from_node_public_key(pubkey);
                        for rhint in relay_hints.iter() {
                            if rhint.peer.public_key_hash == pubkey_hash {
                                do_relay = false;
                                break;
                            }
                        }
                    }
                    if !do_relay {
                        debug!(
                            "{:?}: Do not broadcast '{}' to {:?}: it has already relayed it",
                            &self.local_peer,
                            message_payload.get_message_description(),
                            &nk
                        );
                        continue;
                    }

                    match convo.sign_and_forward(
                        &self.local_peer,
                        &self.chain_view,
                        relay_hints.clone(),
                        message_payload.clone(),
                    ) {
                        Ok(rh) => {
                            debug!(
                                "{:?}: Broadcasted '{}' to {:?}",
                                &self.local_peer,
                                message_payload.get_message_description(),
                                &nk
                            );
                            self.add_relay_handle(event_id, rh);
                        }
                        Err(e) => {
                            warn!(
                                "{:?}: Failed to broadcast message to {:?}: {:?}",
                                &self.local_peer, nk, &e
                            );
                        }
                    }
                } else {
                    debug!(
                        "{:?}: No open conversation for {:?}; will not broadcast {:?} to it",
                        &self.local_peer,
                        &nk,
                        message_payload.get_message_description()
                    );
                }
            } else {
                debug!(
                    "{:?}: No connection open to {:?}; will not broadcast {:?} to it",
                    &self.local_peer,
                    &nk,
                    message_payload.get_message_description()
                );
            }
        }
        debug!(
            "{:?}: Done broadcasting '{}",
            &self.local_peer,
            message_payload.get_message_description()
        );
    }

    /// Count how many outbound conversations are going on
    pub fn count_outbound_conversations(peers: &PeerMap) -> u64 {
        let mut ret = 0;
        for (_, convo) in peers.iter() {
            if convo.stats.outbound {
                ret += 1;
            }
        }
        ret
    }

    /// Count how many connections to a given IP address we have
    pub fn count_ip_connections(
        ipaddr: &SocketAddr,
        sockets: &HashMap<usize, mio_net::TcpStream>,
    ) -> u64 {
        let mut ret = 0;
        for (_, socket) in sockets.iter() {
            match socket.peer_addr() {
                Ok(addr) => {
                    if addr.ip() == ipaddr.ip() {
                        ret += 1;
                    }
                }
                Err(_) => {}
            };
        }
        ret
    }

    /// Connect to a peer.
    /// Idempotent -- will not re-connect if already connected.
    /// Fails if the peer is denied.
    pub fn connect_peer(&mut self, neighbor: &NeighborKey) -> Result<usize, net_error> {
        self.connect_peer_deny_checks(neighbor, true)
    }

    /// Connect to a peer, optionally checking our deny information.
    /// Idempotent -- will not re-connect if already connected.
    /// Fails if the peer is denied.
    fn connect_peer_deny_checks(
        &mut self,
        neighbor: &NeighborKey,
        check_denied: bool,
    ) -> Result<usize, net_error> {
        debug!("{:?}: connect to {:?}", &self.local_peer, neighbor);

        if check_denied {
            // don't talk to our bind address
            if self.is_bound(neighbor) {
                debug!(
                    "{:?}: do not connect to myself at {:?}",
                    &self.local_peer, neighbor
                );
                return Err(net_error::Denied);
            }

            // don't talk if denied
            if PeerDB::is_peer_denied(
                &self.peerdb.conn(),
                neighbor.network_id,
                &neighbor.addrbytes,
                neighbor.port,
            )? {
                debug!(
                    "{:?}: Neighbor {:?} is denied; will not connect",
                    &self.local_peer, neighbor
                );
                return Err(net_error::Denied);
            }
        }

        // already connected?
        if let Some(event_id) = self.get_event_id(neighbor) {
            debug!(
                "{:?}: already connected to {:?} as event {}",
                &self.local_peer, neighbor, event_id
            );
            return Ok(event_id);
        }

        let next_event_id = match self.network {
            None => {
                test_debug!("{:?}: network not connected", &self.local_peer);
                return Err(net_error::NotConnected);
            }
            Some(ref mut network) => {
                let sock = NetworkState::connect(&neighbor.addrbytes.to_socketaddr(neighbor.port))?;
                let hint_event_id = network.next_event_id()?;
                let registered_event_id =
                    network.register(self.p2p_network_handle, hint_event_id, &sock)?;

                self.connecting
                    .insert(registered_event_id, (sock, true, get_epoch_time_secs()));
                registered_event_id
            }
        };

        Ok(next_event_id)
    }

    /// Given a list of neighbors keys, find the _set_ of neighbor keys that represent unique
    /// connections.  This is used by the broadcast logic to ensure that we only send a message to
    /// a peer once, even if we have both an inbound and outbound connection to it.
    fn coalesce_neighbors(&self, neighbors: Vec<NeighborKey>) -> Vec<NeighborKey> {
        let mut seen = HashSet::new();
        let mut unique = HashSet::new();
        for nk in neighbors.into_iter() {
            if seen.contains(&nk) {
                continue;
            }

            unique.insert(nk.clone());

            // don't include its reciprocal connection
            if let Some(event_id) = self.events.get(&nk) {
                if let Some(other_event_id) = self.find_reciprocal_event(*event_id) {
                    if let Some(other_convo) = self.peers.get(&other_event_id) {
                        let other_nk = other_convo.to_neighbor_key();
                        seen.insert(other_nk);
                        seen.insert(nk);
                    }
                }
            }
        }
        unique.into_iter().collect::<Vec<NeighborKey>>()
    }

    /// Sample the available connections to broadcast on.
    /// Up to MAX_BROADCAST_OUTBOUND_PEERS outbound connections will be used.
    /// Up to MAX_BROADCAST_INBOUND_PEERS inbound connections will be used.
    /// The outbound will be sampled according to their AS distribution
    /// The inbound will be sampled according to how rarely they send duplicate messages.
    /// The final set of message recipients will be coalesced -- if we have an inbound and outbound
    /// connection to the same neighbor, only one connection will be used.
    fn sample_broadcast_peers<R: RelayPayload>(
        &self,
        relay_hints: &Vec<RelayData>,
        payload: &R,
    ) -> Result<Vec<NeighborKey>, net_error> {
        // coalesce
        let mut outbound_neighbors = vec![];
        let mut inbound_neighbors = vec![];

        for (_, convo) in self.peers.iter() {
            if !convo.is_authenticated() {
                continue;
            }
            let nk = convo.to_neighbor_key();
            if convo.is_outbound() {
                outbound_neighbors.push(nk);
            } else {
                inbound_neighbors.push(nk);
            }
        }

        let mut outbound_dist = self
            .relayer_stats
            .get_outbound_relay_rankings(&self.peerdb, &outbound_neighbors)?;
        let mut inbound_dist = self.relayer_stats.get_inbound_relay_rankings(
            &inbound_neighbors,
            payload,
            RELAY_DUPLICATE_INFERENCE_WARMUP,
        );

        let mut relay_pubkhs = HashSet::new();
        for rhint in relay_hints {
            relay_pubkhs.insert(rhint.peer.public_key_hash.clone());
        }

        // don't send a message to anyone who sent this message to us
        for (_, convo) in self.peers.iter() {
            if let Some(pubkey) = convo.ref_public_key() {
                let pubkey_hash = Hash160::from_node_public_key(pubkey);
                if relay_pubkhs.contains(&pubkey_hash) {
                    let nk = convo.to_neighbor_key();
                    debug!(
                        "{:?}: Do not forward {} to {:?}, since it already saw this message",
                        &self.local_peer,
                        payload.get_id(),
                        &nk
                    );
                    outbound_dist.remove(&nk);
                    inbound_dist.remove(&nk);
                }
            }
        }

        debug!(
            "Inbound recipient distribution (out of {}): {:?}",
            inbound_neighbors.len(),
            &inbound_dist
        );
        debug!(
            "Outbound recipient distribution (out of {}): {:?}",
            outbound_neighbors.len(),
            &outbound_dist
        );

        let mut outbound_sample =
            RelayerStats::sample_neighbors(outbound_dist, MAX_BROADCAST_OUTBOUND_RECEIVERS);
        let mut inbound_sample =
            RelayerStats::sample_neighbors(inbound_dist, MAX_BROADCAST_INBOUND_RECEIVERS);

        debug!(
            "Inbound recipients (out of {}): {:?}",
            inbound_neighbors.len(),
            &inbound_sample
        );
        debug!(
            "Outbound recipients (out of {}): {:?}",
            outbound_neighbors.len(),
            &outbound_sample
        );

        outbound_sample.append(&mut inbound_sample);
        let ret = self.coalesce_neighbors(outbound_sample);

        debug!("All recipients (out of {}): {:?}", ret.len(), &ret);
        Ok(ret)
    }

    /// Dispatch a single request from another thread.
    pub fn dispatch_request(&mut self, request: NetworkRequest) -> Result<(), net_error> {
        match request {
            NetworkRequest::Ban(neighbor_keys) => {
                for neighbor_key in neighbor_keys.iter() {
                    debug!("Request to ban {:?}", neighbor_key);
                    match self.events.get(neighbor_key) {
                        Some(event_id) => {
                            debug!("Will ban {:?} (event {})", neighbor_key, event_id);
                            self.bans.insert(*event_id);
                        }
                        None => {}
                    }
                }
                Ok(())
            }
            NetworkRequest::AdvertizeBlocks(blocks) => {
                if !(cfg!(test) && self.connection_opts.disable_block_advertisement) {
                    self.advertize_blocks(blocks)?;
                }
                Ok(())
            }
            NetworkRequest::AdvertizeMicroblocks(mblocks) => {
                if !(cfg!(test) && self.connection_opts.disable_block_advertisement) {
                    self.advertize_microblocks(mblocks)?;
                }
                Ok(())
            }
            NetworkRequest::Relay(neighbor_key, msg) => self
                .relay_signed_message(&neighbor_key, msg)
                .and_then(|_| Ok(())),
            NetworkRequest::Broadcast(relay_hints, msg) => {
                // pick some neighbors. Note that only some messages can be broadcasted.
                let neighbor_keys = match msg {
                    StacksMessageType::Blocks(ref data) => {
                        // send to each neighbor that needs one
                        let mut all_neighbors = HashSet::new();
                        for (_, block) in data.blocks.iter() {
                            let mut neighbors = self.sample_broadcast_peers(&relay_hints, block)?;
                            for nk in neighbors.drain(..) {
                                all_neighbors.insert(nk);
                            }
                        }
                        Ok(all_neighbors.into_iter().collect())
                    }
                    StacksMessageType::Microblocks(ref data) => {
                        // send to each neighbor that needs at least one
                        let mut all_neighbors = HashSet::new();
                        for mblock in data.microblocks.iter() {
                            let mut neighbors =
                                self.sample_broadcast_peers(&relay_hints, mblock)?;
                            for nk in neighbors.drain(..) {
                                all_neighbors.insert(nk);
                            }
                        }
                        Ok(all_neighbors.into_iter().collect())
                    }
                    StacksMessageType::Transaction(ref data) => {
                        self.sample_broadcast_peers(&relay_hints, data)
                    }
                    _ => {
                        // not suitable for broadcast
                        return Err(net_error::InvalidMessage);
                    }
                }?;
                self.broadcast_message(neighbor_keys, relay_hints, msg);
                Ok(())
            }
        }
    }

    /// Process any handle requests from other threads.
    /// Returns the number of requests dispatched.
    /// This method does not block.
    fn dispatch_requests(&mut self) {
        let mut to_remove = vec![];
        let mut messages = vec![];
        let mut responses = vec![];

        // receive all in-bound requests
        for i in 0..self.handles.len() {
            match self.handles.get(i) {
                Some(ref handle) => {
                    loop {
                        // drain all inbound requests
                        let inbound_request_res = handle.chan_in.try_recv();
                        match inbound_request_res {
                            Ok(inbound_request) => {
                                messages.push((i, inbound_request));
                            }
                            Err(TryRecvError::Empty) => {
                                // nothing to do
                                break;
                            }
                            Err(TryRecvError::Disconnected) => {
                                // dead; remove
                                to_remove.push(i);
                                break;
                            }
                        }
                    }
                }
                None => {}
            }
        }

        // dispatch all in-bound requests from waiting threads
        for (i, inbound_request) in messages {
            let inbound_str = format!("{:?}", &inbound_request);
            let dispatch_res = self.dispatch_request(inbound_request);
            responses.push((i, inbound_str, dispatch_res));
        }

        for (i, inbound_str, dispatch_res) in responses {
            if let Err(e) = dispatch_res {
                warn!(
                    "P2P client channel {}: request '{:?}' failed: '{:?}'",
                    i, &inbound_str, &e
                );
            }
        }

        // clear out dead handles
        to_remove.reverse();
        for i in to_remove {
            self.handles.remove(i);
        }
    }

    /// Process ban requests.  Update the deny in the peer database.  Return the vec of event IDs to disconnect from.
    fn process_bans(&mut self) -> Result<Vec<usize>, net_error> {
        if cfg!(test) && self.connection_opts.disable_network_bans {
            return Ok(vec![]);
        }

        let mut tx = self.peerdb.tx_begin()?;
        let mut disconnect = vec![];
        for event_id in self.bans.drain() {
            let (neighbor_key, neighbor_info_opt) = match self.peers.get(&event_id) {
                Some(convo) => match Neighbor::from_conversation(&tx, convo)? {
                    Some(neighbor) => {
                        if neighbor.is_allowed() {
                            debug!(
                                "Misbehaving neighbor {:?} is allowed; will not punish",
                                &neighbor.addr
                            );
                            continue;
                        }
                        (convo.to_neighbor_key(), Some(neighbor))
                    }
                    None => {
                        test_debug!(
                            "No such neighbor in peer DB, but will ban nevertheless: {:?}",
                            convo.to_neighbor_key()
                        );
                        (convo.to_neighbor_key(), None)
                    }
                },
                None => {
                    continue;
                }
            };

            disconnect.push(event_id);

            let now = get_epoch_time_secs();
            let penalty = if let Some(neighbor_info) = neighbor_info_opt {
                if neighbor_info.denied < 0
                    || (neighbor_info.denied as u64) < now + DENY_MIN_BAN_DURATION
                {
                    now + DENY_MIN_BAN_DURATION
                } else {
                    // already recently penalized; make ban length grow exponentially
                    if ((neighbor_info.denied as u64) - now) * 2 < DENY_BAN_DURATION {
                        now + ((neighbor_info.denied as u64) - now) * 2
                    } else {
                        now + DENY_BAN_DURATION
                    }
                }
            } else {
                now + DENY_BAN_DURATION
            };

            debug!(
                "Ban peer {:?} for {}s until {}",
                &neighbor_key,
                penalty - now,
                penalty
            );

            PeerDB::set_deny_peer(
                &mut tx,
                neighbor_key.network_id,
                &neighbor_key.addrbytes,
                neighbor_key.port,
                penalty,
            )?;
        }

        tx.commit()?;
        Ok(disconnect)
    }

    /// Get the neighbor if we know of it and it's public key is unexpired.
    fn lookup_peer(
        &self,
        cur_block_height: u64,
        peer_addr: &SocketAddr,
    ) -> Result<Option<Neighbor>, net_error> {
        let conn = self.peerdb.conn();
        let addrbytes = PeerAddress::from_socketaddr(peer_addr);
        let neighbor_opt = PeerDB::get_peer(
            conn,
            self.local_peer.network_id,
            &addrbytes,
            peer_addr.port(),
        )
        .map_err(net_error::DBError)?;

        match neighbor_opt {
            None => Ok(None),
            Some(neighbor) => {
                if neighbor.expire_block < cur_block_height {
                    Ok(Some(neighbor))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Get number of inbound connections we're servicing
    pub fn num_peers(&self) -> usize {
        self.sockets.len()
    }

    /// Is a node with the given public key hash registered?
    /// Return the event IDs if so
    pub fn get_pubkey_events(&self, pubkh: &Hash160) -> Vec<usize> {
        let mut ret = vec![];
        for (event_id, convo) in self.peers.iter() {
            if convo.is_authenticated() {
                if let Some(convo_pubkh) = convo.get_public_key_hash() {
                    if convo_pubkh == *pubkh {
                        ret.push(*event_id);
                    }
                }
            }
        }
        ret
    }

    /// Find the neighbor key bound to an event ID
    pub fn get_event_neighbor_key(&self, event_id: usize) -> Option<NeighborKey> {
        for (nk, eid) in self.events.iter() {
            if *eid == event_id {
                return Some(nk.clone());
            }
        }
        None
    }

    /// Is an event ID connecting?
    pub fn is_connecting(&self, event_id: usize) -> bool {
        self.connecting.contains_key(&event_id)
    }

    /// Is this neighbor key the same as the one that represents our p2p bind address?
    pub fn is_bound(&self, neighbor_key: &NeighborKey) -> bool {
        self.bind_nk.network_id == neighbor_key.network_id
            && self.bind_nk.addrbytes == neighbor_key.addrbytes
            && self.bind_nk.port == neighbor_key.port
    }

    /// Check to see if we can register the given socket
    /// * we can't have registered this neighbor already
    /// * if this is inbound, we can't add more than self.num_clients
    pub fn can_register_peer(
        &mut self,
        neighbor_key: &NeighborKey,
        outbound: bool,
    ) -> Result<(), net_error> {
        // don't talk to our bind address
        if self.is_bound(neighbor_key) {
            debug!(
                "{:?}: do not register myself at {:?}",
                &self.local_peer, neighbor_key
            );
            return Err(net_error::Denied);
        }

        // denied?
        if PeerDB::is_peer_denied(
            &self.peerdb.conn(),
            neighbor_key.network_id,
            &neighbor_key.addrbytes,
            neighbor_key.port,
        )? {
            info!(
                "{:?}: Peer {:?} is denied; dropping",
                &self.local_peer, neighbor_key
            );
            return Err(net_error::Denied);
        }

        // already connected?
        if let Some(event_id) = self.get_event_id(&neighbor_key) {
            test_debug!(
                "{:?}: already connected to {:?} on event {}",
                &self.local_peer,
                &neighbor_key,
                event_id
            );
            return Err(net_error::AlreadyConnected(event_id, neighbor_key.clone()));
        }

        // consider rate-limits on in-bound peers
        let num_outbound = PeerNetwork::count_outbound_conversations(&self.peers);
        if !outbound && (self.peers.len() as u64) - num_outbound >= self.connection_opts.num_clients
        {
            // too many inbounds
            info!("{:?}: Too many inbound connections", &self.local_peer);
            return Err(net_error::TooManyPeers);
        }

        Ok(())
    }

    /// Check to see if we can register a peer with a given public key in a given direction
    pub fn can_register_peer_with_pubkey(
        &mut self,
        nk: &NeighborKey,
        outbound: bool,
        pubkh: &Hash160,
    ) -> Result<(), net_error> {
        // can't talk to myself
        let my_pubkey_hash = Hash160::from_node_public_key(&Secp256k1PublicKey::from_private(
            &self.local_peer.private_key,
        ));
        if pubkh == &my_pubkey_hash {
            return Err(net_error::ConnectionCycle);
        }

        self.can_register_peer(nk, outbound).and_then(|_| {
            let other_events = self.get_pubkey_events(pubkh);
            if other_events.len() > 0 {
                for event_id in other_events.into_iter() {
                    if let Some(convo) = self.peers.get(&event_id) {
                        // only care if we're trying to connect in the same direction
                        if outbound == convo.is_outbound() {
                            let nk = self
                                .get_event_neighbor_key(event_id)
                                .ok_or(net_error::PeerNotConnected)?;
                            return Err(net_error::AlreadyConnected(event_id, nk));
                        }
                    }
                }
            }
            return Ok(());
        })
    }

    /// Low-level method to register a socket/event pair on the p2p network interface.
    /// Call only once the socket is registered with the underlying poller (so we can detect
    /// connection events).  If this method fails for some reason, it'll de-register the socket
    /// from the poller.
    /// outbound is true if we are the peer that started the connection (otherwise it's false)
    fn register_peer(
        &mut self,
        event_id: usize,
        socket: mio_net::TcpStream,
        outbound: bool,
    ) -> Result<(), net_error> {
        let client_addr = match socket.peer_addr() {
            Ok(addr) => addr,
            Err(e) => {
                debug!(
                    "{:?}: Failed to get peer address of {:?}: {:?}",
                    &self.local_peer, &socket, &e
                );
                self.deregister_socket(event_id, socket);
                return Err(net_error::SocketError);
            }
        };

        let neighbor_opt = match self.lookup_peer(self.chain_view.burn_block_height, &client_addr) {
            Ok(neighbor_opt) => neighbor_opt,
            Err(e) => {
                debug!("Failed to look up peer {}: {:?}", client_addr, &e);
                self.deregister_socket(event_id, socket);
                return Err(e);
            }
        };

        // NOTE: the neighbor_key will have the same network_id as the remote peer, and the same
        // major version number in the peer_version.  The chat logic won't accept any messages for
        // which this is not true.  Comparison and Hashing are defined for neighbor keys
        // appropriately, so it's okay for us to use self.peer_version and
        // self.local_peer.network_id here for the remote peer's neighbor key.
        let (pubkey_opt, neighbor_key) = match neighbor_opt {
            Some(neighbor) => (Some(neighbor.public_key.clone()), neighbor.addr),
            None => (
                None,
                NeighborKey::from_socketaddr(
                    self.peer_version,
                    self.local_peer.network_id,
                    &client_addr,
                ),
            ),
        };

        match self.can_register_peer(&neighbor_key, outbound) {
            Ok(_) => {}
            Err(e) => {
                debug!(
                    "{:?}: Could not register peer {:?}: {:?}",
                    &self.local_peer, &neighbor_key, &e
                );
                self.deregister_socket(event_id, socket);
                return Err(e);
            }
        }

        let mut new_convo = ConversationP2P::new(
            self.local_peer.network_id,
            self.peer_version,
            &self.burnchain,
            &client_addr,
            &self.connection_opts,
            outbound,
            event_id,
        );
        new_convo.set_public_key(pubkey_opt);

        debug!(
            "{:?}: Registered {} as event {} ({:?},outbound={})",
            &self.local_peer, &client_addr, event_id, &neighbor_key, outbound
        );

        assert!(!self.sockets.contains_key(&event_id));
        assert!(!self.peers.contains_key(&event_id));

        self.sockets.insert(event_id, socket);
        self.peers.insert(event_id, new_convo);
        self.events.insert(neighbor_key, event_id);

        Ok(())
    }

    /// Are we connected to a remote host already?
    pub fn is_registered(&self, neighbor_key: &NeighborKey) -> bool {
        self.events.contains_key(neighbor_key)
    }

    /// Get the event ID associated with a neighbor key
    pub fn get_event_id(&self, neighbor_key: &NeighborKey) -> Option<usize> {
        let event_id_opt = match self.events.get(neighbor_key) {
            Some(eid) => Some(*eid),
            None => None,
        };
        event_id_opt
    }

    /// Get a ref to a conversation given a neighbor key
    pub fn get_convo(&self, neighbor_key: &NeighborKey) -> Option<&ConversationP2P> {
        match self.events.get(neighbor_key) {
            Some(event_id) => self.peers.get(event_id),
            None => None,
        }
    }

    /// Get a ref to a conversation given its event ID
    pub fn get_peer_convo(&self, event_id: usize) -> Option<&ConversationP2P> {
        self.peers.get(&event_id)
    }

    /// Deregister a socket from our p2p network instance.
    fn deregister_socket(&mut self, event_id: usize, socket: mio_net::TcpStream) -> () {
        match self.network {
            Some(ref mut network) => {
                let _ = network.deregister(event_id, &socket);
            }
            None => {}
        }
    }

    /// Deregister a socket/event pair
    pub fn deregister_peer(&mut self, event_id: usize) -> () {
        debug!("{:?}: Disconnect event {}", &self.local_peer, event_id);

        let mut nk_remove: Vec<NeighborKey> = vec![];
        for (neighbor_key, ev_id) in self.events.iter() {
            if *ev_id == event_id {
                nk_remove.push(neighbor_key.clone());
            }
        }

        for nk in nk_remove.into_iter() {
            // remove event state
            self.events.remove(&nk);

            // remove inventory state
            match self.inv_state {
                Some(ref mut inv_state) => {
                    debug!(
                        "{:?}: Remove inventory state for {:?}",
                        &self.local_peer, &nk
                    );
                    inv_state.del_peer(&nk);
                }
                None => {}
            }
        }

        match self.network {
            None => {}
            Some(ref mut network) => {
                // deregister socket if connected and registered already
                if let Some(socket) = self.sockets.remove(&event_id) {
                    let _ = network.deregister(event_id, &socket);
                }
                // deregister socket if still connecting
                if let Some((socket, ..)) = self.connecting.remove(&event_id) {
                    let _ = network.deregister(event_id, &socket);
                }
            }
        }

        self.relay_handles.remove(&event_id);
        self.peers.remove(&event_id);
        self.pending_messages.remove(&event_id);
    }

    /// Deregister by neighbor key
    pub fn deregister_neighbor(&mut self, neighbor_key: &NeighborKey) -> () {
        debug!("Disconnect from {:?}", neighbor_key);
        let event_id = match self.events.get(&neighbor_key) {
            None => {
                return;
            }
            Some(eid) => *eid,
        };
        self.deregister_peer(event_id);
    }

    /// Deregister and ban a neighbor
    pub fn deregister_and_ban_neighbor(&mut self, neighbor: &NeighborKey) -> () {
        debug!("Disconnect from and ban {:?}", neighbor);
        match self.events.get(neighbor) {
            Some(event_id) => {
                self.bans.insert(*event_id);
            }
            None => {}
        }

        self.relayer_stats.process_neighbor_ban(neighbor);
        self.deregister_neighbor(neighbor);
    }

    /// Sign a p2p message to be sent to a particular peer we're having a conversation with.
    /// The peer must already be connected.
    pub fn sign_for_peer(
        &mut self,
        peer_key: &NeighborKey,
        message_payload: StacksMessageType,
    ) -> Result<StacksMessage, net_error> {
        match self.events.get(&peer_key) {
            None => {
                // not connected
                debug!("Could not sign for peer {:?}: not connected", peer_key);
                Err(net_error::PeerNotConnected)
            }
            Some(event_id) => match self.peers.get_mut(&event_id) {
                None => Err(net_error::PeerNotConnected),
                Some(ref mut convo) => convo.sign_message(
                    &self.chain_view,
                    &self.local_peer.private_key,
                    message_payload,
                ),
            },
        }
    }

    /// Process new inbound TCP connections we just accepted.
    /// Returns the event IDs of sockets we need to register
    fn process_new_sockets(
        &mut self,
        poll_state: &mut NetworkPollState,
    ) -> Result<Vec<usize>, net_error> {
        if self.network.is_none() {
            test_debug!("{:?}: network not connected", &self.local_peer);
            return Err(net_error::NotConnected);
        }

        let mut registered = vec![];

        for (hint_event_id, client_sock) in poll_state.new.drain() {
            let event_id = match self.network {
                Some(ref mut network) => {
                    // add to poller
                    let event_id = match network.register(
                        self.p2p_network_handle,
                        hint_event_id,
                        &client_sock,
                    ) {
                        Ok(event_id) => event_id,
                        Err(e) => {
                            warn!("Failed to register {:?}: {:?}", &client_sock, &e);
                            continue;
                        }
                    };

                    // event ID already used?
                    if self.peers.contains_key(&event_id) {
                        warn!(
                            "Already have an event {}: {:?}",
                            event_id,
                            self.peers.get(&event_id)
                        );
                        let _ = network.deregister(event_id, &client_sock);
                        continue;
                    }

                    event_id
                }
                None => {
                    debug!("{:?}: network not connected", &self.local_peer);
                    return Err(net_error::NotConnected);
                }
            };

            // start tracking it
            if let Err(_e) = self.register_peer(event_id, client_sock, false) {
                // NOTE: register_peer will deregister the socket for us
                continue;
            }
            registered.push(event_id);
        }

        Ok(registered)
    }

    /// Process network traffic on a p2p conversation.
    /// Returns list of unhandled messages, and whether or not the convo is still alive.
    fn process_p2p_conversation(
        local_peer: &LocalPeer,
        peerdb: &mut PeerDB,
        sortdb: &SortitionDB,
        pox_id: &PoxId,
        chainstate: &mut StacksChainState,
        header_cache: &mut BlockHeaderCache,
        chain_view: &BurnchainView,
        event_id: usize,
        client_sock: &mut mio_net::TcpStream,
        convo: &mut ConversationP2P,
    ) -> Result<(Vec<StacksMessage>, bool), net_error> {
        // get incoming bytes and update the state of this conversation.
        let mut convo_dead = false;
        let recv_res = convo.recv(client_sock);
        match recv_res {
            Err(e) => {
                match e {
                    net_error::PermanentlyDrained => {
                        // socket got closed, but we might still have pending unsolicited messages
                        debug!(
                            "{:?}: Remote peer disconnected event {} (socket {:?})",
                            local_peer, event_id, &client_sock
                        );
                    }
                    _ => {
                        debug!(
                            "{:?}: Failed to receive data on event {} (socket {:?}): {:?}",
                            local_peer, event_id, &client_sock, &e
                        );
                    }
                }
                convo_dead = true;
            }
            Ok(_) => {}
        }

        // react to inbound messages -- do we need to send something out, or fulfill requests
        // to other threads?  Try to chat even if the recv() failed, since we'll want to at
        // least drain the conversation inbox.
        let chat_res = convo.chat(
            local_peer,
            peerdb,
            sortdb,
            pox_id,
            chainstate,
            header_cache,
            chain_view,
        );
        let unhandled = match chat_res {
            Err(e) => {
                debug!(
                    "Failed to converse on event {} (socket {:?}): {:?}",
                    event_id, &client_sock, &e
                );
                convo_dead = true;
                vec![]
            }
            Ok(unhandled_messages) => unhandled_messages,
        };

        if !convo_dead {
            // (continue) sending out data in this conversation, if the conversation is still
            // ongoing
            let send_res = convo.send(client_sock);
            match send_res {
                Err(e) => {
                    debug!(
                        "Failed to send data to event {} (socket {:?}): {:?}",
                        event_id, &client_sock, &e
                    );
                    convo_dead = true;
                }
                Ok(_) => {}
            }
        }

        Ok((unhandled, !convo_dead))
    }

    /// Process any newly-connecting sockets
    fn process_connecting_sockets(&mut self, poll_state: &mut NetworkPollState) -> () {
        for event_id in poll_state.ready.iter() {
            if self.connecting.contains_key(event_id) {
                let (socket, outbound, _) = self.connecting.remove(event_id).unwrap();
                let sock_str = format!("{:?}", &socket);
                if let Err(_e) = self.register_peer(*event_id, socket, outbound) {
                    debug!(
                        "{:?}: Failed to register connecting socket on event {} ({}): {:?}",
                        &self.local_peer, event_id, sock_str, &_e
                    );
                } else {
                    debug!(
                        "{:?}: Registered peer on event {}: {:?} (outbound={})",
                        &self.local_peer, event_id, sock_str, outbound
                    );
                }
            }
        }
    }

    /// Process sockets that are ready, but specifically inbound or outbound only.
    /// Advance the state of all such conversations with remote peers.
    /// Return the list of events that correspond to failed conversations, as well as the set of
    /// unhandled messages grouped by event_id.
    fn process_ready_sockets(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        poll_state: &mut NetworkPollState,
    ) -> (Vec<usize>, HashMap<usize, Vec<StacksMessage>>) {
        let mut to_remove = vec![];
        let mut unhandled: HashMap<usize, Vec<StacksMessage>> = HashMap::new();

        for event_id in &poll_state.ready {
            if !self.sockets.contains_key(&event_id) {
                test_debug!("Rogue socket event {}", event_id);
                to_remove.push(*event_id);
                continue;
            }

            let client_sock_opt = self.sockets.get_mut(&event_id);
            if client_sock_opt.is_none() {
                test_debug!("No such socket event {}", event_id);
                to_remove.push(*event_id);
                continue;
            }
            let client_sock = client_sock_opt.unwrap();

            match self.peers.get_mut(event_id) {
                Some(ref mut convo) => {
                    // activity on a p2p socket
                    debug!("{:?}: process p2p data from {:?}", &self.local_peer, convo);
                    let mut convo_unhandled = match PeerNetwork::process_p2p_conversation(
                        &self.local_peer,
                        &mut self.peerdb,
                        sortdb,
                        &self.pox_id,
                        chainstate,
                        &mut self.header_cache,
                        &self.chain_view,
                        *event_id,
                        client_sock,
                        convo,
                    ) {
                        Ok((convo_unhandled, alive)) => {
                            if !alive {
                                test_debug!("Connection to {:?} is no longer alive", &convo);
                                to_remove.push(*event_id);
                            }
                            convo_unhandled
                        }
                        Err(_e) => {
                            test_debug!("Connection to {:?} failed: {:?}", &convo, &_e);
                            to_remove.push(*event_id);
                            continue;
                        }
                    };

                    // forward along unhandled messages from this peer
                    if unhandled.contains_key(event_id) {
                        unhandled
                            .get_mut(event_id)
                            .unwrap()
                            .append(&mut convo_unhandled);
                    } else {
                        unhandled.insert(*event_id, convo_unhandled);
                    }
                }
                None => {
                    warn!("Rogue event {} for socket {:?}", event_id, &client_sock);
                    to_remove.push(*event_id);
                }
            }
        }

        (to_remove, unhandled)
    }

    /// Get stats for a neighbor
    pub fn get_neighbor_stats(&self, nk: &NeighborKey) -> Option<NeighborStats> {
        match self.events.get(&nk) {
            None => None,
            Some(eid) => match self.peers.get(&eid) {
                None => None,
                Some(ref convo) => Some(convo.stats.clone()),
            },
        }
    }

    /// Update peer connections as a result of a peer graph walk.
    /// -- Drop broken connections.
    /// -- Update our frontier.
    /// -- Prune our frontier if it gets too big.
    fn process_neighbor_walk(&mut self, walk_result: NeighborWalkResult) -> () {
        for broken in walk_result.broken_connections.iter() {
            self.deregister_and_ban_neighbor(broken);
        }

        for dead in walk_result.dead_connections.iter() {
            self.deregister_neighbor(dead);
        }

        for replaced in walk_result.replaced_neighbors.iter() {
            self.deregister_neighbor(replaced);
        }

        // store for later
        self.walk_result = walk_result;
    }

    /// Queue up pings to everyone we haven't spoken to in a while to let them know that we're still
    /// alive.
    pub fn queue_ping_heartbeats(&mut self) -> () {
        let now = get_epoch_time_secs();
        let mut relay_handles = HashMap::new();
        for (_, convo) in self.peers.iter_mut() {
            if convo.is_outbound()
                && convo.is_authenticated()
                && convo.stats.last_handshake_time > 0
                && convo.stats.last_send_time
                    + (convo.heartbeat as u64)
                    + self.connection_opts.neighbor_request_timeout
                    < now
            {
                // haven't talked to this neighbor in a while
                let payload = StacksMessageType::Ping(PingData::new());
                let ping_res =
                    convo.sign_message(&self.chain_view, &self.local_peer.private_key, payload);

                match ping_res {
                    Ok(ping) => {
                        // NOTE: use "relay" here because we don't intend to wait for a reply
                        // (the conversational logic will update our measure of this node's uptime)
                        match convo.relay_signed_message(ping) {
                            Ok(handle) => {
                                relay_handles.insert(convo.conn_id, handle);
                            }
                            Err(_e) => {
                                debug!("Outbox to {:?} is full; cannot ping", &convo);
                            }
                        };
                    }
                    Err(e) => {
                        debug!("Unable to create ping message for {:?}: {:?}", &convo, &e);
                    }
                };
            }
        }
        for (event_id, handle) in relay_handles.drain() {
            self.add_relay_handle(event_id, handle);
        }
    }

    /// Remove unresponsive peers
    fn disconnect_unresponsive(&mut self) -> usize {
        let now = get_epoch_time_secs();
        let mut to_remove = vec![];
        for (event_id, (socket, _, ts)) in self.connecting.iter() {
            if ts + self.connection_opts.connect_timeout < now {
                debug!("{:?}: Disconnect unresponsive connecting peer {:?} (event {}): timed out after {} ({} < {})s", &self.local_peer, socket, event_id, self.connection_opts.timeout, ts + self.connection_opts.timeout, now);
                to_remove.push(*event_id);
            }
        }

        for (event_id, convo) in self.peers.iter() {
            if convo.is_authenticated() {
                // have handshaked with this remote peer
                if convo.stats.last_contact_time
                    + (convo.peer_heartbeat as u64)
                    + self.connection_opts.neighbor_request_timeout
                    < now
                {
                    // we haven't heard from this peer in too long a time
                    debug!(
                        "{:?}: Disconnect unresponsive authenticated peer {:?}: {} + {} + {} < {}",
                        &self.local_peer,
                        &convo,
                        convo.stats.last_contact_time,
                        convo.peer_heartbeat,
                        self.connection_opts.neighbor_request_timeout,
                        now
                    );
                    to_remove.push(*event_id);
                }
            } else {
                // have not handshaked with this remote peer
                if convo.instantiated + self.connection_opts.handshake_timeout < now {
                    debug!(
                        "{:?}: Disconnect unresponsive unauthenticated peer {:?}: {} + {} < {}",
                        &self.local_peer,
                        &convo,
                        convo.instantiated,
                        self.connection_opts.handshake_timeout,
                        now
                    );
                    to_remove.push(*event_id);
                }
            }
        }

        let ret = to_remove.len();
        for event_id in to_remove.into_iter() {
            self.deregister_peer(event_id);
        }
        ret
    }

    /// Prune inbound and outbound connections if we can
    fn prune_connections(&mut self) -> () {
        if cfg!(test) && self.connection_opts.disable_network_prune {
            return;
        }

        debug!("Prune from {} connections", self.events.len());
        let mut safe: HashSet<usize> = HashSet::new();
        let now = get_epoch_time_secs();

        // don't prune allowed peers
        for (nk, event_id) in self.events.iter() {
            let neighbor = match PeerDB::get_peer(
                self.peerdb.conn(),
                self.local_peer.network_id,
                &nk.addrbytes,
                nk.port,
            ) {
                Ok(neighbor_opt) => match neighbor_opt {
                    Some(n) => n,
                    None => {
                        continue;
                    }
                },
                Err(e) => {
                    debug!("Failed to query {:?}: {:?}", &nk, &e);
                    return;
                }
            };
            if neighbor.allowed < 0 || (neighbor.allowed as u64) > now {
                test_debug!(
                    "{:?}: event {} is allowed: {:?}",
                    &self.local_peer,
                    event_id,
                    &nk
                );
                safe.insert(*event_id);
            }
        }

        // if we're in the middle of a peer walk, then don't prune any outbound connections it established
        // (yet)
        match self.walk {
            Some(ref walk) => {
                for event_id in walk.events.iter() {
                    safe.insert(*event_id);
                }
            }
            None => {}
        };

        self.prune_frontier(&safe);
    }

    /// Regenerate our session private key and re-handshake with everyone.
    fn rekey(&mut self, old_local_peer_opt: Option<&LocalPeer>) -> () {
        assert!(old_local_peer_opt.is_some());
        let _old_local_peer = old_local_peer_opt.unwrap();

        // begin re-key
        let mut msgs = HashMap::new();
        for (event_id, convo) in self.peers.iter_mut() {
            let nk = convo.to_neighbor_key();
            let handshake_data = HandshakeData::from_local_peer(&self.local_peer);
            let handshake = StacksMessageType::Handshake(handshake_data);

            debug!(
                "{:?}: send re-key Handshake ({:?} --> {:?}) to {:?}",
                &self.local_peer,
                &to_hex(
                    &Secp256k1PublicKey::from_private(&_old_local_peer.private_key)
                        .to_bytes_compressed()
                ),
                &to_hex(
                    &Secp256k1PublicKey::from_private(&self.local_peer.private_key)
                        .to_bytes_compressed()
                ),
                &nk
            );

            if let Ok(msg) =
                convo.sign_message(&self.chain_view, &_old_local_peer.private_key, handshake)
            {
                msgs.insert(nk, (*event_id, msg));
            }
        }

        for (nk, (event_id, msg)) in msgs.drain() {
            match self.send_message(&nk, msg, self.connection_opts.neighbor_request_timeout) {
                Ok(handle) => {
                    self.add_relay_handle(event_id, handle);
                }
                Err(e) => {
                    info!("Failed to rekey to {:?}: {:?}", &nk, &e);
                }
            }
        }
    }

    /// Flush relayed message handles, but don't block.
    /// Drop broken handles.
    /// Return the list of broken conversation event IDs
    fn flush_relay_handles(&mut self) -> Vec<usize> {
        let mut broken = vec![];
        let mut drained = vec![];

        // flush each outgoing conversation
        for (event_id, handle_list) in self.relay_handles.iter_mut() {
            if handle_list.len() == 0 {
                drained.push(*event_id);
                continue;
            }

            if let (Some(ref mut socket), Some(ref mut convo)) =
                (self.sockets.get_mut(event_id), self.peers.get_mut(event_id))
            {
                while handle_list.len() > 0 {
                    let handle = handle_list.front_mut().unwrap();

                    debug!("Flush relay handle to {:?} ({:?})", socket, convo);
                    let (num_sent, flushed) =
                        match PeerNetwork::do_saturate_p2p_socket(convo, socket, handle) {
                            Ok(x) => x,
                            Err(e) => {
                                info!("Broken connection on event {}: {:?}", event_id, &e);
                                broken.push(*event_id);
                                break;
                            }
                        };

                    if flushed && num_sent == 0 {
                        // message fully sent
                        let handle = handle_list.pop_front().unwrap();

                        // if we're expecting a reply, go consume it out of the underlying
                        // connection
                        if handle.expects_reply() {
                            if let Ok(msg) = handle.try_recv() {
                                debug!(
                                    "Got back internal message {} seq {}",
                                    msg.get_message_name(),
                                    msg.request_id()
                                );
                            }
                        }
                        continue;
                    } else if num_sent == 0 {
                        // saturated
                        break;
                    }
                }
            }
        }

        for empty in drained.drain(..) {
            self.relay_handles.remove(&empty);
        }

        broken
    }

    /// Update the state of our neighbor walk.
    /// Return true if we finish, and true if we're throttled
    fn do_network_neighbor_walk(&mut self) -> Result<bool, net_error> {
        if cfg!(test) && self.connection_opts.disable_neighbor_walk {
            test_debug!("neighbor walk is disabled");
            return Ok(true);
        }

        debug!("{:?}: walk peer graph", &self.local_peer);

        // walk the peer graph and deal with new/dropped connections
        let (done, walk_result_opt) = self.walk_peer_graph();
        match walk_result_opt {
            None => {}
            Some(walk_result) => {
                // remember to prune later, if need be
                self.process_neighbor_walk(walk_result);
            }
        }
        Ok(done)
    }

    /// Begin the process of learning this peer's public IP address.
    /// Return Ok(finished with this step)
    /// Return Err(..) on failure
    fn begin_learn_public_ip(&mut self) -> Result<bool, net_error> {
        if self.peers.len() == 0 {
            return Err(net_error::NoSuchNeighbor);
        }

        debug!("{:?}: begin obtaining public IP address", &self.local_peer);

        // pick a random outbound conversation to one of the initial neighbors
        let mut idx = thread_rng().gen::<usize>() % self.peers.len();
        for _ in 0..self.peers.len() + 1 {
            let event_id = match self.peers.keys().skip(idx).next() {
                Some(eid) => *eid,
                None => {
                    idx = 0;
                    continue;
                }
            };
            idx = (idx + 1) % self.peers.len();

            if let Some(convo) = self.peers.get_mut(&event_id) {
                if !convo.is_authenticated() || !convo.is_outbound() {
                    continue;
                }

                if !PeerDB::is_initial_peer(
                    self.peerdb.conn(),
                    convo.peer_network_id,
                    &convo.peer_addrbytes,
                    convo.peer_port,
                )? {
                    continue;
                }

                debug!("Ask {:?} for my IP address", &convo);

                let nonce = thread_rng().gen::<u32>();
                let natpunch_request = convo
                    .sign_message(
                        &self.chain_view,
                        &self.local_peer.private_key,
                        StacksMessageType::NatPunchRequest(nonce),
                    )
                    .map_err(|e| {
                        info!("Failed to sign NAT punch request: {:?}", &e);
                        e
                    })?;

                let mut rh = convo
                    .send_signed_request(natpunch_request, self.connection_opts.timeout)
                    .map_err(|e| {
                        info!("Failed to send NAT punch request: {:?}", &e);
                        e
                    })?;

                self.saturate_p2p_socket(event_id, &mut rh).map_err(|e| {
                    info!("Failed to saturate NAT punch socket on event {}", &event_id);
                    e
                })?;

                self.public_ip_reply_handle = Some(rh);
                break;
            }
        }

        if self.public_ip_reply_handle.is_none() {
            // no one to talk to
            debug!(
                "{:?}: Did not find any outbound neighbors to ask for a NAT punch reply",
                &self.local_peer
            );
        }
        return Ok(true);
    }

    /// Disconnect from all peers
    fn disconnect_all(&mut self) -> () {
        let mut all_event_ids = vec![];
        for (eid, _) in self.peers.iter() {
            all_event_ids.push(*eid);
        }

        for eid in all_event_ids.into_iter() {
            self.deregister_peer(eid);
        }
    }

    /// Learn this peer's public IP address.
    /// If it was given to us directly, then we can just skip this step.
    /// Once learned, we'll confirm it by trying to self-connect.
    fn do_learn_public_ip(&mut self) -> Result<bool, net_error> {
        if self.public_ip_reply_handle.is_none() {
            if !self.begin_learn_public_ip()? {
                return Ok(false);
            }

            // began request
            self.public_ip_requested_at = get_epoch_time_secs();
            self.public_ip_retries += 1;
        }

        let rh_opt = self.public_ip_reply_handle.take();
        if let Some(mut rh) = rh_opt {
            debug!(
                "{:?}: waiting for NatPunchReply on event {}",
                &self.local_peer,
                rh.get_event_id()
            );

            if let Err(e) = self.saturate_p2p_socket(rh.get_event_id(), &mut rh) {
                info!(
                    "{:?}: Failed to query my public IP address: {:?}",
                    &self.local_peer, &e
                );
                return Err(e);
            }

            match rh.try_send_recv() {
                Ok(message) => match message.payload {
                    StacksMessageType::NatPunchReply(data) => {
                        // peer offers us our public IP address.
                        debug!(
                            "{:?}: learned that my IP address is {:?}",
                            &self.local_peer, &data.addrbytes
                        );
                        self.public_ip_confirmed = true;
                        self.public_ip_learned_at = get_epoch_time_secs();
                        self.public_ip_retries = 0;

                        // if our IP address changed, then disconnect witih everyone
                        let old_ip = self.local_peer.public_ip_address.clone();
                        self.local_peer.public_ip_address =
                            Some((data.addrbytes, self.bind_nk.port));

                        if old_ip != self.local_peer.public_ip_address {
                            info!(
                                "IP address changed from {:?} to {:?}",
                                &old_ip, &self.local_peer.public_ip_address
                            );
                        }
                        return Ok(true);
                    }
                    other_payload => {
                        debug!(
                            "{:?}: Got unexpected payload {:?}",
                            &self.local_peer, &other_payload
                        );

                        // restart
                        return Err(net_error::InvalidMessage);
                    }
                },
                Err(req_res) => match req_res {
                    Ok(same_req) => {
                        // try again
                        self.public_ip_reply_handle = Some(same_req);
                        return Ok(false);
                    }
                    Err(e) => {
                        // disconnected
                        debug!(
                            "{:?}: Failed to get a NatPunchReply reply: {:?}",
                            &self.local_peer, &e
                        );
                        return Err(e);
                    }
                },
            }
        }

        return Ok(true);
    }

    /// Do we need to (re)fetch our public IP?
    fn need_public_ip(&mut self) -> bool {
        if !self.public_ip_learned {
            // IP was given, not learned.  nothing to do
            test_debug!("{:?}: IP address was given to us", &self.local_peer);
            return false;
        }
        if self.local_peer.public_ip_address.is_some()
            && self.public_ip_learned_at + self.connection_opts.public_ip_timeout
                >= get_epoch_time_secs()
        {
            // still fresh
            test_debug!("{:?}: learned IP address is still fresh", &self.local_peer);
            return false;
        }
        let throttle_timeout = if self.local_peer.public_ip_address.is_none() {
            self.connection_opts.public_ip_request_timeout
        } else {
            self.connection_opts.public_ip_timeout
        };

        if self.public_ip_retries > self.connection_opts.public_ip_max_retries {
            if self.public_ip_requested_at + throttle_timeout >= get_epoch_time_secs() {
                // throttle
                debug!(
                    "{:?}: throttle public IP request (max retries {} exceeded) until {}",
                    &self.local_peer,
                    self.public_ip_retries,
                    self.public_ip_requested_at + throttle_timeout
                );
                return false;
            } else {
                // try again
                self.public_ip_retries = 0;
            }
        }

        return true;
    }

    /// Reset all state for querying our public IP address
    fn public_ip_reset(&mut self) {
        debug!("{:?}: reset public IP query state", &self.local_peer);

        self.public_ip_reply_handle = None;
        self.public_ip_confirmed = false;

        if self.public_ip_learned {
            // will go relearn it if it wasn't given
            self.local_peer.public_ip_address = None;
        }
    }

    /// Learn our publicly-routable IP address
    fn do_get_public_ip(&mut self) -> Result<bool, net_error> {
        if !self.need_public_ip() {
            return Ok(true);
        }
        if self.local_peer.public_ip_address.is_some()
            && self.public_ip_requested_at + self.connection_opts.public_ip_request_timeout
                >= get_epoch_time_secs()
        {
            // throttle
            debug!(
                "{:?}: throttle public IP request query until {}",
                &self.local_peer,
                self.public_ip_requested_at + self.connection_opts.public_ip_request_timeout
            );
            return Ok(true);
        }

        match self.do_learn_public_ip() {
            Ok(b) => {
                if !b {
                    test_debug!("{:?}: try do_learn_public_ip again", &self.local_peer);
                    return Ok(false);
                }
            }
            Err(e) => {
                test_debug!(
                    "{:?}: failed to learn public IP: {:?}",
                    &self.local_peer,
                    &e
                );
                self.public_ip_reset();

                match e {
                    net_error::NoSuchNeighbor => {
                        // haven't connected to anyone yet
                        return Ok(true);
                    }
                    _ => {
                        return Err(e);
                    }
                };
            }
        }
        Ok(true)
    }

    /// Update the state of our neighbors' block inventories.
    /// Return true if we finish
    fn do_network_inv_sync(
        &mut self,
        sortdb: &SortitionDB,
        ibd: bool,
    ) -> Result<(bool, bool), net_error> {
        if cfg!(test) && self.connection_opts.disable_inv_sync {
            test_debug!("{:?}: inv sync is disabled", &self.local_peer);
            return Ok((true, false));
        }

        debug!("{:?}: network inventory sync", &self.local_peer);

        if self.inv_state.is_none() {
            self.init_inv_sync(sortdb);
        }

        // synchronize peer block inventories
        let (done, throttled, broken_neighbors, dead_neighbors) =
            self.sync_inventories(sortdb, ibd)?;

        // disconnect and ban broken peers
        for broken in broken_neighbors.into_iter() {
            self.deregister_and_ban_neighbor(&broken);
        }

        // disconnect from dead connections
        for dead in dead_neighbors.into_iter() {
            self.deregister_neighbor(&dead);
        }

        Ok((done, throttled))
    }

    /// Download blocks, and add them to our network result.
    fn do_network_block_download(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        dns_client: &mut DNSClient,
        ibd: bool,
        network_result: &mut NetworkResult,
    ) -> Result<bool, net_error> {
        if self.connection_opts.disable_block_download {
            debug!("{:?}: block download is disabled", &self.local_peer);
            return Ok(true);
        }

        if self.block_downloader.is_none() {
            self.init_block_downloader();
        }

        let (
            done,
            at_chain_tip,
            old_pox_id,
            mut blocks,
            mut microblocks,
            mut broken_http_peers,
            mut broken_p2p_peers,
        ) = match self.download_blocks(sortdb, chainstate, dns_client, ibd) {
            Ok(x) => x,
            Err(net_error::NotConnected) => {
                // there was simply nothing to do
                debug!(
                    "{:?}: no progress can be made on the block downloader -- not connected",
                    &self.local_peer
                );
                return Ok(true);
            }
            Err(net_error::Transient(s)) => {
                // not fatal, but just skip and try again
                info!("Transient network error while downloading blocks: {}", &s);
                return Ok(true);
            }
            Err(e) => {
                warn!(
                    "{:?}: Failed to download blocks: {:?}",
                    &self.local_peer, &e
                );
                return Err(e);
            }
        };

        network_result.download_pox_id = old_pox_id;
        network_result.blocks.append(&mut blocks);
        network_result
            .confirmed_microblocks
            .append(&mut microblocks);

        if cfg!(test) {
            let mut block_set = HashSet::new();
            let mut microblock_set = HashSet::new();

            for (_, block, _) in network_result.blocks.iter() {
                if block_set.contains(&block.block_hash()) {
                    test_debug!("Duplicate block {}", block.block_hash());
                }
                block_set.insert(block.block_hash());
            }

            for (_, mblocks, _) in network_result.confirmed_microblocks.iter() {
                for mblock in mblocks.iter() {
                    if microblock_set.contains(&mblock.block_hash()) {
                        test_debug!("Duplicate microblock {}", mblock.block_hash());
                    }
                    microblock_set.insert(mblock.block_hash());
                }
            }
        }

        let _ = PeerNetwork::with_network_state(self, |ref mut network, ref mut network_state| {
            for dead_event in broken_http_peers.drain(..) {
                debug!(
                    "{:?}: De-register dead/broken HTTP connection {}",
                    &network.local_peer, dead_event
                );
                PeerNetwork::with_http(network, |_, http| {
                    http.deregister_http(network_state, dead_event);
                });
            }
            Ok(())
        });

        for broken_neighbor in broken_p2p_peers.drain(..) {
            debug!(
                "{:?}: De-register dead/broken neighbor {:?}",
                &self.local_peer, &broken_neighbor
            );
            self.deregister_and_ban_neighbor(&broken_neighbor);
        }

        if done && at_chain_tip {
            debug!(
                "{:?}: Completed downloader pass {}",
                &self.local_peer,
                self.num_downloader_passes + 1
            );
            self.num_downloader_passes += 1;
        }

        Ok(done && at_chain_tip)
    }

    /// Find the next block to push
    fn find_next_push_block(
        &mut self,
        nk: &NeighborKey,
        reward_cycle: u64,
        height: u64,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
        local_blocks_inv: &BlocksInvData,
        block_stats: &NeighborBlockStats,
    ) -> Result<Option<(ConsensusHash, StacksBlock)>, net_error> {
        let start_block_height = self.burnchain.reward_cycle_to_block_height(reward_cycle);
        if !local_blocks_inv.has_ith_block((height - start_block_height) as u16) {
            return Ok(None);
        }
        if block_stats.inv.get_block_height() >= height && !block_stats.inv.has_ith_block(height) {
            let ancestor_sn = match self.get_ancestor_sortition_snapshot(sortdb, height) {
                Ok(sn) => sn,
                Err(e) => {
                    debug!(
                        "{:?}: AntiEntropy: Failed to query ancestor block height {}: {:?}",
                        &self.local_peer, height, &e
                    );
                    return Ok(None);
                }
            };

            let index_block_hash = StacksBlockHeader::make_index_block_hash(
                &ancestor_sn.consensus_hash,
                &ancestor_sn.winning_stacks_block_hash,
            );
            let block = match StacksChainState::load_block(
                &chainstate.blocks_path,
                &ancestor_sn.consensus_hash,
                &ancestor_sn.winning_stacks_block_hash,
            )? {
                Some(block) => block,
                None => {
                    debug!(
                        "{:?}: AntiEntropy: No such block {}",
                        &self.local_peer, &index_block_hash
                    );
                    return Ok(None);
                }
            };

            debug!(
                "{:?}: AntiEntropy: Peer {:?} is missing Stacks block {} from height {}, which we have",
                &self.local_peer, nk, &index_block_hash, height
            );
            return Ok(Some((ancestor_sn.consensus_hash, block)));
        } else {
            return Ok(None);
        }
    }

    /// Find the next confirmed microblock stream to push.
    fn find_next_push_microblocks(
        &mut self,
        nk: &NeighborKey,
        reward_cycle: u64,
        height: u64,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
        local_blocks_inv: &BlocksInvData,
        block_stats: &NeighborBlockStats,
    ) -> Result<Option<(ConsensusHash, BlockHeaderHash, Vec<StacksMicroblock>)>, net_error> {
        let start_block_height = self.burnchain.reward_cycle_to_block_height(reward_cycle);
        if !local_blocks_inv.has_ith_microblock_stream((height - start_block_height) as u16) {
            return Ok(None);
        }
        if block_stats.inv.get_block_height() >= height
            && !block_stats.inv.has_ith_microblock_stream(height)
        {
            let ancestor_sn = match self.get_ancestor_sortition_snapshot(sortdb, height) {
                Ok(sn) => sn,
                Err(e) => {
                    debug!(
                        "{:?}: AntiEntropy: Failed to query ancestor block height {}: {:?}",
                        &self.local_peer, height, &e
                    );
                    return Ok(None);
                }
            };

            let block_info = match StacksChainState::load_staging_block_info(
                &chainstate.db(),
                &StacksBlockHeader::make_index_block_hash(
                    &ancestor_sn.consensus_hash,
                    &ancestor_sn.winning_stacks_block_hash,
                ),
            ) {
                Ok(Some(x)) => x,
                Ok(None) => {
                    debug!(
                        "{:?}: AntiEntropy: No block stored for {}/{}",
                        &self.local_peer,
                        &ancestor_sn.consensus_hash,
                        &ancestor_sn.winning_stacks_block_hash,
                    );
                    return Ok(None);
                }
                Err(e) => {
                    debug!(
                        "{:?}: AntiEntropy: Failed to query header info of {}/{}: {:?}",
                        &self.local_peer,
                        &ancestor_sn.consensus_hash,
                        &ancestor_sn.winning_stacks_block_hash,
                        &e
                    );
                    return Ok(None);
                }
            };

            let microblocks = match StacksChainState::load_processed_microblock_stream_fork(
                &chainstate.db(),
                &block_info.parent_consensus_hash,
                &block_info.parent_anchored_block_hash,
                &block_info.parent_microblock_hash,
            ) {
                Ok(Some(mblocks)) => mblocks,
                Ok(None) => {
                    debug!(
                        "{:?}: AntiEntropy: No processed microblocks in-between {}/{} and {}/{}",
                        &self.local_peer,
                        &block_info.parent_consensus_hash,
                        &block_info.parent_anchored_block_hash,
                        &block_info.consensus_hash,
                        &block_info.anchored_block_hash,
                    );
                    return Ok(None);
                }
                Err(e) => {
                    debug!("{:?}: AntiEntropy: Failed to load processed microblocks in-between {}/{} and {}/{}: {:?}",
                           &self.local_peer,
                           &block_info.parent_consensus_hash,
                           &block_info.parent_anchored_block_hash,
                           &block_info.consensus_hash,
                           &block_info.anchored_block_hash,
                           &e
                    );
                    return Ok(None);
                }
            };

            let index_block_hash = StacksBlockHeader::make_index_block_hash(
                &block_info.parent_consensus_hash,
                &block_info.parent_anchored_block_hash,
            );
            debug!(
                "{:?}: AntiEntropy: Peer {:?} is missing Stacks microblocks {} from height {}, which we have",
                &self.local_peer, nk, &index_block_hash, height
            );
            return Ok(Some((
                block_info.parent_consensus_hash,
                block_info.parent_anchored_block_hash,
                microblocks,
            )));
        } else {
            return Ok(None);
        }
    }

    /// Push any blocks and microblock streams that we're holding onto out to our neighbors.
    /// Push all but the last arrived Stacks block (the block-push and blocks-available protocols
    /// should handle this, and we don't want the network to DDoS itself to death).
    fn try_push_local_data(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
    ) -> Result<(), net_error> {
        if self.antientropy_last_push_ts + self.connection_opts.antientropy_retry
            >= get_epoch_time_secs()
        {
            return Ok(());
        }

        self.antientropy_last_push_ts = get_epoch_time_secs();

        let num_public_inbound = self.count_public_inbound();
        debug!(
            "{:?}: AntiEntropy: Number of public inbound neighbors: {}, public={}",
            &self.local_peer, num_public_inbound, self.connection_opts.antientropy_public
        );

        if num_public_inbound > 0 && !self.connection_opts.antientropy_public {
            // we're likely not NAT'ed, and we're not supposed to push blocks to the public.
            return Ok(());
        }

        if self.relay_handles.len() as u64
            > self.connection_opts.max_block_push + self.connection_opts.max_microblock_push
        {
            // overwhelmed
            debug!(
                "{:?}: AntiEntropy: too many relay handles ({}), skipping anti-entropy",
                &self.local_peer,
                self.relay_handles.len()
            );
            return Ok(());
        }

        if self.inv_state.is_none() {
            // nothing to do
            return Ok(());
        }

        let mut total_blocks_to_broadcast = 0;
        let mut total_microblocks_to_broadcast = 0;
        let mut lowest_reward_cycle_with_missing_block = HashMap::new();
        let neighbor_keys: Vec<NeighborKey> = self
            .inv_state
            .as_ref()
            .map(|inv_state| inv_state.block_stats.keys().map(|nk| nk.clone()).collect())
            .unwrap_or(vec![]);

        if self.antientropy_start_reward_cycle >= self.pox_id.num_inventory_reward_cycles() as u64 {
            debug!("AntiEntropy: wrap around back to reward cycle 0");
            self.antientropy_start_reward_cycle = 0;
        }

        let reward_cycle_start = self.antientropy_start_reward_cycle;
        let reward_cycle_finish = cmp::min(
            self.antientropy_start_reward_cycle + self.connection_opts.inv_reward_cycles,
            self.pox_id.num_inventory_reward_cycles() as u64,
        );

        self.antientropy_start_reward_cycle = reward_cycle_finish;

        if neighbor_keys.len() == 0 {
            return Ok(());
        }

        debug!(
            "{:?}: AntiEntropy: run protocol for {} neighbors, over reward cycles {}-{}",
            &self.local_peer,
            &neighbor_keys.len(),
            reward_cycle_start,
            reward_cycle_finish
        );

        for reward_cycle in reward_cycle_start..reward_cycle_finish {
            let local_blocks_inv = match self.get_local_blocks_inv(sortdb, chainstate, reward_cycle)
            {
                Ok(inv) => inv,
                Err(e) => {
                    debug!(
                        "{:?}: AntiEntropy: Failed to load local blocks inventory for reward cycle {}: {:?}",
                        &self.local_peer, reward_cycle, &e
                    );
                    continue;
                }
            };

            debug!(
                "{:?}: AntiEntropy: Local blocks inventory for reward cycle {} is {:?}",
                &self.local_peer, reward_cycle, &local_blocks_inv
            );

            let mut blocks_to_broadcast = HashMap::new();
            let mut microblocks_to_broadcast = HashMap::new();

            let start_block_height = self.burnchain.reward_cycle_to_block_height(reward_cycle);
            let highest_snapshot = self.burnchain_tip.clone();
            for nk in neighbor_keys.iter() {
                if total_blocks_to_broadcast >= self.connection_opts.max_block_push
                    && total_microblocks_to_broadcast >= self.connection_opts.max_microblock_push
                {
                    break;
                }
                let (blocks, microblocks) = match self.with_neighbor_blocks_inv(
                    nk,
                    |ref mut network, ref mut block_stats| {
                        let mut local_blocks = vec![];
                        let mut local_microblocks = vec![];

                        for height in start_block_height
                            ..network
                                .burnchain
                                .reward_cycle_to_block_height(reward_cycle + 1)
                        {
                            if total_blocks_to_broadcast < network.connection_opts.max_block_push
                                && local_blocks.len() < BLOCKS_PUSHED_MAX as usize
                            {
                                if let Some((consensus_hash, block)) = network
                                    .find_next_push_block(
                                        nk,
                                        reward_cycle,
                                        height,
                                        sortdb,
                                        chainstate,
                                        &local_blocks_inv,
                                        block_stats,
                                    )?
                                {
                                    let index_block_hash = StacksBlockHeader::make_index_block_hash(
                                        &consensus_hash,
                                        &block.block_hash(),
                                    );

                                    if consensus_hash == highest_snapshot.consensus_hash {
                                        // This block was just sortition'ed
                                        debug!("{:?}: AntiEntropy: do not push anchored block {} just yet -- give it a chance to propagate through other means", &network.local_peer, &index_block_hash);
                                        continue;
                                    }

                                    // have we recently tried to push this out yet?
                                    if let Some(ref mut push_set) =
                                        network.antientropy_blocks.get_mut(nk)
                                    {
                                        if let Some(ts) = push_set.get(&index_block_hash) {
                                            if *ts
                                                > get_epoch_time_secs()
                                                    + network.connection_opts.antientropy_retry
                                            {
                                                // tried pushing this block recently
                                                debug!("{:?}: AntiEntropy: already recently pushed anchored block {} (will push again after {})", &network.local_peer, &index_block_hash, get_epoch_time_secs() + network.connection_opts.antientropy_retry);
                                                continue;
                                            }
                                        } else {
                                            push_set
                                                .insert(index_block_hash, get_epoch_time_secs() + network.connection_opts.antientropy_retry);
                                        }
                                    } else {
                                        let mut pushed = HashMap::new();
                                        pushed.insert(index_block_hash, get_epoch_time_secs());
                                        network.antientropy_blocks.insert(nk.clone(), pushed);
                                    }

                                    local_blocks.push((consensus_hash, block));

                                    if !lowest_reward_cycle_with_missing_block.contains_key(nk) {
                                        lowest_reward_cycle_with_missing_block
                                            .insert(nk.clone(), reward_cycle);
                                    }

                                    total_blocks_to_broadcast += 1;
                                }
                            }

                            if total_microblocks_to_broadcast
                                < network.connection_opts.max_microblock_push
                            {
                                if let Some((parent_consensus_hash, parent_block_hash, microblocks)) = network
                                    .find_next_push_microblocks(
                                        nk,
                                        reward_cycle,
                                        height,
                                        sortdb,
                                        chainstate,
                                        &local_blocks_inv,
                                        block_stats,
                                    )?
                                {
                                    let index_block_hash = StacksBlockHeader::make_index_block_hash(
                                        &parent_consensus_hash,
                                        &parent_block_hash
                                    );

                                    if parent_consensus_hash == highest_snapshot.consensus_hash {
                                        // This parent block was just sortition'ed
                                        debug!("{:?}: AntiEntropy: do not push microblocks built on {} just yet -- give them a chance to propagate through other means", &network.local_peer, &index_block_hash);
                                        continue;
                                    }

                                    // have we recently tried to push this out yet?
                                    if let Some(ref mut push_set) =
                                        network.antientropy_microblocks.get_mut(nk)
                                    {
                                        if let Some(ts) = push_set.get(&index_block_hash) {
                                            if *ts
                                                > get_epoch_time_secs()
                                                    + network.connection_opts.antientropy_retry
                                            {
                                                // tried pushing this microblock stream recently
                                                debug!("{:?}: AntiEntropy: already recently pushed microblocks off of {} (will push again after {})", &network.local_peer, &index_block_hash, get_epoch_time_secs() + network.connection_opts.antientropy_retry);
                                                continue;
                                            }
                                        } else {
                                            push_set.insert(
                                                index_block_hash.clone(),
                                                get_epoch_time_secs() + network.connection_opts.antientropy_retry,
                                            );
                                        }
                                    } else {
                                        let mut pushed = HashMap::new();
                                        pushed.insert(index_block_hash, get_epoch_time_secs());
                                        network.antientropy_microblocks.insert(nk.clone(), pushed);
                                    }

                                    local_microblocks.push((index_block_hash, microblocks));

                                    if !lowest_reward_cycle_with_missing_block.contains_key(nk) {
                                        lowest_reward_cycle_with_missing_block
                                            .insert(nk.clone(), reward_cycle);
                                    }

                                    total_microblocks_to_broadcast += 1;
                                }
                            }
                        }
                        Ok((local_blocks, local_microblocks))
                    },
                ) {
                    Ok(x) => x,
                    Err(net_error::PeerNotConnected) => {
                        debug!("{:?}: AntiEntropy: not connected: {:?}", &self.local_peer, &nk);
                        continue;
                    }
                    Err(e) => {
                        debug!(
                            "{:?}: AntiEntropy: Failed to push blocks to {:?}: {:?}",
                            &self.local_peer, &nk, &e
                        );
                        return Err(e);
                    }
                };

                blocks_to_broadcast.insert(nk.clone(), blocks);
                microblocks_to_broadcast.insert(nk.clone(), microblocks);
            }

            debug!(
                "{:?}: AntiEntropy: push {} blocks and {} microblocks",
                &self.local_peer, total_blocks_to_broadcast, total_microblocks_to_broadcast
            );

            for (nk, blocks) in blocks_to_broadcast.into_iter() {
                let num_blocks = blocks.len();
                if num_blocks == 0 {
                    continue;
                }

                for block in blocks.iter() {
                    let ibh =
                        StacksBlockHeader::make_index_block_hash(&block.0, &block.1.block_hash());
                    debug!(
                        "{:?}: AntiEntropy: push anchored block {} to {}",
                        &self.local_peer, &ibh, &nk
                    );
                }

                let blocks_data = BlocksData { blocks: blocks };

                self.broadcast_message(
                    vec![nk.clone()],
                    vec![],
                    StacksMessageType::Blocks(blocks_data),
                );
            }

            for (nk, microblock_datas) in microblocks_to_broadcast.into_iter() {
                for (anchor_block_id, microblocks) in microblock_datas.into_iter() {
                    let num_microblocks = microblocks.len();
                    if num_microblocks == 0 {
                        continue;
                    }
                    let microblocks_data = MicroblocksData {
                        index_anchor_block: anchor_block_id.clone(),
                        microblocks: microblocks,
                    };

                    debug!(
                        "{:?}: AntiEntropy: push microblock stream (len={}) on {} to {}",
                        &self.local_peer,
                        microblocks_data.microblocks.len(),
                        &microblocks_data.index_anchor_block,
                        &nk
                    );

                    self.broadcast_message(
                        vec![nk.clone()],
                        vec![],
                        StacksMessageType::Microblocks(microblocks_data),
                    );
                }
            }
        }

        // invalidate inventories at and after the affected reward cycles, so we're forced to go
        // and re-download them (once our block has been received).  This prevents this code from
        // DDoS'ing remote nodes to death with blocks over and over again, and it prevents this
        // code from doing needless extra work for remote nodes that always report 0 for their
        // inventory statuses.
        for (nk, reward_cycle) in lowest_reward_cycle_with_missing_block.into_iter() {
            debug!(
                "{:?}: AntiEntropy: Invalidate inventory for {:?} at and after reward cycle {}",
                &self.local_peer, &nk, reward_cycle
            );
            PeerNetwork::with_inv_state(self, |network, inv_state| {
                if let Some(block_stats) = inv_state.block_stats.get_mut(&nk) {
                    block_stats
                        .inv
                        .truncate_pox_inventory(&network.burnchain, reward_cycle);
                }
                Ok(())
            })?;
        }
        Ok(())
    }

    /// Do the actual work in the state machine.
    /// Return true if we need to prune connections.
    fn do_network_work(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        dns_client_opt: &mut Option<&mut DNSClient>,
        download_backpressure: bool,
        ibd: bool,
        network_result: &mut NetworkResult,
    ) -> Result<bool, net_error> {
        // do some Actual Work(tm)
        let mut do_prune = false;
        let mut did_cycle = false;

        while !did_cycle {
            debug!(
                "{:?}: network work state is {:?}",
                &self.local_peer, &self.work_state
            );
            let cur_state = self.work_state;
            match self.work_state {
                PeerNetworkWorkState::GetPublicIP => {
                    if cfg!(test) && self.connection_opts.disable_natpunch {
                        self.work_state = PeerNetworkWorkState::BlockInvSync;
                    } else {
                        // (re)determine our public IP address
                        match self.do_get_public_ip() {
                            Ok(b) => {
                                if b {
                                    self.work_state = PeerNetworkWorkState::BlockInvSync;
                                }
                            }
                            Err(e) => {
                                info!("Failed to query public IP ({:?}) skipping", &e);
                                self.work_state = PeerNetworkWorkState::BlockInvSync;
                            }
                        }
                    }
                }
                PeerNetworkWorkState::BlockInvSync => {
                    // synchronize peer block inventories
                    let (inv_done, inv_throttled) = self.do_network_inv_sync(sortdb, ibd)?;
                    if inv_done {
                        if !download_backpressure {
                            // proceed to get blocks, if we're not backpressured
                            self.work_state = PeerNetworkWorkState::BlockDownload;
                        } else {
                            // skip downloads for now
                            self.work_state = PeerNetworkWorkState::Prune;
                        }

                        if !inv_throttled {
                            // only count an inv_sync as passing if there's an always-allowed node
                            // in our inv state
                            let always_allowed: HashSet<_> = PeerDB::get_always_allowed_peers(
                                &self.peerdb.conn(),
                                self.local_peer.network_id,
                            )
                            .unwrap_or(vec![])
                            .into_iter()
                            .map(|neighbor| neighbor.addr)
                            .collect();

                            let mut have_always_allowed = false;

                            if always_allowed.len() == 0 {
                                have_always_allowed = true;
                            } else {
                                if let Some(ref inv_state) = self.inv_state {
                                    for (nk, stats) in inv_state.block_stats.iter() {
                                        if !always_allowed.contains(&nk) {
                                            continue;
                                        }

                                        if stats.inv.num_reward_cycles
                                            >= self.pox_id.num_inventory_reward_cycles() as u64
                                        {
                                            debug!(
                                                "{:?}: Fully-sync'ed PoX inventory from {}",
                                                &self.local_peer, nk
                                            );
                                            have_always_allowed = true;
                                        }
                                    }
                                }
                            }

                            if have_always_allowed {
                                debug!("{:?}: synchronized inventories with at least one always-allowed peer", &self.local_peer);
                                self.num_inv_sync_passes += 1;
                            } else {
                                debug!("{:?}: did NOT synchronize inventories with at least one always-allowed peer", &self.local_peer);
                            }
                            debug!(
                                "{:?}: Finished full inventory state-machine pass ({})",
                                &self.local_peer, self.num_inv_sync_passes
                            );

                            // hint to the downloader to start scanning at the sortition
                            // height we just synchronized
                            let start_download_sortition = if let Some(ref inv_state) =
                                self.inv_state
                            {
                                let (consensus_hash, _) =
                                    SortitionDB::get_canonical_stacks_chain_tip_hash(
                                        sortdb.conn(),
                                    )?;

                                let stacks_tip_sortition_height =
                                    SortitionDB::get_block_snapshot_consensus(
                                        sortdb.conn(),
                                        &consensus_hash,
                                    )?
                                    .map(|sn| sn.block_height)
                                    .unwrap_or(self.burnchain.first_block_height)
                                    .saturating_sub(self.burnchain.first_block_height);

                                let sortition_height_start = cmp::min(
                                    stacks_tip_sortition_height,
                                    inv_state.block_sortition_start,
                                );

                                debug!(
                                        "{:?}: Begin downloader synchronization at sortition height {} min({},{})",
                                        &self.local_peer,
                                        sortition_height_start,
                                        inv_state.block_sortition_start,
                                        stacks_tip_sortition_height
                                    );

                                sortition_height_start
                            } else {
                                // really unreachable, but why tempt fate?
                                warn!(
                                    "{:?}: Inventory state machine not yet initialized",
                                    &self.local_peer
                                );
                                0
                            };

                            if let Some(ref mut downloader) = self.block_downloader {
                                debug!(
                                    "{:?}: wake up downloader at sortition height {}",
                                    &self.local_peer, start_download_sortition
                                );
                                downloader.hint_block_sortition_height_available(
                                    start_download_sortition,
                                    ibd,
                                );
                                downloader.hint_microblock_sortition_height_available(
                                    start_download_sortition,
                                    ibd,
                                );
                            } else {
                                warn!(
                                    "{:?}: Block downloader not yet initialized",
                                    &self.local_peer
                                );
                            }
                        }
                    }
                }
                PeerNetworkWorkState::BlockDownload => {
                    // go fetch blocks
                    match dns_client_opt {
                        Some(ref mut dns_client) => {
                            if self.do_network_block_download(
                                sortdb,
                                chainstate,
                                *dns_client,
                                ibd,
                                network_result,
                            )? {
                                // advance work state
                                self.work_state = PeerNetworkWorkState::AntiEntropy;
                            }
                        }
                        None => {
                            // skip this step -- no DNS client available
                            test_debug!(
                                "{:?}: no DNS client provided; skipping block download",
                                &self.local_peer
                            );
                            self.work_state = PeerNetworkWorkState::AntiEntropy;
                        }
                    }
                }
                PeerNetworkWorkState::AntiEntropy => {
                    if ibd {
                        debug!(
                            "{:?}: Skip AntiEntropy while in initial block download",
                            &self.local_peer
                        );
                    } else {
                        match self.try_push_local_data(sortdb, chainstate) {
                            Ok(_) => {}
                            Err(e) => {
                                debug!(
                                    "{:?}: Failed to push local data: {:?}",
                                    &self.local_peer, &e
                                );
                            }
                        };
                    }
                    self.work_state = PeerNetworkWorkState::Prune;
                }
                PeerNetworkWorkState::Prune => {
                    // did one pass
                    did_cycle = true;
                    do_prune = true;

                    // restart
                    self.work_state = PeerNetworkWorkState::GetPublicIP;
                }
            }

            if self.work_state == cur_state {
                // only break early if we can't make progress
                break;
            }
        }

        if did_cycle {
            self.num_state_machine_passes += 1;
            debug!(
                "{:?}: Finished full p2p state-machine pass ({})",
                &self.local_peer, self.num_state_machine_passes
            );
        }

        Ok(do_prune)
    }

    fn do_attachment_downloads(
        &mut self,
        chainstate: &mut StacksChainState,
        mut dns_client_opt: Option<&mut DNSClient>,
        network_result: &mut NetworkResult,
    ) -> Result<(), net_error> {
        if self.attachments_downloader.is_none() {
            self.atlasdb.evict_expired_uninstantiated_attachments()?;
            self.atlasdb
                .evict_expired_unresolved_attachment_instances()?;
            let initial_batch = self.atlasdb.find_unresolved_attachment_instances()?;

            self.init_attachments_downloader(initial_batch);
        }

        match dns_client_opt {
            Some(ref mut dns_client) => {
                let mut dead_events = PeerNetwork::with_attachments_downloader(
                    self,
                    |network, attachments_downloader| {
                        let mut dead_events = vec![];
                        match attachments_downloader.run(dns_client, chainstate, network) {
                            Ok((ref mut attachments, ref mut events_to_deregister)) => {
                                network_result.attachments.append(attachments);
                                dead_events.append(events_to_deregister);
                            }
                            Err(e) => {
                                warn!(
                                    "Atlas: AttachmentsDownloader failed running with error {:?}",
                                    e
                                );
                            }
                        }
                        Ok(dead_events)
                    },
                )?;

                let _ = PeerNetwork::with_network_state(
                    self,
                    |ref mut network, ref mut network_state| {
                        for event_id in dead_events.drain(..) {
                            debug!(
                                "Atlas: Deregistering faulty connection (event_id: {})",
                                event_id
                            );
                            PeerNetwork::with_http(network, |_, http| {
                                http.deregister_http(network_state, event_id);
                            });
                        }
                        Ok(())
                    },
                );
            }
            None => {
                // skip this step -- no DNS client available
                test_debug!(
                    "{:?}: no DNS client provided; skipping block download",
                    &self.local_peer
                );
            }
        }
        Ok(())
    }

    /// Given an event ID, find the other event ID corresponding
    /// to the same remote peer.  There will be at most two such events
    /// -- one registered as the inbound connection, and one registered as the
    /// outbound connection.
    fn find_reciprocal_event(&self, event_id: usize) -> Option<usize> {
        let pubkey = match self.peers.get(&event_id) {
            Some(convo) => match convo.get_public_key() {
                Some(pubk) => pubk,
                None => {
                    return None;
                }
            },
            None => {
                return None;
            }
        };

        for (ev_id, convo) in self.peers.iter() {
            if *ev_id == event_id {
                continue;
            }
            if let Some(pubk) = convo.ref_public_key() {
                if *pubk == pubkey {
                    return Some(*ev_id);
                }
            }
        }
        None
    }

    /// Given an event ID, find the NeighborKey that corresponds to the outbound connection we have
    /// to the peer the event ID references.  This checks both the conversation referenced by the
    /// event ID, as well as the reciprocal conversation of the event ID.
    pub fn find_outbound_neighbor(&self, event_id: usize) -> Option<NeighborKey> {
        let (is_authenticated, is_outbound, neighbor_key) = match self.peers.get(&event_id) {
            Some(convo) => (
                convo.is_authenticated(),
                convo.is_outbound(),
                convo.to_neighbor_key(),
            ),
            None => {
                test_debug!("No such neighbor event={}", event_id);
                return None;
            }
        };

        let outbound_neighbor_key = if !is_outbound {
            let reciprocal_event_id = match self.find_reciprocal_event(event_id) {
                Some(re) => re,
                None => {
                    test_debug!(
                        "{:?}: no reciprocal conversation for {:?}",
                        &self.local_peer,
                        &neighbor_key
                    );
                    return None;
                }
            };

            let (reciprocal_is_authenticated, reciprocal_is_outbound, reciprocal_neighbor_key) =
                match self.peers.get(&reciprocal_event_id) {
                    Some(convo) => (
                        convo.is_authenticated(),
                        convo.is_outbound(),
                        convo.to_neighbor_key(),
                    ),
                    None => {
                        test_debug!(
                            "{:?}: No reciprocal conversation for {} (event={})",
                            &self.local_peer,
                            &neighbor_key,
                            event_id
                        );
                        return None;
                    }
                };

            if !is_authenticated && !reciprocal_is_authenticated {
                test_debug!(
                    "{:?}: {:?} and {:?} are not authenticated",
                    &self.local_peer,
                    &neighbor_key,
                    &reciprocal_neighbor_key
                );
                return None;
            }

            if !is_outbound && !reciprocal_is_outbound {
                test_debug!(
                    "{:?}: {:?} and {:?} are not outbound",
                    &self.local_peer,
                    &neighbor_key,
                    &reciprocal_neighbor_key
                );
                return None;
            }

            reciprocal_neighbor_key
        } else {
            neighbor_key
        };

        Some(outbound_neighbor_key)
    }

    /// Update a peer's inventory state to indicate that the given block is available.
    /// If updated, return the sortition height of the bit in the inv that was set.
    fn handle_unsolicited_inv_update(
        &mut self,
        sortdb: &SortitionDB,
        event_id: usize,
        outbound_neighbor_key: &NeighborKey,
        consensus_hash: &ConsensusHash,
        microblocks: bool,
    ) -> Result<Option<u64>, net_error> {
        let block_sortition_height = match self.inv_state {
            Some(ref mut inv) => {
                let res = if microblocks {
                    inv.set_microblocks_available(
                        &self.burnchain,
                        outbound_neighbor_key,
                        sortdb,
                        consensus_hash,
                    )
                } else {
                    inv.set_block_available(
                        &self.burnchain,
                        outbound_neighbor_key,
                        sortdb,
                        consensus_hash,
                    )
                };

                match res {
                    Ok(Some(block_height)) => block_height,
                    Ok(None) => {
                        debug!(
                            "{:?}: We already know the inventory state in {} for {}",
                            &self.local_peer, outbound_neighbor_key, consensus_hash
                        );
                        return Ok(None);
                    }
                    Err(net_error::NotFoundError) => {
                        // is this remote node simply ahead of us?
                        if let Some(convo) = self.peers.get(&event_id) {
                            if self.chain_view.burn_block_height < convo.burnchain_tip_height {
                                debug!("{:?}: Unrecognized consensus hash {}; it is possible that {} is ahead of us", &self.local_peer, consensus_hash, outbound_neighbor_key);
                                return Err(net_error::NotFoundError);
                            }
                        }
                        // not ahead of us -- it's a bad consensus hash
                        debug!("{:?}: Unrecognized consensus hash {}; assuming that {} has a different chain view", &self.local_peer, consensus_hash, outbound_neighbor_key);
                        return Ok(None);
                    }
                    Err(net_error::InvalidMessage) => {
                        // punish this peer
                        info!(
                            "Peer {:?} sent an invalid update for {}",
                            &outbound_neighbor_key,
                            if microblocks {
                                "streamed microblocks"
                            } else {
                                "blocks"
                            }
                        );
                        self.bans.insert(event_id);

                        if let Some(outbound_event_id) = self.events.get(&outbound_neighbor_key) {
                            self.bans.insert(*outbound_event_id);
                        }
                        return Ok(None);
                    }
                    Err(e) => {
                        warn!(
                            "Failed to update inv state for {:?}: {:?}",
                            &outbound_neighbor_key, &e
                        );
                        return Ok(None);
                    }
                }
            }
            None => {
                return Ok(None);
            }
        };
        Ok(Some(block_sortition_height))
    }

    /// Buffer a message for re-processing once the burnchain view updates
    fn buffer_data_message(&mut self, event_id: usize, msg: StacksMessage) -> () {
        if let Some(msgs) = self.pending_messages.get_mut(&event_id) {
            // check limits:
            // at most 1 BlocksAvailable
            // at most 1 MicroblocksAvailable
            // at most 1 BlocksData
            // at most $self.connection_opts.max_buffered_microblocks MicroblocksDatas
            let mut blocks_available = 0;
            let mut microblocks_available = 0;
            let mut blocks_data = 0;
            let mut microblocks_data = 0;
            for msg in msgs.iter() {
                match &msg.payload {
                    StacksMessageType::BlocksAvailable(_) => {
                        blocks_available += 1;
                    }
                    StacksMessageType::MicroblocksAvailable(_) => {
                        microblocks_available += 1;
                    }
                    StacksMessageType::Blocks(_) => {
                        blocks_data += 1;
                    }
                    StacksMessageType::Microblocks(_) => {
                        microblocks_data += 1;
                    }
                    _ => {}
                }
            }

            if let StacksMessageType::BlocksAvailable(_) = &msg.payload {
                if blocks_available >= self.connection_opts.max_buffered_blocks_available {
                    debug!(
                        "{:?}: Drop BlocksAvailable from event {} -- already have {} buffered",
                        &self.local_peer, event_id, blocks_available
                    );
                    return;
                }
            }
            if let StacksMessageType::MicroblocksAvailable(_) = &msg.payload {
                if microblocks_available >= self.connection_opts.max_buffered_microblocks_available
                {
                    debug!(
                        "{:?}: Drop MicroblocksAvailable from event {} -- already have {} buffered",
                        &self.local_peer, event_id, microblocks_available
                    );
                    return;
                }
            }
            if let StacksMessageType::Blocks(_) = &msg.payload {
                if blocks_data >= self.connection_opts.max_buffered_blocks {
                    debug!(
                        "{:?}: Drop BlocksData from event {} -- already have {} buffered",
                        &self.local_peer, event_id, blocks_data
                    );
                    return;
                }
            }
            if let StacksMessageType::Microblocks(_) = &msg.payload {
                if microblocks_data >= self.connection_opts.max_buffered_microblocks {
                    debug!(
                        "{:?}: Drop MicroblocksData from event {} -- already have {} buffered",
                        &self.local_peer, event_id, microblocks_data
                    );
                    return;
                }
            }
            msgs.push(msg);
            debug!(
                "{:?}: Event {} has {} messages buffered",
                &self.local_peer,
                event_id,
                msgs.len()
            );
        } else {
            self.pending_messages.insert(event_id, vec![msg]);
            debug!(
                "{:?}: Event {} has 1 messages buffered",
                &self.local_peer, event_id
            );
        }
    }

    /// Handle unsolicited BlocksAvailable.
    /// Update our inv for this peer.
    /// Mask errors.
    /// Return whether or not we need to buffer this message
    fn handle_unsolicited_BlocksAvailable(
        &mut self,
        sortdb: &SortitionDB,
        event_id: usize,
        new_blocks: &BlocksAvailableData,
        buffer: bool,
    ) -> bool {
        let outbound_neighbor_key = match self.find_outbound_neighbor(event_id) {
            Some(onk) => onk,
            None => {
                return false;
            }
        };

        debug!(
            "{:?}: Process BlocksAvailable from {:?} with {} entries",
            &self.local_peer,
            outbound_neighbor_key,
            new_blocks.available.len()
        );

        let mut to_buffer = false;
        for (consensus_hash, block_hash) in new_blocks.available.iter() {
            let block_sortition_height = match self.handle_unsolicited_inv_update(
                sortdb,
                event_id,
                &outbound_neighbor_key,
                consensus_hash,
                false,
            ) {
                Ok(Some(bsh)) => bsh,
                Ok(None) => {
                    continue;
                }
                Err(net_error::NotFoundError) => {
                    if buffer {
                        debug!("{:?}: Will buffer BlocksAvailable for {} until the next burnchain view update", &self.local_peer, &consensus_hash);
                        to_buffer = true;
                    }
                    continue;
                }
                Err(e) => {
                    info!(
                        "{:?}: Failed to handle BlocksAvailable({}/{}) from {}: {:?}",
                        &self.local_peer, &consensus_hash, &block_hash, &outbound_neighbor_key, &e
                    );
                    continue;
                }
            };

            // have the downloader request this block if it's new
            match self.block_downloader {
                Some(ref mut downloader) => {
                    downloader.hint_block_sortition_height_available(block_sortition_height, false);
                }
                None => {}
            }
        }

        to_buffer
    }

    /// Handle unsolicited MicroblocksAvailable.
    /// Update our inv for this peer.
    /// Mask errors.
    /// Return whether or not we need to buffer this message
    fn handle_unsolicited_MicroblocksAvailable(
        &mut self,
        sortdb: &SortitionDB,
        event_id: usize,
        new_mblocks: &BlocksAvailableData,
        buffer: bool,
    ) -> bool {
        let outbound_neighbor_key = match self.find_outbound_neighbor(event_id) {
            Some(onk) => onk,
            None => {
                return false;
            }
        };

        debug!(
            "{:?}: Process MicroblocksAvailable from {:?} with {} entries",
            &self.local_peer,
            outbound_neighbor_key,
            new_mblocks.available.len()
        );

        let mut to_buffer = false;

        for (consensus_hash, block_hash) in new_mblocks.available.iter() {
            let mblock_sortition_height = match self.handle_unsolicited_inv_update(
                sortdb,
                event_id,
                &outbound_neighbor_key,
                consensus_hash,
                true,
            ) {
                Ok(Some(bsh)) => bsh,
                Ok(None) => {
                    continue;
                }
                Err(net_error::NotFoundError) => {
                    if buffer {
                        debug!("{:?}: Will buffer MicroblocksAvailable for {} until the next burnchain view update", &self.local_peer, &consensus_hash);
                        to_buffer = true;
                    }
                    continue;
                }
                Err(e) => {
                    info!(
                        "{:?}: Failed to handle MicroblocksAvailable({}/{}) from {}: {:?}",
                        &self.local_peer, &consensus_hash, &block_hash, &outbound_neighbor_key, &e
                    );
                    continue;
                }
            };

            // have the downloader request this block if it's new
            match self.block_downloader {
                Some(ref mut downloader) => {
                    downloader
                        .hint_microblock_sortition_height_available(mblock_sortition_height, false);
                }
                None => {}
            }
        }
        to_buffer
    }

    /// Handle unsolicited BlocksData.
    /// Don't (yet) validate the data, but do update our inv for the peer that sent it, if we have
    /// an outbound connection to that peer.  Accept the blocks data either way if it corresponds
    /// to a winning sortition -- this will cause the blocks data to be fed into the relayer, which
    /// will then decide whether or not it needs to be stored and/or forwarded.
    /// Mask errors.
    fn handle_unsolicited_BlocksData(
        &mut self,
        sortdb: &SortitionDB,
        event_id: usize,
        new_blocks: &BlocksData,
        buffer: bool,
    ) -> bool {
        let (remote_neighbor_key, remote_is_authenticated) = match self.peers.get(&event_id) {
            Some(convo) => (convo.to_neighbor_key(), convo.is_authenticated()),
            None => {
                test_debug!(
                    "{:?}: No such neighbor event={}",
                    &self.local_peer,
                    event_id
                );
                return false;
            }
        };

        if !remote_is_authenticated {
            // drop -- a correct peer will have authenticated before sending this message
            test_debug!(
                "{:?}: Drop unauthenticated BlocksData from {:?}",
                &self.local_peer,
                &remote_neighbor_key
            );
            return false;
        }

        let outbound_neighbor_key_opt = self.find_outbound_neighbor(event_id);

        debug!(
            "{:?}: Process BlocksData from {:?} with {} entries",
            &self.local_peer,
            outbound_neighbor_key_opt
                .as_ref()
                .unwrap_or(&remote_neighbor_key),
            new_blocks.blocks.len()
        );

        let mut to_buffer = false;

        for (consensus_hash, block) in new_blocks.blocks.iter() {
            let sn = match SortitionDB::get_block_snapshot_consensus(
                &sortdb.conn(),
                &consensus_hash,
            ) {
                Ok(Some(sn)) => sn,
                Ok(None) => {
                    if buffer {
                        debug!(
                                "{:?}: Will buffer unsolicited BlocksData({}/{}) ({}) -- consensus hash not (yet) recognized",
                                &self.local_peer,
                                &consensus_hash,
                                &block.block_hash(),
                                StacksBlockHeader::make_index_block_hash(
                                    &consensus_hash,
                                    &block.block_hash()
                                )
                            );
                        to_buffer = true;
                    } else {
                        debug!(
                                "{:?}: Will drop unsolicited BlocksData({}/{}) ({}) -- consensus hash not (yet) recognized",
                                &self.local_peer,
                                &consensus_hash,
                                &block.block_hash(),
                                StacksBlockHeader::make_index_block_hash(
                                    &consensus_hash,
                                    &block.block_hash()
                                )
                            );
                    }
                    continue;
                }
                Err(e) => {
                    info!(
                        "{:?}: Failed to query block snapshot for {}: {:?}",
                        &self.local_peer, consensus_hash, &e
                    );
                    continue;
                }
            };

            if !sn.pox_valid {
                info!(
                    "{:?}: Failed to query snapshot for {}: not on the valid PoX fork",
                    &self.local_peer, consensus_hash
                );
                continue;
            }

            if sn.winning_stacks_block_hash != block.block_hash() {
                info!(
                    "{:?}: Ignoring block {} -- winning block was {} (sortition: {})",
                    &self.local_peer,
                    block.block_hash(),
                    sn.winning_stacks_block_hash,
                    sn.sortition
                );
                continue;
            }

            // only bother updating the inventory for this event's peer if we have an outbound
            // connection to it.
            if let Some(outbound_neighbor_key) = outbound_neighbor_key_opt.as_ref() {
                let _ = self.handle_unsolicited_inv_update(
                    sortdb,
                    event_id,
                    &outbound_neighbor_key,
                    &sn.consensus_hash,
                    false,
                );
            }
        }

        to_buffer
    }

    /// Handle unsolicited MicroblocksData.
    /// Returns whether or not to buffer (if buffer is true)
    /// Returns whether or not to pass to the relayer (if buffer is false).
    fn handle_unsolicited_MicroblocksData(
        &mut self,
        chainstate: &StacksChainState,
        event_id: usize,
        new_microblocks: &MicroblocksData,
        buffer: bool,
    ) -> bool {
        let (remote_neighbor_key, remote_is_authenticated) = match self.peers.get(&event_id) {
            Some(convo) => (convo.to_neighbor_key(), convo.is_authenticated()),
            None => {
                test_debug!(
                    "{:?}: No such neighbor event={}",
                    &self.local_peer,
                    event_id
                );
                return false;
            }
        };

        if !remote_is_authenticated {
            // drop -- a correct peer will have authenticated before sending this message
            test_debug!(
                "{:?}: Drop unauthenticated MicroblocksData from {:?}",
                &self.local_peer,
                &remote_neighbor_key
            );
            return false;
        }

        let outbound_neighbor_key_opt = self.find_outbound_neighbor(event_id);

        debug!(
            "{:?}: Process MicroblocksData from {:?} for {} with {} entries",
            &self.local_peer,
            outbound_neighbor_key_opt
                .as_ref()
                .unwrap_or(&remote_neighbor_key),
            &new_microblocks.index_anchor_block,
            new_microblocks.microblocks.len()
        );

        // do we have the associated anchored block?
        match chainstate.get_block_header_hashes(&new_microblocks.index_anchor_block) {
            Ok(Some(_)) => {
                // yup; can process now
                debug!("{:?}: have microblock parent anchored block {}, so can process its microblocks", &self.local_peer, &new_microblocks.index_anchor_block);
                !buffer
            }
            Ok(None) => {
                if buffer {
                    debug!(
                        "{:?}: Will buffer unsolicited MicroblocksData({})",
                        &self.local_peer, &new_microblocks.index_anchor_block
                    );
                    true
                } else {
                    debug!(
                        "{:?}: Will not buffer unsolicited MicroblocksData({})",
                        &self.local_peer, &new_microblocks.index_anchor_block
                    );
                    false
                }
            }
            Err(e) => {
                warn!(
                    "{:?}: Failed to get header hashes for {:?}: {:?}",
                    &self.local_peer, &new_microblocks.index_anchor_block, &e
                );
                false
            }
        }
    }

    /// Returns (true, x) if we should buffer the message and try again
    /// Returns (x, true) if the relayer should receive the message
    fn handle_unsolicited_message(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
        event_id: usize,
        payload: &StacksMessageType,
        buffer: bool,
    ) -> (bool, bool) {
        match payload {
            // Update our inv state for this peer, but only do so if we have an
            // outbound connection to it and it's authenticated (we don't synchronize inv
            // state with inbound peers).  Since we will have received this message
            // from an _inbound_ conversation, we need to find the reciprocal _outbound_
            // conversation and use _that_ conversation's neighbor key to identify
            // which inventory we need to update.
            StacksMessageType::BlocksAvailable(ref new_blocks) => {
                let to_buffer =
                    self.handle_unsolicited_BlocksAvailable(sortdb, event_id, new_blocks, buffer);
                (to_buffer, false)
            }
            StacksMessageType::MicroblocksAvailable(ref new_mblocks) => {
                let to_buffer = self.handle_unsolicited_MicroblocksAvailable(
                    sortdb,
                    event_id,
                    new_mblocks,
                    buffer,
                );
                (to_buffer, false)
            }
            StacksMessageType::Blocks(ref new_blocks) => {
                // update inv state for this peer
                let to_buffer =
                    self.handle_unsolicited_BlocksData(sortdb, event_id, new_blocks, buffer);

                // forward to relayer for processing
                (to_buffer, true)
            }
            StacksMessageType::Microblocks(ref new_mblocks) => {
                let to_buffer = self.handle_unsolicited_MicroblocksData(
                    chainstate,
                    event_id,
                    new_mblocks,
                    buffer,
                );

                // only forward to the relayer if we don't need to buffer it.
                (to_buffer, true)
            }
            _ => (false, true),
        }
    }

    /// Handle unsolicited messages propagated up to us from our ongoing ConversationP2Ps.
    /// Return messages that we couldn't handle here, but key them by neighbor, not event.
    /// Drop invalid messages.
    /// If buffer is true, then re-try handling this message once the burnchain view advances.
    fn handle_unsolicited_messages(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
        unsolicited: HashMap<usize, Vec<StacksMessage>>,
        buffer: bool,
    ) -> Result<HashMap<NeighborKey, Vec<StacksMessage>>, net_error> {
        let mut unhandled: HashMap<NeighborKey, Vec<StacksMessage>> = HashMap::new();
        for (event_id, messages) in unsolicited.into_iter() {
            let neighbor_key = match self.peers.get(&event_id) {
                Some(convo) => convo.to_neighbor_key(),
                None => {
                    debug!(
                        "{:?}: No longer such neighbor event={}, dropping {} unsolicited messages",
                        &self.local_peer,
                        event_id,
                        messages.len()
                    );
                    continue;
                }
            };

            if messages.len() == 0 {
                continue;
            }

            debug!("{:?}: Process {} unsolicited messages from {:?}", &self.local_peer, messages.len(), &neighbor_key; "buffer" => %buffer);

            for message in messages.into_iter() {
                if !buffer {
                    debug!(
                        "{:?}: Re-try handling buffered message {} from {:?}",
                        &self.local_peer,
                        &message.payload.get_message_description(),
                        &neighbor_key
                    );
                }
                let (to_buffer, relay) = self.handle_unsolicited_message(
                    sortdb,
                    chainstate,
                    event_id,
                    &message.payload,
                    buffer,
                );
                if buffer && to_buffer {
                    self.buffer_data_message(event_id, message);
                } else if relay {
                    // forward to relayer for processing
                    debug!(
                        "{:?}: Will forward message {} from {:?} to relayer",
                        &self.local_peer,
                        &message.payload.get_message_description(),
                        &neighbor_key
                    );
                    if let Some(msgs) = unhandled.get_mut(&neighbor_key) {
                        msgs.push(message);
                    } else {
                        unhandled.insert(neighbor_key.clone(), vec![message]);
                    }
                }
            }
        }
        Ok(unhandled)
    }

    /// Find unauthenticated inbound conversations
    fn find_unauthenticated_inbound_convos(&self) -> Vec<usize> {
        let mut ret = vec![];
        for (event_id, convo) in self.peers.iter() {
            if !convo.is_outbound() && !convo.is_authenticated() {
                ret.push(*event_id);
            }
        }
        ret
    }

    /// Find inbound conversations that have authenticated, given a list of event ids to search
    /// for.  Add them to our network pingbacks
    fn schedule_network_pingbacks(&mut self, event_ids: Vec<usize>) -> Result<(), net_error> {
        if cfg!(test) && self.connection_opts.disable_pingbacks {
            test_debug!("{:?}: pingbacks are disabled for testing", &self.local_peer);
            return Ok(());
        }

        // clear timed-out pingbacks
        let mut to_remove = vec![];
        for (naddr, pingback) in self.walk_pingbacks.iter() {
            if pingback.ts + self.connection_opts.pingback_timeout < get_epoch_time_secs() {
                to_remove.push((*naddr).clone());
            }
        }

        for naddr in to_remove.into_iter() {
            self.walk_pingbacks.remove(&naddr);
        }

        let my_pubkey_hash = Hash160::from_node_public_key(&Secp256k1PublicKey::from_private(
            &self.local_peer.private_key,
        ));

        // add new pingbacks
        for event_id in event_ids.into_iter() {
            if let Some(ref convo) = self.peers.get(&event_id) {
                if !convo.is_outbound() && convo.is_authenticated() {
                    let nk = convo.to_handshake_neighbor_key();
                    let addr = convo.to_handshake_neighbor_address();
                    let pubkey = convo
                        .get_public_key()
                        .expect("BUG: convo is authenticated but we have no public key for it");

                    if addr.public_key_hash == my_pubkey_hash {
                        // don't talk to ourselves
                        continue;
                    }

                    let neighbor_opt = PeerDB::get_peer(
                        self.peerdb.conn(),
                        self.local_peer.network_id,
                        &addr.addrbytes,
                        addr.port,
                    )
                    .map_err(net_error::DBError)?;

                    if neighbor_opt.is_some() {
                        debug!(
                            "{:?}: will not ping back {:?}: already known to us",
                            &self.local_peer, &nk
                        );
                        continue;
                    }

                    debug!(
                        "{:?}: will ping back {:?} ({:?}) to see if it's routable from us",
                        &self.local_peer, &nk, convo
                    );
                    self.walk_pingbacks.insert(
                        addr,
                        NeighborPingback {
                            peer_version: nk.peer_version,
                            network_id: nk.network_id,
                            ts: get_epoch_time_secs(),
                            pubkey: pubkey,
                        },
                    );

                    if self.walk_pingbacks.len() > MAX_NEIGHBORS_DATA_LEN as usize {
                        // drop one at random
                        let idx = thread_rng().gen::<usize>() % self.walk_pingbacks.len();
                        let drop_addr = match self.walk_pingbacks.keys().skip(idx).next() {
                            Some(ref addr) => (*addr).clone(),
                            None => {
                                continue;
                            }
                        };

                        debug!("{:?}: drop pingback {:?}", &self.local_peer, drop_addr);
                        self.walk_pingbacks.remove(&drop_addr);
                    }
                }
            }
        }

        test_debug!(
            "{:?}: have {} pingbacks scheduled",
            &self.local_peer,
            self.walk_pingbacks.len()
        );
        Ok(())
    }

    /// Count up the number of inbound neighbors that have public IP addresses (i.e. that we have
    /// outbound connections to) and report it.
    /// If we're NAT'ed, then this value will be 0.
    pub fn count_public_inbound(&self) -> usize {
        let mut num_public_inbound = 0;
        for (event_id, convo) in self.peers.iter() {
            if convo.is_outbound() {
                continue;
            }

            // convo is inbound
            // does it have a reciprocal outbound event?
            if self.find_reciprocal_event(*event_id).is_some() {
                num_public_inbound += 1;
            }
        }
        num_public_inbound
    }

    /// Do we need to call .run() again, shortly, to advance the downloader state?
    pub fn has_more_downloads(&self) -> bool {
        if self.work_state == PeerNetworkWorkState::BlockDownload {
            if let Some(ref dl) = self.block_downloader {
                (!dl.is_download_idle() || dl.is_initial_download())
                    && dl.num_requests_inflight() == 0
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Get the local peer from the peer DB, but also preserve the public IP address
    pub fn load_local_peer(&self) -> Result<LocalPeer, net_error> {
        let mut lp = PeerDB::get_local_peer(&self.peerdb.conn())?;
        lp.public_ip_address = self.local_peer.public_ip_address.clone();
        Ok(lp)
    }

    /// Refresh view of local peer
    pub fn refresh_local_peer(&mut self) -> Result<(), net_error> {
        // update local-peer state
        self.local_peer = self.load_local_peer()?;
        Ok(())
    }

    /// Refresh view of burnchain, if needed
    pub fn refresh_burnchain_view(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
    ) -> Result<HashMap<NeighborKey, Vec<StacksMessage>>, net_error> {
        // update burnchain snapshot if we need to (careful -- it's expensive)
        let sn = SortitionDB::get_canonical_burn_chain_tip(&sortdb.conn())?;
        let mut ret: HashMap<NeighborKey, Vec<StacksMessage>> = HashMap::new();
        if sn.block_height != self.chain_view.burn_block_height {
            debug!(
                "{:?}: load chain view for burn block {}",
                &self.local_peer, sn.block_height
            );
            let new_chain_view =
                SortitionDB::get_burnchain_view(&sortdb.conn(), &self.burnchain, &sn)?;

            let new_chain_view_stable_consensus_hash = {
                let ic = sortdb.index_conn();
                let ancestor_sn = SortitionDB::get_ancestor_snapshot(
                    &ic,
                    new_chain_view.burn_stable_block_height,
                    &sn.sortition_id,
                )?
                .unwrap_or(SortitionDB::get_first_block_snapshot(sortdb.conn())?);
                ancestor_sn.consensus_hash
            };

            // wake up the inv-sync and downloader -- we have potentially more sortitions
            self.hint_sync_invs(self.chain_view.burn_stable_block_height);
            self.hint_download_rescan(
                self.chain_view
                    .burn_stable_block_height
                    .saturating_sub(self.burnchain.first_block_height),
                false,
            );

            // update cached burnchain view for /v2/info
            self.chain_view = new_chain_view;
            self.chain_view_stable_consensus_hash = new_chain_view_stable_consensus_hash;
        }

        if sn.burn_header_hash != self.burnchain_tip.burn_header_hash {
            // try processing previously-buffered messages (best-effort)
            let buffered_messages = mem::replace(&mut self.pending_messages, HashMap::new());
            ret = self.handle_unsolicited_messages(sortdb, chainstate, buffered_messages, false)?;
        }

        // update cached stacks chain view for /v2/info
        self.burnchain_tip = sn;

        Ok(ret)
    }

    /// Update p2p networking state.
    /// -- accept new connections
    /// -- send data on ready sockets
    /// -- receive data on ready sockets
    /// -- clear out timed-out requests
    fn dispatch_network(
        &mut self,
        network_result: &mut NetworkResult,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        mut dns_client_opt: Option<&mut DNSClient>,
        download_backpressure: bool,
        ibd: bool,
        mut poll_state: NetworkPollState,
    ) -> Result<(), net_error> {
        if self.network.is_none() {
            test_debug!("{:?}: network not connected", &self.local_peer);
            return Err(net_error::NotConnected);
        }

        // set up new inbound conversations
        self.process_new_sockets(&mut poll_state)?;

        // set up sockets that have finished connecting
        self.process_connecting_sockets(&mut poll_state);

        // find out who is inbound and unauthenticated
        let unauthenticated_inbounds = self.find_unauthenticated_inbound_convos();

        // run existing conversations, clear out broken ones, and get back messages forwarded to us
        let (error_events, unsolicited_messages) =
            self.process_ready_sockets(sortdb, chainstate, &mut poll_state);
        for error_event in error_events {
            debug!(
                "{:?}: Failed connection on event {}",
                &self.local_peer, error_event
            );
            self.deregister_peer(error_event);
        }
        let unhandled_messages =
            self.handle_unsolicited_messages(sortdb, chainstate, unsolicited_messages, true)?;
        network_result.consume_unsolicited(unhandled_messages);

        // schedule now-authenticated inbound convos for pingback
        self.schedule_network_pingbacks(unauthenticated_inbounds)?;

        // do some Actual Work(tm)
        // do this _after_ processing new sockets, so the act of opening a socket doesn't trample
        // an already-used network ID.
        let do_prune = self.do_network_work(
            sortdb,
            chainstate,
            &mut dns_client_opt,
            download_backpressure,
            ibd,
            network_result,
        )?;
        if do_prune {
            // prune back our connections if it's been a while
            // (only do this if we're done with all other tasks).
            // Also, process banned peers.
            let mut dead_events = self.process_bans()?;
            for dead in dead_events.drain(..) {
                debug!(
                    "{:?}: Banned connection on event {}",
                    &self.local_peer, dead
                );
                self.deregister_peer(dead);
            }
            self.prune_connections();
            let outbound_neighbors = PeerNetwork::count_outbound_conversations(&self.peers);
            let inbound_neighbors = self.peers.len() - outbound_neighbors as usize;
            update_outbound_neighbors(outbound_neighbors as i64);
            update_inbound_neighbors(inbound_neighbors as i64);
        }

        // In parallel, do a neighbor walk, but only if we're not doing the initial block download
        self.do_network_neighbor_walk()?;

        // download attachments
        self.do_attachment_downloads(chainstate, dns_client_opt, network_result)?;

        // remove timed-out requests from other threads
        for (_, convo) in self.peers.iter_mut() {
            convo.clear_timeouts();
        }

        // clear out peers that we haven't heard from in our heartbeat interval
        self.disconnect_unresponsive();

        // queue up pings to neighbors we haven't spoken to in a while
        self.queue_ping_heartbeats();

        // move conversations along
        let error_events = self.flush_relay_handles();
        for error_event in error_events {
            debug!(
                "{:?}: Failed connection on event {}",
                &self.local_peer, error_event
            );
            self.deregister_peer(error_event);
        }

        // is our key about to expire?  do we need to re-key?
        // NOTE: must come last since it invalidates local_peer
        if self.local_peer.private_key_expire < self.chain_view.burn_block_height + 1 {
            self.peerdb.rekey(
                self.local_peer.private_key_expire + self.connection_opts.private_key_lifetime,
            )?;
            let new_local_peer = self.load_local_peer()?;
            let old_local_peer = self.local_peer.clone();
            self.local_peer = new_local_peer;
            self.rekey(Some(&old_local_peer));
        }

        // update our relay statistics, so we know who to forward messages to
        self.update_relayer_stats(&network_result);

        // finally, handle network I/O requests from other threads, and get back reply handles to them.
        // do this after processing new sockets, so we don't accidentally re-use an event ID.
        self.dispatch_requests();

        // fault injection -- periodically disconnect from everyone
        if cfg!(test) {
            if let Some(disconnect_interval) = self.connection_opts.force_disconnect_interval {
                if self.fault_last_disconnect + disconnect_interval < get_epoch_time_secs() {
                    debug!(
                        "{:?}: Fault injection: forcing disconnect",
                        &self.local_peer
                    );
                    self.disconnect_all();
                    self.fault_last_disconnect = get_epoch_time_secs();
                }
            }
        }

        Ok(())
    }

    /// Store a single transaction
    /// Return true if stored; false if it was a dup.
    /// Has to be done here, since only the p2p network has the unconfirmed state.
    fn store_transaction(
        mempool: &mut MemPoolDB,
        chainstate: &mut StacksChainState,
        consensus_hash: &ConsensusHash,
        block_hash: &BlockHeaderHash,
        tx: StacksTransaction,
        event_observer: Option<&dyn MemPoolEventDispatcher>,
    ) -> bool {
        let txid = tx.txid();
        if mempool.has_tx(&txid) {
            debug!("Already have tx {}", txid);
            return false;
        }

        if let Err(e) = mempool.submit(chainstate, consensus_hash, block_hash, &tx, event_observer)
        {
            warn!("Transaction rejected from mempool, {}", &e.into_json(&txid));
            return false;
        }

        debug!("Stored tx {}", txid);
        return true;
    }

    /// Store all inbound transactions, and return the ones that we actually stored so they can be
    /// relayed.
    pub fn store_transactions(
        mempool: &mut MemPoolDB,
        chainstate: &mut StacksChainState,
        sortdb: &SortitionDB,
        network_result: &mut NetworkResult,
        event_observer: Option<&dyn MemPoolEventDispatcher>,
    ) -> Result<(), net_error> {
        let (canonical_consensus_hash, canonical_block_hash) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn())?;

        let mut ret: HashMap<NeighborKey, Vec<(Vec<RelayData>, StacksTransaction)>> =
            HashMap::new();

        // messages pushed via the p2p network
        for (nk, tx_data) in network_result.pushed_transactions.drain() {
            for (relayers, tx) in tx_data.into_iter() {
                if PeerNetwork::store_transaction(
                    mempool,
                    chainstate,
                    &canonical_consensus_hash,
                    &canonical_block_hash,
                    tx.clone(),
                    event_observer,
                ) {
                    if let Some(ref mut new_tx_data) = ret.get_mut(&nk) {
                        new_tx_data.push((relayers, tx));
                    } else {
                        ret.insert(nk.clone(), vec![(relayers, tx)]);
                    }
                }
            }
        }

        // (HTTP-uploaded transactions are already in the mempool)

        network_result.pushed_transactions.extend(ret);
        Ok(())
    }

    /// Top-level main-loop circuit to take.
    /// -- polls the peer network and http network server sockets to get new sockets and detect ready sockets
    /// -- carries out network conversations
    /// -- receives and dispatches requests from other threads
    /// -- runs the p2p and http peer main loop
    /// Returns the table of unhandled network messages to be acted upon, keyed by the neighbors
    /// that sent them (i.e. keyed by their event IDs)
    pub fn run(
        &mut self,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        mempool: &mut MemPoolDB,
        dns_client_opt: Option<&mut DNSClient>,
        download_backpressure: bool,
        ibd: bool,
        poll_timeout: u64,
        handler_args: &RPCHandlerArgs,
        attachment_requests: &mut HashSet<AttachmentInstance>,
    ) -> Result<NetworkResult, net_error> {
        debug!(">>>>>>>>>>>>>>>>>>>>>>> Begin Network Dispatch (poll for {}) >>>>>>>>>>>>>>>>>>>>>>>>>>>>", poll_timeout);
        let mut poll_states = match self.network {
            None => {
                debug!("{:?}: network not connected", &self.local_peer);
                Err(net_error::NotConnected)
            }
            Some(ref mut network) => {
                let poll_result = network.poll(poll_timeout);
                poll_result
            }
        }?;

        let p2p_poll_state = poll_states
            .remove(&self.p2p_network_handle)
            .expect("BUG: no poll state for p2p network handle");
        let http_poll_state = poll_states
            .remove(&self.http_network_handle)
            .expect("BUG: no poll state for http network handle");

        let mut network_result = NetworkResult::new(
            self.num_state_machine_passes,
            self.num_inv_sync_passes,
            self.num_downloader_passes,
        );

        // update local-peer state
        self.refresh_local_peer()?;

        // update burnchain view, before handling any HTTP connections
        let unsolicited_buffered_messages = self.refresh_burnchain_view(sortdb, chainstate)?;
        network_result.consume_unsolicited(unsolicited_buffered_messages);

        // update PoX view, before handling any HTTP connections
        self.refresh_sortition_view(sortdb)?;

        // This operation needs to be performed before any early return:
        // Events are being parsed and dispatched here once and we want to
        // enqueue them.
        match PeerNetwork::with_attachments_downloader(self, |network, attachments_downloader| {
            let mut known_attachments = attachments_downloader.enqueue_new_attachments(
                attachment_requests,
                &mut network.atlasdb,
                false,
            )?;
            network_result.attachments.append(&mut known_attachments);
            Ok(())
        }) {
            Ok(_) => {}
            Err(e) => {
                warn!("Atlas: updating attachment inventory failed: {}", e);
            }
        }

        PeerNetwork::with_network_state(self, |ref mut network, ref mut network_state| {
            let http_stacks_msgs = PeerNetwork::with_http(network, |ref mut net, ref mut http| {
                http.run(
                    network_state,
                    net,
                    sortdb,
                    chainstate,
                    mempool,
                    http_poll_state,
                    handler_args,
                )
            })?;
            network_result.consume_http_uploads(http_stacks_msgs);
            Ok(())
        })?;

        self.dispatch_network(
            &mut network_result,
            sortdb,
            chainstate,
            dns_client_opt,
            download_backpressure,
            ibd,
            p2p_poll_state,
        )?;

        debug!("<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< End Network Dispatch <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<");
        Ok(network_result)
    }
}

#[cfg(test)]
mod test {
    use std::thread;
    use std::time;

    use rand;
    use rand::RngCore;

    use burnchains::burnchain::*;
    use burnchains::*;
    use chainstate::stacks::test::*;
    use chainstate::stacks::*;
    use net::atlas::*;
    use net::codec::*;
    use net::db::*;
    use net::*;
    use util::log;
    use util::sleep_ms;
    use util::test::*;

    use crate::types::chainstate::BurnchainHeaderHash;

    use super::*;

    fn make_random_peer_address() -> PeerAddress {
        let mut rng = rand::thread_rng();
        let mut bytes = [0u8; 16];
        rng.fill_bytes(&mut bytes);
        PeerAddress(bytes)
    }

    fn make_test_neighbor(port: u16) -> Neighbor {
        let neighbor = Neighbor {
            addr: NeighborKey {
                peer_version: 0x12345678,
                network_id: 0x9abcdef0,
                addrbytes: PeerAddress([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x7f,
                    0x00, 0x00, 0x01,
                ]),
                port: port,
            },
            public_key: Secp256k1PublicKey::from_hex(
                "02fa66b66f8971a8cd4d20ffded09674e030f0f33883f337f34b95ad4935bac0e3",
            )
            .unwrap(),
            expire_block: 23456,
            last_contact_time: 1552509642,
            allowed: -1,
            denied: -1,
            asn: 34567,
            org: 45678,
            in_degree: 1,
            out_degree: 1,
        };
        neighbor
    }

    fn make_test_p2p_network(initial_neighbors: &Vec<Neighbor>) -> PeerNetwork {
        let mut conn_opts = ConnectionOptions::default();
        conn_opts.inbox_maxlen = 5;
        conn_opts.outbox_maxlen = 5;

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = Burnchain {
            pox_constants: PoxConstants::test_default(),
            peer_version: 0x012345678,
            network_id: 0x9abcdef0,
            chain_name: "bitcoin".to_string(),
            network_name: "testnet".to_string(),
            working_dir: "/nope".to_string(),
            consensus_hash_lifetime: 24,
            stable_confirmations: 7,
            initial_reward_start_block: 50,
            first_block_height: 50,
            first_block_timestamp: 0,
            first_block_hash: first_burn_hash.clone(),
        };

        let mut burnchain_view = BurnchainView {
            burn_block_height: 12345,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12339,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        burnchain_view.make_test_data();

        let db = PeerDB::connect_memory(
            0x9abcdef0,
            0,
            23456,
            "http://test-p2p.com".into(),
            &vec![],
            initial_neighbors,
        )
        .unwrap();
        let atlas_config = AtlasConfig::default(false);
        let atlasdb = AtlasDB::connect_memory(atlas_config).unwrap();

        let local_peer = PeerDB::get_local_peer(db.conn()).unwrap();
        let p2p = PeerNetwork::new(
            db,
            atlasdb,
            local_peer,
            0x12345678,
            burnchain,
            burnchain_view,
            conn_opts,
        );
        p2p
    }

    #[test]
    fn test_event_id_no_connecting_leaks() {
        with_timeout(100, || {
            let neighbor = make_test_neighbor(2300);
            let mut p2p = make_test_p2p_network(&vec![]);

            use std::net::TcpListener;
            let listener = TcpListener::bind("127.0.0.1:2300").unwrap();

            // start fake neighbor endpoint, which will accept once and wait 35 seconds
            let endpoint_thread = thread::spawn(move || {
                let (sock, addr) = listener.accept().unwrap();
                test_debug!("Accepted {:?}", &addr);
                thread::sleep(time::Duration::from_millis(35_000));
            });

            p2p.bind(
                &"127.0.0.1:2400".parse().unwrap(),
                &"127.0.0.1:2401".parse().unwrap(),
            )
            .unwrap();
            p2p.connect_peer(&neighbor.addr).unwrap();

            // start dispatcher
            let p2p_thread = thread::spawn(move || {
                let mut total_disconnected = 0;
                for i in 0..40 {
                    test_debug!("dispatch batch {}", i);

                    p2p.dispatch_requests();
                    let mut poll_states = match p2p.network {
                        None => {
                            panic!("network not connected");
                        }
                        Some(ref mut network) => network.poll(100).unwrap(),
                    };

                    let mut p2p_poll_state = poll_states.remove(&p2p.p2p_network_handle).unwrap();

                    p2p.process_new_sockets(&mut p2p_poll_state).unwrap();
                    p2p.process_connecting_sockets(&mut p2p_poll_state);
                    total_disconnected += p2p.disconnect_unresponsive();

                    let ne = p2p.network.as_ref().unwrap().num_events();
                    test_debug!("{} events", ne);

                    thread::sleep(time::Duration::from_millis(1000));
                }

                assert_eq!(total_disconnected, 1);

                // no leaks -- only server events remain
                assert_eq!(p2p.network.as_ref().unwrap().num_events(), 2);
            });

            p2p_thread.join().unwrap();
            test_debug!("dispatcher thread joined");

            endpoint_thread.join().unwrap();
            test_debug!("fake endpoint thread joined");
        })
    }

    // tests relay_signed_message()
    #[test]
    #[ignore]
    fn test_dispatch_requests_connect_and_message_relay() {
        with_timeout(100, || {
            let neighbor = make_test_neighbor(2100);

            let mut p2p = make_test_p2p_network(&vec![]);

            let ping = StacksMessage::new(
                p2p.peer_version,
                p2p.local_peer.network_id,
                p2p.chain_view.burn_block_height,
                &p2p.chain_view.burn_block_hash,
                p2p.chain_view.burn_stable_block_height,
                &p2p.chain_view.burn_stable_block_hash,
                StacksMessageType::Ping(PingData::new()),
            );

            let mut h = p2p.new_handle(1);

            use std::net::TcpListener;
            let listener = TcpListener::bind("127.0.0.1:2100").unwrap();

            // start fake neighbor endpoint, which will accept once and wait 5 seconds
            let endpoint_thread = thread::spawn(move || {
                let (sock, addr) = listener.accept().unwrap();
                test_debug!("Accepted {:?}", &addr);
                thread::sleep(time::Duration::from_millis(5000));
            });

            p2p.bind(
                &"127.0.0.1:2000".parse().unwrap(),
                &"127.0.0.1:2001".parse().unwrap(),
            )
            .unwrap();
            p2p.connect_peer(&neighbor.addr).unwrap();

            // start dispatcher
            let p2p_thread = thread::spawn(move || {
                for i in 0..5 {
                    test_debug!("dispatch batch {}", i);

                    p2p.dispatch_requests();
                    let mut poll_states = match p2p.network {
                        None => {
                            panic!("network not connected");
                        }
                        Some(ref mut network) => network.poll(100).unwrap(),
                    };

                    let mut p2p_poll_state = poll_states.remove(&p2p.p2p_network_handle).unwrap();

                    p2p.process_new_sockets(&mut p2p_poll_state).unwrap();
                    p2p.process_connecting_sockets(&mut p2p_poll_state);

                    thread::sleep(time::Duration::from_millis(1000));
                }
            });

            // will eventually accept
            let mut sent = false;
            for i in 0..10 {
                match h.relay_signed_message(neighbor.addr.clone(), ping.clone()) {
                    Ok(_) => {
                        sent = true;
                        break;
                    }
                    Err(net_error::NoSuchNeighbor) | Err(net_error::FullHandle) => {
                        test_debug!("Failed to relay; try again in {} ms", (i + 1) * 1000);
                        sleep_ms((i + 1) * 1000);
                    }
                    Err(e) => {
                        eprintln!("{:?}", &e);
                        assert!(false);
                    }
                }
            }

            if !sent {
                error!("Failed to relay to neighbor");
                assert!(false);
            }

            p2p_thread.join().unwrap();
            test_debug!("dispatcher thread joined");

            endpoint_thread.join().unwrap();
            test_debug!("fake endpoint thread joined");
        })
    }

    #[test]
    #[ignore]
    fn test_dispatch_requests_connect_and_ban() {
        with_timeout(100, || {
            let neighbor = make_test_neighbor(2200);

            let mut p2p = make_test_p2p_network(&vec![]);

            let txn = StacksMessage::new(
                p2p.peer_version,
                p2p.local_peer.network_id,
                p2p.chain_view.burn_block_height,
                &p2p.chain_view.burn_block_hash,
                p2p.chain_view.burn_stable_block_height,
                &p2p.chain_view.burn_stable_block_hash,
                StacksMessageType::Ping(PingData::new()),
            );

            let mut h = p2p.new_handle(1);

            use std::net::TcpListener;
            let listener = TcpListener::bind("127.0.0.1:2200").unwrap();

            // start fake neighbor endpoint, which will accept once and wait 5 seconds
            let endpoint_thread = thread::spawn(move || {
                let (sock, addr) = listener.accept().unwrap();
                test_debug!("Accepted {:?}", &addr);
                thread::sleep(time::Duration::from_millis(5000));
            });

            p2p.bind(
                &"127.0.0.1:2010".parse().unwrap(),
                &"127.0.0.1:2011".parse().unwrap(),
            )
            .unwrap();
            p2p.connect_peer(&neighbor.addr).unwrap();

            let (sx, rx) = sync_channel(1);

            // start dispatcher, and relay back the list of peers we banned
            let p2p_thread = thread::spawn(move || {
                let mut banned_peers = vec![];
                for i in 0..5 {
                    test_debug!("dispatch batch {}", i);

                    p2p.dispatch_requests();
                    let mut poll_state = match p2p.network {
                        None => {
                            panic!("network not connected");
                        }
                        Some(ref mut network) => network.poll(100).unwrap(),
                    };

                    let mut p2p_poll_state = poll_state.remove(&p2p.p2p_network_handle).unwrap();

                    p2p.process_new_sockets(&mut p2p_poll_state).unwrap();
                    p2p.process_connecting_sockets(&mut p2p_poll_state);

                    let mut banned = p2p.process_bans().unwrap();
                    if banned.len() > 0 {
                        test_debug!("Banned {} peer(s)", banned.len());
                    }

                    banned_peers.append(&mut banned);

                    thread::sleep(time::Duration::from_millis(5000));
                }

                let _ = sx.send(banned_peers);
            });

            // will eventually accept and ban
            for i in 0..5 {
                match h.ban_peers(vec![neighbor.addr.clone()]) {
                    Ok(_) => {
                        continue;
                    }
                    Err(net_error::FullHandle) => {
                        test_debug!("Failed to relay; try again in {} ms", 1000 * (i + 1));
                        sleep_ms(1000 * (i + 1));
                    }
                    Err(e) => {
                        eprintln!("{:?}", &e);
                        assert!(false);
                    }
                }
            }

            let banned = rx.recv().unwrap();
            assert!(banned.len() >= 1);

            p2p_thread.join().unwrap();
            test_debug!("dispatcher thread joined");

            endpoint_thread.join().unwrap();
            test_debug!("fake endpoint thread joined");
        })
    }
}
