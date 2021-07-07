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
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::convert::TryFrom;
use std::io::Read;
use std::io::Write;
use std::mem;
use std::net::SocketAddr;

use rand;
use rand::thread_rng;
use rand::Rng;

use burnchains::Burnchain;
use burnchains::BurnchainView;
use burnchains::PublicKey;
use chainstate::burn::db::sortdb;
use chainstate::burn::db::sortdb::{BlockHeaderCache, SortitionDB};
use chainstate::stacks::db::StacksChainState;
use chainstate::stacks::StacksPublicKey;
use monitoring;
use net::asn::ASEntry4;
use net::codec::*;
use net::connection::ConnectionOptions;
use net::connection::ConnectionP2P;
use net::connection::ReplyHandleP2P;
use net::db::PeerDB;
use net::db::*;
use net::neighbors::MAX_NEIGHBOR_BLOCK_DELAY;
use net::relay::*;
use net::Error as net_error;
use net::GetBlocksInv;
use net::GetPoxInv;
use net::Neighbor;
use net::NeighborKey;
use net::PeerAddress;
use net::StacksMessage;
use net::StacksP2P;
use net::GETPOXINV_MAX_BITLEN;
use net::*;
use util::db::DBConn;
use util::db::Error as db_error;
use util::get_epoch_time_secs;
use util::hash::to_hex;
use util::log;
use util::secp256k1::Secp256k1PrivateKey;
use util::secp256k1::Secp256k1PublicKey;

use crate::types::chainstate::PoxId;
use crate::types::chainstate::StacksBlockHeader;
use crate::types::StacksPublicKeyBuffer;

// did we or did we not successfully send a message?
#[derive(Debug, Clone)]
pub struct NeighborHealthPoint {
    pub success: bool,
    pub time: u64,
}

impl Default for NeighborHealthPoint {
    fn default() -> NeighborHealthPoint {
        NeighborHealthPoint {
            success: false,
            time: 0,
        }
    }
}

pub const NUM_HEALTH_POINTS: usize = 32;
pub const HEALTH_POINT_LIFETIME: u64 = 12 * 3600; // 12 hours

pub const NUM_BLOCK_POINTS: usize = 32;
pub const BLOCK_POINT_LIFETIME: u64 = 600;

pub const MAX_PEER_HEARTBEAT_INTERVAL: usize = 3600 * 6; // 6 hours

/// Statistics on relayer hints in Stacks messages.  Used to deduce network choke points.
#[derive(Debug, Clone)]
pub struct RelayStats {
    pub num_messages: u64, // how many messages a relayer has pushed to this neighbor
    pub num_bytes: u64,    // how many bytes a relayer has pushed to this neighbor
    pub last_seen: u64,    // the last time (in seconds) since we've seen this relayer
}

impl RelayStats {
    pub fn new() -> RelayStats {
        RelayStats {
            num_messages: 0,
            num_bytes: 0,
            last_seen: 0,
        }
    }

    /// Combine two relayers' stats
    pub fn merge(&mut self, other: RelayStats) {
        if other.last_seen > self.last_seen {
            self.num_messages += other.num_messages;
            self.num_bytes += other.num_bytes;
            self.last_seen = get_epoch_time_secs();
        }
    }
}

#[derive(Debug, Clone)]
pub struct NeighborStats {
    pub outbound: bool,
    pub first_contact_time: u64,
    pub last_contact_time: u64,
    pub last_send_time: u64,
    pub last_recv_time: u64,
    pub last_handshake_time: u64,
    pub bytes_tx: u64,
    pub bytes_rx: u64,
    pub msgs_tx: u64,
    pub msgs_rx: u64,
    pub msgs_rx_unsolicited: u64,
    pub msgs_err: u64,
    pub healthpoints: VecDeque<NeighborHealthPoint>,
    pub msg_rx_counts: HashMap<StacksMessageID, u64>,
    pub block_push_rx_counts: VecDeque<(u64, u64)>, // (count, num bytes)
    pub microblocks_push_rx_counts: VecDeque<(u64, u64)>, // (count, num bytes)
    pub transaction_push_rx_counts: VecDeque<(u64, u64)>, // (count, num bytes)
    pub relayed_messages: HashMap<NeighborAddress, RelayStats>,
}

impl NeighborStats {
    pub fn new(outbound: bool) -> NeighborStats {
        NeighborStats {
            outbound: outbound,
            first_contact_time: 0,
            last_contact_time: 0,
            last_send_time: 0,
            last_recv_time: 0,
            last_handshake_time: 0,
            bytes_tx: 0,
            bytes_rx: 0,
            msgs_tx: 0,
            msgs_rx: 0,
            msgs_rx_unsolicited: 0,
            msgs_err: 0,
            healthpoints: VecDeque::new(),
            msg_rx_counts: HashMap::new(),
            block_push_rx_counts: VecDeque::new(),
            microblocks_push_rx_counts: VecDeque::new(),
            transaction_push_rx_counts: VecDeque::new(),
            relayed_messages: HashMap::new(),
        }
    }

    pub fn add_healthpoint(&mut self, success: bool) -> () {
        let hp = NeighborHealthPoint {
            success: success,
            time: get_epoch_time_secs(),
        };
        self.healthpoints.push_back(hp);
        while self.healthpoints.len() > NUM_HEALTH_POINTS {
            self.healthpoints.pop_front();
        }
    }

    pub fn add_block_push(&mut self, message_size: u64) -> () {
        self.block_push_rx_counts
            .push_back((get_epoch_time_secs(), message_size));
        while self.block_push_rx_counts.len() > NUM_BLOCK_POINTS {
            self.block_push_rx_counts.pop_front();
        }
    }

    pub fn add_microblocks_push(&mut self, message_size: u64) -> () {
        self.microblocks_push_rx_counts
            .push_back((get_epoch_time_secs(), message_size));
        while self.microblocks_push_rx_counts.len() > NUM_BLOCK_POINTS {
            self.microblocks_push_rx_counts.pop_front();
        }
    }

    pub fn add_transaction_push(&mut self, message_size: u64) -> () {
        self.transaction_push_rx_counts
            .push_back((get_epoch_time_secs(), message_size));
        while self.transaction_push_rx_counts.len() > NUM_BLOCK_POINTS {
            self.transaction_push_rx_counts.pop_front();
        }
    }

    pub fn add_relayer(&mut self, addr: &NeighborAddress, num_bytes: u64) -> () {
        if let Some(stats) = self.relayed_messages.get_mut(addr) {
            stats.num_messages += 1;
            stats.num_bytes += num_bytes;
            stats.last_seen = get_epoch_time_secs();
        } else {
            let info = RelayStats {
                num_messages: 1,
                num_bytes: num_bytes,
                last_seen: get_epoch_time_secs(),
            };
            self.relayed_messages.insert(addr.clone(), info);
        }
    }

    pub fn take_relayers(&mut self) -> HashMap<NeighborAddress, RelayStats> {
        let ret = mem::replace(&mut self.relayed_messages, HashMap::new());
        ret
    }

    /// Get a peer's perceived health -- the last $NUM_HEALTH_POINTS successful messages divided by
    /// the total.
    pub fn get_health_score(&self) -> f64 {
        // if we don't have enough data, assume 50%
        if self.healthpoints.len() < NUM_HEALTH_POINTS {
            return 0.5;
        }

        let mut successful = 0;
        let mut total = 0;
        let now = get_epoch_time_secs();
        for hp in self.healthpoints.iter() {
            // penalize stale data points -- only look at recent data
            if hp.success && now < hp.time + HEALTH_POINT_LIFETIME {
                successful += 1;
            }
            total += 1;
        }
        (successful as f64) / (total as f64)
    }

    fn get_bandwidth(rx_counts: &VecDeque<(u64, u64)>, lifetime: u64) -> f64 {
        if rx_counts.len() < 2 {
            return 0.0;
        }

        let elapsed_time_start = rx_counts.front().unwrap().0;
        let elapsed_time_end = rx_counts.back().unwrap().0;
        let now = get_epoch_time_secs();

        let mut total_bytes = 0;
        for (time, size) in rx_counts.iter() {
            if now < time + lifetime {
                total_bytes += size;
            }
        }

        if elapsed_time_start == elapsed_time_end {
            total_bytes as f64
        } else {
            (total_bytes as f64) / ((elapsed_time_end - elapsed_time_start) as f64)
        }
    }

    /// Get a peer's total block-push bandwidth usage.
    pub fn get_block_push_bandwidth(&self) -> f64 {
        NeighborStats::get_bandwidth(&self.block_push_rx_counts, BLOCK_POINT_LIFETIME)
    }

    /// Get a peer's total microblock-push bandwidth usage.
    pub fn get_microblocks_push_bandwidth(&self) -> f64 {
        NeighborStats::get_bandwidth(&self.microblocks_push_rx_counts, BLOCK_POINT_LIFETIME)
    }

    /// Get a peer's total transaction-push bandwidth usage
    pub fn get_transaction_push_bandwidth(&self) -> f64 {
        NeighborStats::get_bandwidth(&self.transaction_push_rx_counts, BLOCK_POINT_LIFETIME)
    }

    /// Determine how many of a particular message this peer has received
    pub fn get_message_recv_count(&self, msg_id: StacksMessageID) -> u64 {
        *(self.msg_rx_counts.get(&msg_id).unwrap_or(&0))
    }
}

/// P2P ongoing conversation with another Stacks peer
pub struct ConversationP2P {
    pub instantiated: u64,

    pub network_id: u32,
    pub version: u32,
    pub connection: ConnectionP2P,
    pub conn_id: usize,

    pub burnchain: Burnchain, // copy of our burnchain config
    pub heartbeat: u32,       // how often do we send heartbeats?

    pub peer_network_id: u32,
    pub peer_version: u32,
    pub peer_services: u16,
    pub peer_addrbytes: PeerAddress,      // from socketaddr
    pub peer_port: u16,                   // from socketaddr
    pub handshake_addrbytes: PeerAddress, // from handshake
    pub handshake_port: u16,              // from handshake
    pub peer_heartbeat: u32,              // how often do we need to ping the remote peer?
    pub peer_expire_block_height: u64,    // when does the peer's key expire?

    pub data_url: UrlString, // where does this peer's data live?  Set to a 0-length string if not known.

    // highest block height and consensus hash this peer has seen
    pub burnchain_tip_height: u64,
    pub burnchain_tip_burn_header_hash: BurnchainHeaderHash,
    pub burnchain_stable_tip_height: u64,
    pub burnchain_stable_tip_burn_header_hash: BurnchainHeaderHash,

    pub stats: NeighborStats,

    // outbound replies
    pub reply_handles: VecDeque<ReplyHandleP2P>,
}

impl fmt::Display for ConversationP2P {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "convo:id={},outbound={},peer={:?}",
            self.conn_id,
            self.stats.outbound,
            &self.to_neighbor_key()
        )
    }
}

impl fmt::Debug for ConversationP2P {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "convo:id={},outbound={},peer={:?}",
            self.conn_id,
            self.stats.outbound,
            &self.to_neighbor_key()
        )
    }
}

impl NeighborKey {
    pub fn from_handshake(
        peer_version: u32,
        network_id: u32,
        handshake_data: &HandshakeData,
    ) -> NeighborKey {
        NeighborKey {
            peer_version: peer_version,
            network_id: network_id,
            addrbytes: handshake_data.addrbytes.clone(),
            port: handshake_data.port,
        }
    }

    pub fn from_socketaddr(peer_version: u32, network_id: u32, addr: &SocketAddr) -> NeighborKey {
        NeighborKey {
            peer_version: peer_version,
            network_id: network_id,
            addrbytes: PeerAddress::from_socketaddr(addr),
            port: addr.port(),
        }
    }
}

impl Neighbor {
    /// Update fields in this neighbor from a given handshake.
    /// Also, re-calculate the peer's ASN and organization ID
    pub fn handshake_update(
        &mut self,
        conn: &DBConn,
        handshake_data: &HandshakeData,
    ) -> Result<(), net_error> {
        let pubk = handshake_data.node_public_key.to_public_key()?;
        let asn_opt =
            PeerDB::asn_lookup(conn, &handshake_data.addrbytes).map_err(net_error::DBError)?;

        let asn = match asn_opt {
            Some(a) => a,
            None => 0,
        };

        self.public_key = pubk;
        self.expire_block = handshake_data.expire_block_height;
        self.last_contact_time = get_epoch_time_secs();

        if asn != 0 {
            self.asn = asn;
            self.org = asn; // TODO; AS number is a place-holder for an organization ID (an organization can own multiple ASs)
        }

        Ok(())
    }

    pub fn from_handshake(
        conn: &DBConn,
        peer_version: u32,
        network_id: u32,
        handshake_data: &HandshakeData,
    ) -> Result<Neighbor, net_error> {
        let addr = NeighborKey::from_handshake(peer_version, network_id, handshake_data);
        let pubk = handshake_data.node_public_key.to_public_key()?;

        let peer_opt = PeerDB::get_peer(conn, network_id, &addr.addrbytes, addr.port)
            .map_err(net_error::DBError)?;

        let mut neighbor = match peer_opt {
            Some(neighbor) => {
                let mut ret = neighbor;
                ret.addr = addr.clone();
                ret
            }
            None => {
                let ret = Neighbor::empty(&addr, &pubk, handshake_data.expire_block_height);
                ret
            }
        };

        #[cfg(test)]
        {
            // setting BLOCKSTACK_NEIGHBOR_TEST_${PORTNUMBER} will let us select an organization
            // for this peer
            use std::env;
            match env::var(format!("BLOCKSTACK_NEIGHBOR_TEST_{}", addr.port).to_string()) {
                Ok(asn_str) => {
                    neighbor.asn = asn_str.parse().unwrap();
                    neighbor.org = neighbor.asn;
                    test_debug!("Override {:?} to ASN/org {}", &neighbor.addr, neighbor.asn);
                }
                Err(_) => {}
            };
        }

        neighbor.handshake_update(conn, &handshake_data)?;
        Ok(neighbor)
    }

    pub fn from_conversation(
        conn: &DBConn,
        convo: &ConversationP2P,
    ) -> Result<Option<Neighbor>, net_error> {
        let addr = convo.to_neighbor_key();
        let peer_opt = PeerDB::get_peer(conn, addr.network_id, &addr.addrbytes, addr.port)
            .map_err(net_error::DBError)?;

        match peer_opt {
            None => Ok(None),
            Some(mut peer) => {
                if peer.asn == 0 {
                    let asn_opt =
                        PeerDB::asn_lookup(conn, &addr.addrbytes).map_err(net_error::DBError)?;

                    match asn_opt {
                        Some(a) => {
                            if a != 0 {
                                peer.asn = a;
                            }
                        }
                        None => {}
                    };
                }
                Ok(Some(peer))
            }
        }
    }
}

impl ConversationP2P {
    /// Create an unconnected conversation
    pub fn new(
        network_id: u32,
        version: u32,
        burnchain: &Burnchain,
        peer_addr: &SocketAddr,
        conn_opts: &ConnectionOptions,
        outbound: bool,
        conn_id: usize,
    ) -> ConversationP2P {
        ConversationP2P {
            instantiated: get_epoch_time_secs(),
            network_id: network_id,
            version: version,
            connection: ConnectionP2P::new(StacksP2P::new(), conn_opts, None),
            conn_id: conn_id,
            heartbeat: conn_opts.heartbeat,
            burnchain: burnchain.clone(),

            peer_network_id: 0,
            peer_version: 0,
            peer_addrbytes: PeerAddress::from_socketaddr(peer_addr),
            peer_port: peer_addr.port(),
            handshake_addrbytes: PeerAddress([0u8; 16]),
            handshake_port: 0,
            peer_heartbeat: 0,
            peer_services: 0,
            peer_expire_block_height: 0,

            data_url: UrlString::try_from("".to_string()).unwrap(),

            burnchain_tip_height: 0,
            burnchain_tip_burn_header_hash: BurnchainHeaderHash::zero(),
            burnchain_stable_tip_height: 0,
            burnchain_stable_tip_burn_header_hash: BurnchainHeaderHash::zero(),

            stats: NeighborStats::new(outbound),
            reply_handles: VecDeque::new(),
        }
    }

    pub fn set_public_key(&mut self, pubkey_opt: Option<Secp256k1PublicKey>) -> () {
        self.connection.set_public_key(pubkey_opt);
    }

    pub fn to_neighbor_key(&self) -> NeighborKey {
        NeighborKey {
            peer_version: self.peer_version,
            network_id: self.peer_network_id,
            addrbytes: self.peer_addrbytes.clone(),
            port: self.peer_port,
        }
    }

    pub fn to_handshake_neighbor_key(&self) -> NeighborKey {
        NeighborKey {
            peer_version: self.peer_version,
            network_id: self.peer_network_id,
            addrbytes: self.handshake_addrbytes.clone(),
            port: self.handshake_port,
        }
    }

    pub fn best_effort_neighbor_key(&self) -> NeighborKey {
        if self.handshake_port > 0 && self.peer_version > 0 {
            // got a handshake response already
            self.to_handshake_neighbor_key()
        } else {
            // assume we know nothing from this neighbor
            NeighborKey {
                peer_version: self.version,
                network_id: self.network_id,
                addrbytes: self.peer_addrbytes.clone(),
                port: self.peer_port,
            }
        }
    }

    pub fn to_neighbor_address(&self) -> NeighborAddress {
        let pubkh = if let Some(ref pubk) = self.ref_public_key() {
            Hash160::from_node_public_key(pubk)
        } else {
            Hash160([0u8; 20])
        };

        NeighborAddress {
            addrbytes: self.peer_addrbytes.clone(),
            port: self.peer_port,
            public_key_hash: pubkh,
        }
    }

    pub fn to_handshake_neighbor_address(&self) -> NeighborAddress {
        let pubkh = if let Some(ref pubk) = self.ref_public_key() {
            Hash160::from_node_public_key(pubk)
        } else {
            Hash160([0u8; 20])
        };

        NeighborAddress {
            addrbytes: self.handshake_addrbytes.clone(),
            port: self.handshake_port,
            public_key_hash: pubkh,
        }
    }

    pub fn is_outbound(&self) -> bool {
        self.stats.outbound
    }

    pub fn is_authenticated(&self) -> bool {
        self.connection.has_public_key()
    }

    pub fn get_public_key(&self) -> Option<StacksPublicKey> {
        self.connection.get_public_key()
    }

    pub fn get_public_key_hash(&self) -> Option<Hash160> {
        self.ref_public_key()
            .map(|pubk| Hash160::from_node_public_key(pubk))
    }

    pub fn ref_public_key(&self) -> Option<&StacksPublicKey> {
        self.connection.ref_public_key()
    }

    pub fn get_burnchain_tip_height(&self) -> u64 {
        self.burnchain_tip_height
    }

    pub fn get_stable_burnchain_tip_height(&self) -> u64 {
        self.burnchain_stable_tip_height
    }

    pub fn get_burnchain_tip_burn_header_hash(&self) -> BurnchainHeaderHash {
        self.burnchain_tip_burn_header_hash.clone()
    }

    pub fn get_stable_burnchain_tip_burn_header_hash(&self) -> BurnchainHeaderHash {
        self.burnchain_stable_tip_burn_header_hash.clone()
    }

    /// Determine whether or not a given (height, burn_header_hash) pair _disagrees_ with our
    /// burnchain view.  If it does, return true.  If it doesn't (including if the given pair is
    /// simply absent from the chain_view), then return False.
    fn check_burn_header_hash_disagreement(
        block_height: u64,
        their_burn_header_hash: &BurnchainHeaderHash,
        chain_view: &BurnchainView,
    ) -> bool {
        let bhh = match chain_view.last_burn_block_hashes.get(&block_height) {
            Some(ref bhh) => bhh.clone(),
            None => {
                // not present; can't prove disagreement (assume the remote peer is just stale)
                return false;
            }
        };
        if *bhh != *their_burn_header_hash {
            test_debug!(
                "Burn header hash mismatch in preamble: {} != {}",
                bhh,
                their_burn_header_hash
            );
            return true;
        }
        false
    }

    /// Validate an inbound message's preamble against our knowledge of the burn chain.
    /// Return Ok(true) if we can proceed
    /// Return Ok(false) if we can't proceed, but the remote peer is not in violation of the protocol
    /// Return Err(net_error::InvalidMessage) if the remote peer returns an invalid message in
    ///     violation of the protocol
    pub fn is_preamble_valid(
        &self,
        msg: &StacksMessage,
        chain_view: &BurnchainView,
    ) -> Result<bool, net_error> {
        if msg.preamble.network_id != self.network_id {
            // not on our network
            debug!(
                "{:?}: Preamble invalid: wrong network ID: {:x} != {:x}",
                &self, msg.preamble.network_id, self.network_id
            );
            return Err(net_error::InvalidMessage);
        }
        if (msg.preamble.peer_version & 0xff000000) != (self.version & 0xff000000) {
            // major version mismatch
            test_debug!(
                "{:?}: Preamble invalid: wrong peer version: {:x} != {:x}",
                &self,
                msg.preamble.peer_version,
                self.version
            );
            return Err(net_error::InvalidMessage);
        }
        if msg
            .preamble
            .burn_stable_block_height
            .checked_add(self.burnchain.stable_confirmations as u64)
            != Some(msg.preamble.burn_block_height)
        {
            // invalid message
            debug!(
                "{:?}: Preamble invalid: wrong stable block height: {:?} != {}",
                &self,
                msg.preamble
                    .burn_stable_block_height
                    .checked_add(self.burnchain.stable_confirmations as u64),
                msg.preamble.burn_block_height
            );
            return Err(net_error::InvalidMessage);
        }

        if msg.preamble.burn_stable_block_height
            > chain_view.burn_block_height + MAX_NEIGHBOR_BLOCK_DELAY
        {
            // this node is too far ahead of us for neighbor walks, but otherwise still potentially valid
            debug!(
                "{:?}: remote peer is far ahead of us: {} > {}",
                &self, msg.preamble.burn_stable_block_height, chain_view.burn_block_height
            );
        }

        // must agree on stable burn header hash
        let rules_disagree = ConversationP2P::check_burn_header_hash_disagreement(
            msg.preamble.burn_stable_block_height,
            &msg.preamble.burn_stable_block_hash,
            chain_view,
        );
        if rules_disagree {
            // remote peer disagrees on stable burn header hash -- follows different rules than us
            return Err(net_error::InvalidMessage);
        }

        Ok(true)
    }

    /// Get next message sequence number
    fn next_seq(&mut self) -> u32 {
        let mut rng = thread_rng();
        rng.gen::<u32>()
    }

    /// Generate a signed message for this conversation
    pub fn sign_message(
        &mut self,
        chain_view: &BurnchainView,
        private_key: &Secp256k1PrivateKey,
        payload: StacksMessageType,
    ) -> Result<StacksMessage, net_error> {
        let mut msg =
            StacksMessage::from_chain_view(self.version, self.network_id, chain_view, payload);
        msg.sign(self.next_seq(), private_key)?;
        Ok(msg)
    }

    /// Generate a signed forwarded message for this conversation.
    /// Include ourselves as the latest relayer.
    pub fn sign_relay_message(
        &mut self,
        local_peer: &LocalPeer,
        chain_view: &BurnchainView,
        mut relay_hints: Vec<RelayData>,
        payload: StacksMessageType,
    ) -> Result<StacksMessage, net_error> {
        let mut msg =
            StacksMessage::from_chain_view(self.version, self.network_id, chain_view, payload);
        msg.relayers.append(&mut relay_hints);
        msg.sign_relay(
            &local_peer.private_key,
            self.next_seq(),
            &local_peer.to_neighbor_addr(),
        )?;
        Ok(msg)
    }

    /// Generate a signed reply for this conversation
    pub fn sign_reply(
        &mut self,
        chain_view: &BurnchainView,
        private_key: &Secp256k1PrivateKey,
        payload: StacksMessageType,
        seq: u32,
    ) -> Result<StacksMessage, net_error> {
        let mut msg =
            StacksMessage::from_chain_view(self.version, self.network_id, chain_view, payload);
        msg.sign(seq, private_key)?;
        Ok(msg)
    }

    /// sign and reply a message
    fn sign_and_reply(
        &mut self,
        local_peer: &LocalPeer,
        burnchain_view: &BurnchainView,
        request_preamble: &Preamble,
        reply_message: StacksMessageType,
    ) -> Result<ReplyHandleP2P, net_error> {
        let _msgtype = reply_message.get_message_name().to_owned();
        let reply = self.sign_reply(
            burnchain_view,
            &local_peer.private_key,
            reply_message,
            request_preamble.seq,
        )?;
        let reply_handle = self.relay_signed_message(reply).map_err(|e| {
            debug!("Unable to reply a {}: {:?}", _msgtype, &e);
            e
        })?;

        self.stats.msgs_tx += 1;
        Ok(reply_handle)
    }

    /// Sign and forward a message
    pub fn sign_and_forward(
        &mut self,
        local_peer: &LocalPeer,
        burnchain_view: &BurnchainView,
        relay_hints: Vec<RelayData>,
        forward_message: StacksMessageType,
    ) -> Result<ReplyHandleP2P, net_error> {
        let _msgtype = forward_message.get_message_name().to_owned();
        let fwd =
            self.sign_relay_message(local_peer, burnchain_view, relay_hints, forward_message)?;
        let fwd_handle = self.relay_signed_message(fwd).map_err(|e| {
            debug!("Unable to forward a {}: {:?}", _msgtype, &e);
            e
        })?;

        self.stats.msgs_tx += 1;
        Ok(fwd_handle)
    }

    /// Reply a NACK
    fn reply_nack(
        &mut self,
        local_peer: &LocalPeer,
        burnchain_view: &BurnchainView,
        preamble: &Preamble,
        nack_code: u32,
    ) -> Result<ReplyHandleP2P, net_error> {
        let nack_payload = StacksMessageType::Nack(NackData::new(nack_code));
        self.sign_and_reply(local_peer, burnchain_view, preamble, nack_payload)
    }

    /// Queue up this message to this peer, and update our stats.
    /// This is a non-blocking operation. The caller needs to call .try_flush() or .flush() on the
    /// returned Write to finish sending.
    pub fn relay_signed_message(
        &mut self,
        msg: StacksMessage,
    ) -> Result<ReplyHandleP2P, net_error> {
        let _name = msg.payload.get_message_description();
        let _seq = msg.request_id();

        let mut handle = self.connection.make_relay_handle(self.conn_id)?;
        msg.consensus_serialize(&mut handle)?;

        self.stats.msgs_tx += 1;

        debug!(
            "{:?}: relay-send({}) {} seq {}",
            &self, self.stats.msgs_tx, _name, _seq
        );
        Ok(handle)
    }

    /// Queue up this message to this peer, and update our stats.  Expect a reply.
    /// This is a non-blocking operation.  The caller needs to call .try_flush() or .flush() on the
    /// returned handle to finish sending.
    pub fn send_signed_request(
        &mut self,
        msg: StacksMessage,
        ttl: u64,
    ) -> Result<ReplyHandleP2P, net_error> {
        let _name = msg.get_message_name();
        let _seq = msg.request_id();

        let mut handle =
            self.connection
                .make_request_handle(msg.request_id(), ttl, self.conn_id)?;
        msg.consensus_serialize(&mut handle)?;

        self.stats.msgs_tx += 1;

        debug!(
            "{:?}: request-send({}) {} seq {}",
            &self, self.stats.msgs_tx, _name, _seq
        );
        Ok(handle)
    }

    /// Validate a handshake request.
    /// Return Err(...) if the handshake request was invalid.
    fn validate_handshake(
        &mut self,
        local_peer: &LocalPeer,
        chain_view: &BurnchainView,
        message: &mut StacksMessage,
    ) -> Result<(), net_error> {
        let handshake_data = match message.payload {
            StacksMessageType::Handshake(ref mut data) => data.clone(),
            _ => panic!("Message is not a handshake"),
        };

        match self.connection.get_public_key() {
            None => {
                // if we don't yet have a public key for this node, verify the message.
                // if it's improperly signed, it's probably a poorly-timed re-key request (but either way the message should be rejected)
                message
                    .verify_secp256k1(&handshake_data.node_public_key)
                    .map_err(|_e| {
                        debug!(
                            "{:?}: invalid handshake: not signed with given public key",
                            &self
                        );
                        net_error::InvalidMessage
                    })?;
            }
            Some(_) => {
                // for outbound connections, the self-reported address must match socket address if we already have a public key.
                // (not the case for inbound connections, since the peer socket address we see may
                // not be the same as the address the remote peer thinks it has).
                // The only exception to this is if the remote peer does not yet know its own
                // public IP address, in which case, its handshake addrbytes will be the
                // any-network bind address (0.0.0.0 or ::)
                if self.stats.outbound
                    && (!handshake_data.addrbytes.is_anynet()
                        && (self.peer_addrbytes != handshake_data.addrbytes
                            || self.peer_port != handshake_data.port))
                {
                    // wrong peer address
                    debug!(
                        "{:?}: invalid handshake -- wrong addr/port ({:?}:{:?})",
                        &self, &handshake_data.addrbytes, handshake_data.port
                    );
                    return Err(net_error::InvalidHandshake);
                }
            }
        };

        let their_public_key_res = handshake_data.node_public_key.to_public_key();
        match their_public_key_res {
            Ok(_) => {}
            Err(_e) => {
                // bad public key
                debug!("{:?}: invalid handshake -- invalid public key", &self);
                return Err(net_error::InvalidMessage);
            }
        };

        if handshake_data.expire_block_height <= chain_view.burn_block_height {
            // already stale
            debug!(
                "{:?}: invalid handshake -- stale public key (expired at {})",
                &self, handshake_data.expire_block_height
            );
            return Err(net_error::InvalidHandshake);
        }

        // the handshake cannot come from us
        if handshake_data.node_public_key
            == StacksPublicKeyBuffer::from_public_key(&Secp256k1PublicKey::from_private(
                &local_peer.private_key,
            ))
        {
            debug!(
                "{:?}: invalid handshake -- got a handshake from myself",
                &self
            );
            return Err(net_error::InvalidHandshake);
        }

        Ok(())
    }

    /// Update connection state from handshake data.
    /// Returns true if we learned a new public key; false if not
    pub fn update_from_handshake_data(
        &mut self,
        preamble: &Preamble,
        handshake_data: &HandshakeData,
    ) -> Result<bool, net_error> {
        let pubk = handshake_data.node_public_key.to_public_key()?;

        self.peer_version = preamble.peer_version;
        self.peer_network_id = preamble.network_id;
        self.peer_services = handshake_data.services;
        self.peer_expire_block_height = handshake_data.expire_block_height;
        self.handshake_addrbytes = handshake_data.addrbytes.clone();
        self.handshake_port = handshake_data.port;
        self.data_url = handshake_data.data_url.clone();

        let mut updated = false;
        let cur_pubk_opt = self.connection.get_public_key();
        if let Some(cur_pubk) = cur_pubk_opt {
            if pubk != cur_pubk {
                debug!(
                    "{:?}: Upgrade key {:?} to {:?} expires {:?}",
                    &self,
                    &to_hex(&cur_pubk.to_bytes_compressed()),
                    &to_hex(&pubk.to_bytes_compressed()),
                    self.peer_expire_block_height
                );
                updated = true;
            }
        }

        self.connection.set_public_key(Some(pubk.clone()));

        Ok(updated)
    }

    /// Handle an inbound NAT-punch request -- just tell the peer what we think their IP/port are.
    /// No authentication from the peer is necessary.
    fn handle_natpunch_request(&self, chain_view: &BurnchainView, nonce: u32) -> StacksMessage {
        // monitoring::increment_p2p_msg_nat_punch_request_received_counter();
        monitoring::increment_msg_counter("p2p_nat_punch_request".to_string());

        let natpunch_data = NatPunchData {
            addrbytes: self.peer_addrbytes.clone(),
            port: self.peer_port,
            nonce: nonce,
        };
        let msg = StacksMessage::from_chain_view(
            self.version,
            self.network_id,
            chain_view,
            StacksMessageType::NatPunchReply(natpunch_data),
        );
        msg
    }

    /// Handle an inbound handshake request, and generate either a HandshakeAccept or a HandshakeReject
    /// payload to send back.
    /// A handshake will only be accepted if we do not yet know the public key of this remote peer,
    /// or if it is signed by the current public key.
    /// Returns a reply (either an accept or reject) if appropriate
    /// Panics if this message is not a handshake (caller should check)
    fn handle_handshake(
        &mut self,
        local_peer: &LocalPeer,
        peerdb: &mut PeerDB,
        chain_view: &BurnchainView,
        message: &mut StacksMessage,
        authenticated: bool,
    ) -> Result<(Option<StacksMessage>, bool), net_error> {
        if !authenticated && self.connection.options.disable_inbound_handshakes {
            debug!("{:?}: blocking inbound unauthenticated handshake", &self);
            return Ok((None, true));
        }

        let res = self.validate_handshake(local_peer, chain_view, message);
        match res {
            Ok(_) => {}
            Err(net_error::InvalidHandshake) => {
                let reject = StacksMessage::from_chain_view(
                    self.version,
                    self.network_id,
                    chain_view,
                    StacksMessageType::HandshakeReject,
                );
                debug!("{:?}: invalid handshake", &self);
                return Ok((Some(reject), true));
            }
            Err(e) => {
                return Err(e);
            }
        };

        let handshake_data = match message.payload {
            StacksMessageType::Handshake(ref mut data) => data.clone(),
            _ => panic!("Message is not a handshake"),
        };

        let old_pubkey_opt = self.connection.get_public_key();
        let updated = self.update_from_handshake_data(&message.preamble, &handshake_data)?;
        let _authentic_msg = if !updated {
            "same"
        } else if old_pubkey_opt.is_none() {
            "new"
        } else {
            "upgraded"
        };

        debug!(
            "Handshake from {:?} {} public key {:?} expires at {:?}",
            &self,
            _authentic_msg,
            &to_hex(
                &handshake_data
                    .node_public_key
                    .to_public_key()
                    .unwrap()
                    .to_bytes_compressed()
            ),
            handshake_data.expire_block_height
        );

        if updated {
            // save the new key
            let mut tx = peerdb.tx_begin().map_err(net_error::DBError)?;
            let mut neighbor = Neighbor::from_handshake(
                &mut tx,
                message.preamble.peer_version,
                message.preamble.network_id,
                &handshake_data,
            )?;
            neighbor.save_update(&mut tx)?;
            tx.commit()
                .map_err(|e| net_error::DBError(db_error::SqliteError(e)))?;

            debug!(
                "{:?}: Re-key {:?} to {:?} expires {}",
                local_peer,
                &neighbor.addr,
                &to_hex(&neighbor.public_key.to_bytes_compressed()),
                neighbor.expire_block
            );
        }

        let accept_data = HandshakeAcceptData::new(local_peer, self.heartbeat);
        let accept = StacksMessage::from_chain_view(
            self.version,
            self.network_id,
            chain_view,
            StacksMessageType::HandshakeAccept(accept_data),
        );

        // update stats
        self.stats.last_contact_time = get_epoch_time_secs();
        self.peer_heartbeat = self.heartbeat; // use our own heartbeat to determine how often we expect this peer to ping us, since that's what we've told the peer

        // always pass back handshakes, even though we "handled" them (since other processes --
        // in particular, the neighbor-walk logic -- need to receive them)
        Ok((Some(accept), false))
    }

    /// Handle an inbound handshake-accept
    /// Update conversation state based on a HandshakeAccept
    /// Called from the p2p network thread.
    fn handle_handshake_accept(
        &mut self,
        preamble: &Preamble,
        handshake_accept: &HandshakeAcceptData,
    ) -> Result<(), net_error> {
        self.update_from_handshake_data(preamble, &handshake_accept.handshake)?;
        self.peer_heartbeat =
            if handshake_accept.heartbeat_interval > (MAX_PEER_HEARTBEAT_INTERVAL as u32) {
                debug!(
                    "{:?}: heartbeat interval is too long; forcing default maximum",
                    self
                );
                MAX_PEER_HEARTBEAT_INTERVAL as u32
            } else {
                handshake_accept.heartbeat_interval
            };

        self.stats.last_handshake_time = get_epoch_time_secs();

        debug!(
            "HandshakeAccept from {:?}: set public key to {:?} expiring at {:?} heartbeat {}s",
            &self,
            &to_hex(
                &handshake_accept
                    .handshake
                    .node_public_key
                    .to_public_key()
                    .unwrap()
                    .to_bytes_compressed()
            ),
            handshake_accept.handshake.expire_block_height,
            self.peer_heartbeat
        );
        Ok(())
    }

    /// Reply to a ping with a pong.
    /// Called from the p2p network thread.
    fn handle_ping(
        &mut self,
        chain_view: &BurnchainView,
        message: &mut StacksMessage,
    ) -> Result<Option<StacksMessage>, net_error> {
        // monitoring::increment_p2p_msg_ping_received_counter();
        monitoring::increment_msg_counter("p2p_ping".to_string());

        let ping_data = match message.payload {
            StacksMessageType::Ping(ref data) => data,
            _ => panic!("Message is not a ping"),
        };
        let pong_data = PongData::from_ping(&ping_data);
        Ok(Some(StacksMessage::from_chain_view(
            self.version,
            self.network_id,
            chain_view,
            StacksMessageType::Pong(pong_data),
        )))
    }

    /// Handle an inbound GetNeighbors request.
    fn handle_getneighbors(
        &mut self,
        peer_dbconn: &DBConn,
        local_peer: &LocalPeer,
        chain_view: &BurnchainView,
        preamble: &Preamble,
    ) -> Result<ReplyHandleP2P, net_error> {
        // monitoring::increment_p2p_msg_get_neighbors_received_counter();
        monitoring::increment_msg_counter("p2p_get_neighbors".to_string());

        // get neighbors at random as long as they're fresh
        let mut neighbors = PeerDB::get_random_neighbors(
            peer_dbconn,
            self.network_id,
            MAX_NEIGHBORS_DATA_LEN,
            chain_view.burn_block_height,
            false,
        )
        .map_err(net_error::DBError)?;

        if cfg!(test) && self.connection.options.disable_chat_neighbors {
            // never report neighbors if this is disabled by a test
            test_debug!(
                "{:?}: Neighbor crawl is disabled; reporting 0 neighbors",
                &local_peer
            );
            neighbors.clear();
        }

        let neighbor_addrs: Vec<NeighborAddress> = neighbors
            .iter()
            .map(|n| NeighborAddress::from_neighbor(n))
            .collect();

        debug!(
            "{:?}: handle GetNeighbors from {:?}. Reply with {} neighbors",
            &local_peer,
            &self,
            neighbor_addrs.len()
        );

        let payload = StacksMessageType::Neighbors(NeighborsData {
            neighbors: neighbor_addrs,
        });
        let reply = self.sign_reply(chain_view, &local_peer.private_key, payload, preamble.seq)?;
        let reply_handle = self.relay_signed_message(reply).map_err(|e| {
            debug!(
                "Outbox to {:?} is full; cannot reply to GetNeighbors",
                &self
            );
            e
        })?;

        Ok(reply_handle)
    }

    /// Handle an inbound GetBlocksInv request.
    /// Returns a reply handle to the generated message (possibly a nack)
    /// Only returns up to $reward_cycle_length bits
    pub fn make_getblocksinv_response(
        _local_peer: &LocalPeer,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
        header_cache: &mut BlockHeaderCache,
        get_blocks_inv: &GetBlocksInv,
    ) -> Result<StacksMessageType, net_error> {
        // must not ask for more than a reasonable number of blocks
        if get_blocks_inv.num_blocks == 0
            || get_blocks_inv.num_blocks as u32 > burnchain.pox_constants.reward_cycle_length
        {
            return Ok(StacksMessageType::Nack(NackData::new(
                NackErrorCodes::InvalidMessage,
            )));
        }

        // request must correspond to valid PoX fork and must be aligned to reward cycle
        let base_snapshot = match SortitionDB::get_block_snapshot_consensus(
            sortdb.conn(),
            &get_blocks_inv.consensus_hash,
        )? {
            Some(sn) => sn,
            None => {
                debug!(
                    "{:?}: No such block snapshot for {}",
                    &_local_peer, &get_blocks_inv.consensus_hash
                );
                return Ok(StacksMessageType::Nack(NackData::new(
                    NackErrorCodes::NoSuchBurnchainBlock,
                )));
            }
        };

        // must be on the main PoX fork
        if !base_snapshot.pox_valid {
            debug!(
                "{:?}: Snapshot for {:?} is not on the valid PoX fork",
                _local_peer, base_snapshot.consensus_hash
            );
            return Ok(StacksMessageType::Nack(NackData::new(
                NackErrorCodes::InvalidPoxFork,
            )));
        }

        // must be aligned to the start of a reward cycle
        // (note that the first reward cycle bit doesn't count)
        if base_snapshot.block_height > burnchain.first_block_height + 1
            && !burnchain.is_reward_cycle_start(base_snapshot.block_height)
        {
            warn!(
                "{:?}: Snapshot for {:?} is at height {}, which is not aligned to a reward cycle",
                _local_peer, base_snapshot.consensus_hash, base_snapshot.block_height
            );
            return Ok(StacksMessageType::Nack(NackData::new(
                NackErrorCodes::InvalidPoxFork,
            )));
        }

        // find the tail end of this range on the canonical fork.
        let tip_snapshot = {
            let tip_sort_id = SortitionDB::get_canonical_sortition_tip(sortdb.conn())?;
            let ic = sortdb.index_conn();
            // NOTE: need the '- 1' here because get_stacks_header_hashes includes
            // tip_snapshot.consensus_hash at the end.
            match SortitionDB::get_ancestor_snapshot(
                &ic,
                base_snapshot.block_height + (get_blocks_inv.num_blocks as u64) - 1,
                &tip_sort_id,
            )? {
                Some(sn) => sn,
                None => {
                    debug!(
                        "{:?}: No block known for base {} + num_blocks {} = {} block height",
                        _local_peer,
                        base_snapshot.block_height,
                        get_blocks_inv.num_blocks,
                        base_snapshot.block_height + (get_blocks_inv.num_blocks as u64)
                    );
                    return Ok(StacksMessageType::Nack(NackData::new(
                        NackErrorCodes::NoSuchBurnchainBlock,
                    )));
                }
            }
        };

        let block_hashes = {
            let num_headers = cmp::min(
                burnchain.pox_constants.reward_cycle_length as u64,
                get_blocks_inv.num_blocks as u64,
            );

            let ic = sortdb.index_conn();
            let res = ic.get_stacks_header_hashes(
                num_headers,
                &tip_snapshot.consensus_hash,
                header_cache,
            );
            match res {
                Ok(hashes) => Ok(hashes),
                Err(db_error::NotFoundError) | Err(db_error::InvalidPoxSortition) => {
                    debug!(
                        "{:?}: Failed to load ancestor hashes from {}",
                        &_local_peer, &tip_snapshot.consensus_hash
                    );

                    // make this into a NACK
                    return Ok(StacksMessageType::Nack(NackData::new(
                        NackErrorCodes::NoSuchBurnchainBlock,
                    )));
                }
                Err(e) => Err(net_error::DBError(e)),
            }
        }?;

        // update cache
        SortitionDB::merge_block_header_cache(header_cache, &block_hashes);

        let blocks_inv_data: BlocksInvData = chainstate
            .get_blocks_inventory(&block_hashes)
            .map_err(|e| net_error::from(e))?;

        Ok(StacksMessageType::BlocksInv(blocks_inv_data))
    }

    /// Handle an inbound GetBlocksInv request.
    /// Returns a reply handle to the generated message (possibly a nack)
    fn handle_getblocksinv(
        &mut self,
        local_peer: &LocalPeer,
        sortdb: &SortitionDB,
        chainstate: &mut StacksChainState,
        header_cache: &mut BlockHeaderCache,
        burnchain_view: &BurnchainView,
        preamble: &Preamble,
        get_blocks_inv: &GetBlocksInv,
    ) -> Result<ReplyHandleP2P, net_error> {
        // monitoring::increment_p2p_msg_get_blocks_inv_received_counter();
        monitoring::increment_msg_counter("p2p_get_blocks_inv".to_string());

        let mut response = ConversationP2P::make_getblocksinv_response(
            local_peer,
            &self.burnchain,
            sortdb,
            chainstate,
            header_cache,
            get_blocks_inv,
        )?;

        if let StacksMessageType::BlocksInv(ref mut blocks_inv_data) = &mut response {
            debug!(
                "{:?}: Handled GetBlocksInv. Reply {:?} to request {:?}",
                &local_peer, &blocks_inv_data, get_blocks_inv
            );

            if self.connection.options.disable_inv_chat {
                // never reply that we have blocks
                test_debug!(
                    "{:?}: Disable inv chat -- pretend like we have nothing",
                    local_peer
                );
                for i in 0..blocks_inv_data.block_bitvec.len() {
                    blocks_inv_data.block_bitvec[i] = 0;
                }
                for i in 0..blocks_inv_data.microblocks_bitvec.len() {
                    blocks_inv_data.microblocks_bitvec[i] = 0;
                }
            }
        }

        self.sign_and_reply(local_peer, burnchain_view, preamble, response)
    }

    /// Create a response an inbound GetPoxInv request, but unsigned.
    /// Returns a reply handle to the generated message (possibly a nack)
    pub fn make_getpoxinv_response(
        local_peer: &LocalPeer,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        pox_id: &PoxId,
        getpoxinv: &GetPoxInv,
    ) -> Result<StacksMessageType, net_error> {
        if pox_id.len() <= 1 {
            // not initialized yet
            debug!("{:?}: PoX not initialized yet", local_peer);
            return Ok(StacksMessageType::Nack(NackData::new(
                NackErrorCodes::InvalidPoxFork,
            )));
        }
        // consensus hash in getpoxinv must exist on the canonical chain tip
        match SortitionDB::get_block_snapshot_consensus(sortdb.conn(), &getpoxinv.consensus_hash) {
            Ok(Some(sn)) => {
                if !sn.pox_valid {
                    // invalid consensus hash
                    test_debug!(
                        "{:?}: Snapshot {:?} is not on a valid PoX fork",
                        local_peer,
                        sn.burn_header_hash
                    );
                    return Ok(StacksMessageType::Nack(NackData::new(
                        NackErrorCodes::InvalidPoxFork,
                    )));
                }

                // must align to reward cycle, or this is an invalid fork
                if (sn.block_height - burnchain.first_block_height)
                    % (burnchain.pox_constants.reward_cycle_length as u64)
                    != 1
                {
                    test_debug!(
                        "{:?}: block height ({} - {}) % {} != 1",
                        local_peer,
                        sn.block_height,
                        burnchain.first_block_height,
                        burnchain.pox_constants.reward_cycle_length
                    );
                    return Ok(StacksMessageType::Nack(NackData::new(
                        NackErrorCodes::InvalidPoxFork,
                    )));
                }

                match burnchain.block_height_to_reward_cycle(sn.block_height) {
                    Some(reward_cycle) => {
                        // take a slice of the PoxId
                        let (bitvec, bitlen) =
                            pox_id.bit_slice(reward_cycle as usize, getpoxinv.num_cycles as usize);
                        assert!(bitlen <= GETPOXINV_MAX_BITLEN);

                        let poxinvdata = PoxInvData {
                            pox_bitvec: bitvec,
                            bitlen: bitlen as u16,
                        };
                        debug!(
                            "{:?}: Handle GetPoxInv at reward cycle {}; Reply {:?} to request {:?}",
                            &local_peer, reward_cycle, &poxinvdata, getpoxinv
                        );
                        Ok(StacksMessageType::PoxInv(poxinvdata))
                    }
                    None => {
                        // if we can't turn the block height into a reward cycle, then it's before
                        // the first-ever reward cycle and this consensus hash does not correspond
                        // to a real reward cycle.  NACK it.
                        debug!(
                            "{:?}: Consensus hash {:?} does not correspond to a real reward cycle",
                            &local_peer, &getpoxinv.consensus_hash
                        );
                        Ok(StacksMessageType::Nack(NackData::new(
                            NackErrorCodes::InvalidPoxFork,
                        )))
                    }
                }
            }
            Ok(None) | Err(db_error::NotFoundError) => {
                test_debug!(
                    "{:?}: snapshot for consensus hash {} not found",
                    local_peer,
                    getpoxinv.consensus_hash
                );
                Ok(StacksMessageType::Nack(NackData::new(
                    NackErrorCodes::InvalidPoxFork,
                )))
            }
            Err(e) => Err(net_error::DBError(e)),
        }
    }

    /// Handle an inbound GetPoxInv request.
    /// Returns a reply handle to the generated message (possibly a nack)
    fn handle_getpoxinv(
        &mut self,
        local_peer: &LocalPeer,
        sortdb: &SortitionDB,
        pox_id: &PoxId,
        burnchain_view: &BurnchainView,
        preamble: &Preamble,
        getpoxinv: &GetPoxInv,
    ) -> Result<ReplyHandleP2P, net_error> {
        let response = ConversationP2P::make_getpoxinv_response(
            local_peer,
            &self.burnchain,
            sortdb,
            pox_id,
            getpoxinv,
        )?;
        self.sign_and_reply(local_peer, burnchain_view, preamble, response)
    }

    /// Verify that there are no cycles in our relayers list.
    /// Identify relayers by public key hash
    fn check_relayer_cycles(relayers: &Vec<RelayData>) -> bool {
        let mut addrs = HashSet::new();
        for r in relayers.iter() {
            if addrs.contains(&r.peer.public_key_hash) {
                return false;
            }
            addrs.insert(r.peer.public_key_hash.clone());
        }
        true
    }

    /// Verify that we aren't in this relayers list
    fn check_relayers_remote(local_peer: &LocalPeer, relayers: &Vec<RelayData>) -> bool {
        let addr = local_peer.to_neighbor_addr();
        for r in relayers.iter() {
            if r.peer.public_key_hash == addr.public_key_hash {
                return false;
            }
        }
        return true;
    }

    /// Check that a message was properly relayed.
    /// * there are no relay cycles
    /// * we didn't send this
    /// Update relayer statistics for this conversation
    fn process_relayers(
        &mut self,
        local_peer: &LocalPeer,
        preamble: &Preamble,
        relayers: &Vec<RelayData>,
    ) -> bool {
        if !ConversationP2P::check_relayer_cycles(relayers) {
            debug!(
                "Invalid relayers -- message from {:?} contains a cycle",
                self.to_neighbor_key()
            );
            return false;
        }

        if !ConversationP2P::check_relayers_remote(local_peer, relayers) {
            debug!(
                "Invalid relayers -- message originates from us ({})",
                local_peer.to_neighbor_addr()
            );
            return false;
        }

        for relayer in relayers.iter() {
            self.stats
                .add_relayer(&relayer.peer, (preamble.payload_len - 1) as u64);
        }

        return true;
    }

    /// Validate pushed blocks.
    /// Make sure the peer doesn't send us too much at once, though.
    fn validate_blocks_push(
        &mut self,
        local_peer: &LocalPeer,
        chain_view: &BurnchainView,
        preamble: &Preamble,
        relayers: Vec<RelayData>,
    ) -> Result<Option<ReplyHandleP2P>, net_error> {
        assert!(preamble.payload_len > 5); // don't count 1-byte type prefix + 4 byte vector length

        if !self.process_relayers(local_peer, preamble, &relayers) {
            debug!("Drop pushed blocks -- invalid relayers {:?}", &relayers);
            self.stats.msgs_err += 1;
            return Err(net_error::InvalidMessage);
        }

        self.stats.add_block_push((preamble.payload_len as u64) - 5);

        if self.connection.options.max_block_push_bandwidth > 0
            && self.stats.get_block_push_bandwidth()
                > (self.connection.options.max_block_push_bandwidth as f64)
        {
            debug!(
                "Neighbor {:?} exceeded max block-push bandwidth of {} bytes/sec (currently at {})",
                &self.to_neighbor_key(),
                self.connection.options.max_block_push_bandwidth,
                self.stats.get_block_push_bandwidth()
            );
            return self
                .reply_nack(local_peer, chain_view, preamble, NackErrorCodes::Throttled)
                .and_then(|handle| Ok(Some(handle)));
        }
        Ok(None)
    }

    /// Validate pushed microblocks.
    /// Not much we can do to see if they're semantically correct, but we can at least throttle a
    /// peer that sends us too many at once.
    fn validate_microblocks_push(
        &mut self,
        local_peer: &LocalPeer,
        chain_view: &BurnchainView,
        preamble: &Preamble,
        relayers: Vec<RelayData>,
    ) -> Result<Option<ReplyHandleP2P>, net_error> {
        assert!(preamble.payload_len > 5); // don't count 1-byte type prefix + 4 byte vector length

        if !self.process_relayers(local_peer, preamble, &relayers) {
            debug!(
                "Drop pushed microblocks -- invalid relayers {:?}",
                &relayers
            );
            self.stats.msgs_err += 1;
            return Err(net_error::InvalidMessage);
        }

        self.stats
            .add_microblocks_push((preamble.payload_len as u64) - 5);

        if self.connection.options.max_microblocks_push_bandwidth > 0
            && self.stats.get_microblocks_push_bandwidth()
                > (self.connection.options.max_microblocks_push_bandwidth as f64)
        {
            debug!("Neighbor {:?} exceeded max microblocks-push bandwidth of {} bytes/sec (currently at {})", &self.to_neighbor_key(), self.connection.options.max_microblocks_push_bandwidth, self.stats.get_microblocks_push_bandwidth());
            return self
                .reply_nack(local_peer, chain_view, preamble, NackErrorCodes::Throttled)
                .and_then(|handle| Ok(Some(handle)));
        }
        Ok(None)
    }

    /// Validate a pushed transaction.
    /// Update bandwidth accounting, but forward the transaction along.
    fn validate_transaction_push(
        &mut self,
        local_peer: &LocalPeer,
        chain_view: &BurnchainView,
        preamble: &Preamble,
        relayers: Vec<RelayData>,
    ) -> Result<Option<ReplyHandleP2P>, net_error> {
        assert!(preamble.payload_len > 1); // don't count 1-byte type prefix

        if !self.process_relayers(local_peer, preamble, &relayers) {
            debug!(
                "Drop pushed transaction -- invalid relayers {:?}",
                &relayers
            );
            self.stats.msgs_err += 1;
            return Err(net_error::InvalidMessage);
        }

        self.stats
            .add_transaction_push((preamble.payload_len as u64) - 1);

        if self.connection.options.max_transaction_push_bandwidth > 0
            && self.stats.get_transaction_push_bandwidth()
                > (self.connection.options.max_transaction_push_bandwidth as f64)
        {
            debug!("Neighbor {:?} exceeded max transaction-push bandwidth of {} bytes/sec (currently at {})", &self.to_neighbor_key(), self.connection.options.max_transaction_push_bandwidth, self.stats.get_transaction_push_bandwidth());
            return self
                .reply_nack(local_peer, chain_view, preamble, NackErrorCodes::Throttled)
                .and_then(|handle| Ok(Some(handle)));
        }
        Ok(None)
    }

    /// Handle an inbound authenticated p2p data-plane message.
    /// Return the message if not handled
    fn handle_data_message(
        &mut self,
        local_peer: &LocalPeer,
        peerdb: &mut PeerDB,
        sortdb: &SortitionDB,
        pox_id: &PoxId,
        chainstate: &mut StacksChainState,
        header_cache: &mut BlockHeaderCache,
        chain_view: &BurnchainView,
        msg: StacksMessage,
    ) -> Result<Option<StacksMessage>, net_error> {
        let res = match msg.payload {
            StacksMessageType::GetNeighbors => {
                self.handle_getneighbors(peerdb.conn(), local_peer, chain_view, &msg.preamble)
            }
            StacksMessageType::GetPoxInv(ref getpoxinv) => self.handle_getpoxinv(
                local_peer,
                sortdb,
                pox_id,
                chain_view,
                &msg.preamble,
                getpoxinv,
            ),
            StacksMessageType::GetBlocksInv(ref get_blocks_inv) => self.handle_getblocksinv(
                local_peer,
                sortdb,
                chainstate,
                header_cache,
                chain_view,
                &msg.preamble,
                get_blocks_inv,
            ),
            StacksMessageType::Blocks(_) => {
                monitoring::increment_stx_blocks_received_counter();

                // not handled here, but do some accounting -- we can't receive blocks too often,
                // so close this conversation if we do.
                match self.validate_blocks_push(
                    local_peer,
                    chain_view,
                    &msg.preamble,
                    msg.relayers.clone(),
                )? {
                    Some(handle) => Ok(handle),
                    None => {
                        // will forward upstream
                        return Ok(Some(msg));
                    }
                }
            }
            StacksMessageType::Microblocks(_) => {
                monitoring::increment_stx_micro_blocks_received_counter();

                // not handled here, but do some accounting -- we can't receive too many
                // unconfirmed microblocks per second
                match self.validate_microblocks_push(
                    local_peer,
                    chain_view,
                    &msg.preamble,
                    msg.relayers.clone(),
                )? {
                    Some(handle) => Ok(handle),
                    None => {
                        // will forward upstream
                        return Ok(Some(msg));
                    }
                }
            }
            StacksMessageType::Transaction(_) => {
                monitoring::increment_txs_received_counter();

                // not handled here, but do some accounting -- we can't receive too many
                // unconfirmed transactions per second
                match self.validate_transaction_push(
                    local_peer,
                    chain_view,
                    &msg.preamble,
                    msg.relayers.clone(),
                )? {
                    Some(handle) => Ok(handle),
                    None => {
                        // will forward upstream
                        return Ok(Some(msg));
                    }
                }
            }
            _ => {
                // all else will forward upstream
                return Ok(Some(msg));
            }
        };

        match res {
            Ok(handle) => {
                self.reply_handles.push_back(handle);
                Ok(None)
            }
            Err(e) => {
                debug!("Failed to handle messsage: {:?}", &e);
                Ok(Some(msg))
            }
        }
    }

    /// Load data into our connection
    pub fn recv<R: Read>(&mut self, r: &mut R) -> Result<usize, net_error> {
        let mut total_recved = 0;
        loop {
            let res = self.connection.recv_data(r);
            match res {
                Ok(num_recved) => {
                    total_recved += num_recved;
                    if num_recved > 0 {
                        self.stats.last_recv_time = get_epoch_time_secs();
                        self.stats.bytes_rx += num_recved as u64;
                    } else {
                        break;
                    }
                }
                Err(net_error::PermanentlyDrained) => {
                    trace!(
                        "{:?}: failed to recv on P2P conversation: PermanentlyDrained",
                        self
                    );
                    return Err(net_error::PermanentlyDrained);
                }
                Err(e) => {
                    info!("{:?}: failed to recv on P2P conversation: {:?}", self, &e);
                    return Err(e);
                }
            }
        }
        test_debug!("{:?}: received {} bytes", self, total_recved);
        Ok(total_recved)
    }

    /// Write data out of our conversation
    pub fn send<W: Write>(&mut self, w: &mut W) -> Result<usize, net_error> {
        let mut total_sent = 0;
        loop {
            // queue next byte slice
            self.try_flush()?;

            let res = self.connection.send_data(w);
            match res {
                Ok(num_sent) => {
                    total_sent += num_sent;
                    if num_sent > 0 {
                        self.stats.last_send_time = get_epoch_time_secs();
                        self.stats.bytes_tx += num_sent as u64;
                    } else {
                        break;
                    }
                }
                Err(e) => {
                    info!("{:?}: failed to send on P2P conversation: {:?}", self, &e);
                    return Err(e);
                }
            }
        }
        test_debug!("{:?}: sent {} bytes", self, total_sent);
        Ok(total_sent)
    }

    /// Make progress on in-flight messages.
    pub fn try_flush(&mut self) -> Result<(), net_error> {
        // send out responses in the order they were requested
        let mut drained = false;
        let mut broken = false;
        match self.reply_handles.front_mut() {
            Some(ref mut reply) => {
                // try moving some data to the connection
                match reply.try_flush() {
                    Ok(res) => {
                        drained = res;
                    }
                    Err(e) => {
                        // dead
                        warn!("Broken P2P connection: {:?}", &e);
                        broken = true;
                    }
                }
            }
            None => {}
        }

        if broken || drained {
            // done with this stream
            self.reply_handles.pop_front();
        }
        Ok(())
    }

    /// How many pending outgoing messages are there
    pub fn num_pending_outbound(&self) -> usize {
        self.reply_handles.len()
    }

    /// Validate an inbound p2p message
    /// Return Ok(true) if valid, Ok(false) if invalid, and Err if we should disconnect.
    fn validate_inbound_message(
        &mut self,
        msg: &StacksMessage,
        burnchain_view: &BurnchainView,
    ) -> Result<bool, net_error> {
        // validate message preamble
        match self.is_preamble_valid(&msg, burnchain_view) {
            Ok(res) => {
                if !res {
                    info!(
                        "{:?}: Received message with stale preamble; ignoring",
                        &self
                    );
                    self.stats.msgs_err += 1;
                    self.stats.add_healthpoint(false);
                    return Ok(false);
                }
            }
            Err(e) => {
                match e {
                    net_error::InvalidMessage => {
                        // Disconnect from this peer.  If it thinks nothing's wrong, it'll
                        // reconnect on its own.
                        // However, only count this message as error.  Drop all other queued
                        // messages.
                        info!(
                            "{:?}: Received invalid preamble; dropping connection",
                            &self
                        );
                        self.stats.msgs_err += 1;
                        self.stats.add_healthpoint(false);
                        return Err(e);
                    }
                    _ => {
                        // skip this message
                        info!("{:?}: Failed to process message: {:?}", &self, &e);
                        self.stats.msgs_err += 1;
                        self.stats.add_healthpoint(false);
                        return Ok(false);
                    }
                }
            }
        }
        return Ok(true);
    }

    /// Handle an inbound authenticated p2p control-plane message
    /// Return true if we should consume it (i.e. it's not something to forward along), as well as the message we'll send as a reply (if any)
    fn handle_authenticated_control_message(
        &mut self,
        local_peer: &LocalPeer,
        peerdb: &mut PeerDB,
        burnchain_view: &BurnchainView,
        msg: &mut StacksMessage,
    ) -> Result<(Option<StacksMessage>, bool), net_error> {
        let mut consume = false;

        // already have public key; match payload
        let reply_opt = match msg.payload {
            StacksMessageType::Handshake(_) => {
                // monitoring::increment_p2p_msg_authenticated_handshake_received_counter();
                monitoring::increment_msg_counter("p2p_authenticated_handshake".to_string());

                debug!("{:?}: Got Handshake", &self);
                let (handshake_opt, handled) =
                    self.handle_handshake(local_peer, peerdb, burnchain_view, msg, true)?;
                consume = handled;
                Ok(handshake_opt)
            }
            StacksMessageType::HandshakeAccept(ref data) => {
                test_debug!("{:?}: Got HandshakeAccept", &self);
                self.handle_handshake_accept(&msg.preamble, data)
                    .and_then(|_| Ok(None))
            }
            StacksMessageType::Ping(_) => {
                test_debug!("{:?}: Got Ping", &self);

                // consume here if unsolicited
                consume = true;
                self.handle_ping(burnchain_view, msg)
            }
            StacksMessageType::Pong(_) => {
                test_debug!("{:?}: Got Pong", &self);
                Ok(None)
            }
            StacksMessageType::NatPunchRequest(ref nonce) => {
                if cfg!(test) && self.connection.options.disable_natpunch {
                    return Err(net_error::InvalidMessage);
                }
                test_debug!("{:?}: Got NatPunchRequest({})", &self, nonce);

                consume = true;
                let msg = self.handle_natpunch_request(burnchain_view, *nonce);
                Ok(Some(msg))
            }
            StacksMessageType::NatPunchReply(ref _m) => {
                if cfg!(test) && self.connection.options.disable_natpunch {
                    return Err(net_error::InvalidMessage);
                }
                test_debug!("{:?}: Got NatPunchReply({})", &self, _m.nonce);
                Ok(None)
            }
            _ => {
                test_debug!(
                    "{:?}: Got a data-plane message (type {})",
                    &self,
                    msg.payload.get_message_name()
                );
                Ok(None) // nothing to reply to at this time
            }
        }?;
        Ok((reply_opt, consume))
    }

    /// Handle an inbound unauthenticated p2p control-plane message.
    /// Return true if the message was also solicited, as well as the reply we generate to
    /// deal with it (if we do deal with it)
    fn handle_unauthenticated_control_message(
        &mut self,
        local_peer: &LocalPeer,
        peerdb: &mut PeerDB,
        burnchain_view: &BurnchainView,
        msg: &mut StacksMessage,
    ) -> Result<(Option<StacksMessage>, bool), net_error> {
        // only thing we'll take right now is a handshake, as well as handshake
        // accept/rejects, nacks, and NAT holepunches
        //
        // Anything else will be nack'ed -- the peer will first need to handshake.
        let mut consume = false;
        let solicited = self.connection.is_solicited(&msg);
        let reply_opt = match msg.payload {
            StacksMessageType::Handshake(_) => {
                // monitoring::increment_p2p_msg_unauthenticated_handshake_received_counter();
                monitoring::increment_msg_counter("p2p_unauthenticated_handshake".to_string());
                test_debug!("{:?}: Got unauthenticated Handshake", &self);
                let (reply_opt, handled) =
                    self.handle_handshake(local_peer, peerdb, burnchain_view, msg, false)?;
                consume = handled;
                Ok(reply_opt)
            }
            StacksMessageType::HandshakeAccept(ref data) => {
                if solicited {
                    test_debug!("{:?}: Got unauthenticated HandshakeAccept", &self);
                    self.handle_handshake_accept(&msg.preamble, data)
                        .and_then(|_| Ok(None))
                } else {
                    test_debug!("{:?}: Unsolicited unauthenticated HandshakeAccept", &self);

                    // don't update stats or state, and don't pass back
                    consume = true;
                    Ok(None)
                }
            }
            StacksMessageType::HandshakeReject => {
                test_debug!("{:?}: Got unauthenticated HandshakeReject", &self);

                // don't NACK this back just because we were rejected.
                // But, it's okay to forward this back (i.e. don't consume).
                Ok(None)
            }
            StacksMessageType::Nack(_) => {
                test_debug!("{:?}: Got unauthenticated Nack", &self);

                // don't NACK back.
                // But, it's okay to forward this back (i.e. don't consume).
                Ok(None)
            }
            StacksMessageType::NatPunchRequest(ref nonce) => {
                if cfg!(test) && self.connection.options.disable_natpunch {
                    return Err(net_error::InvalidMessage);
                }
                test_debug!(
                    "{:?}: Got unauthenticated NatPunchRequest({})",
                    &self,
                    *nonce
                );
                consume = true;
                let msg = self.handle_natpunch_request(burnchain_view, *nonce);
                Ok(Some(msg))
            }
            StacksMessageType::NatPunchReply(ref _m) => {
                if cfg!(test) && self.connection.options.disable_natpunch {
                    return Err(net_error::InvalidMessage);
                }
                test_debug!(
                    "{:?}: Got unauthenticated NatPunchReply({})",
                    &self,
                    _m.nonce
                );

                // it's okay to forward this back (i.e. don't consume)
                Ok(None)
            }
            _ => {
                test_debug!(
                    "{:?}: Got unauthenticated message (type {}), will NACK",
                    &self,
                    msg.payload.get_message_name()
                );
                let nack_payload =
                    StacksMessageType::Nack(NackData::new(NackErrorCodes::HandshakeRequired));
                let nack = StacksMessage::from_chain_view(
                    self.version,
                    self.network_id,
                    burnchain_view,
                    nack_payload,
                );

                // monitoring::increment_p2p_msg_nack_sent_counter();
                monitoring::increment_msg_counter("p2p_nack_sent".to_string());

                // unauthenticated, so don't forward it (but do consume it, and do nack it)
                consume = true;
                Ok(Some(nack))
            }
        }?;
        Ok((reply_opt, consume))
    }

    /// Carry on a conversation with the remote peer.
    /// Called from the p2p network thread, so no need for a network handle.
    /// Attempts to fulfill requests in other threads as a result of processing a message.
    /// Returns the list of unfulfilled Stacks messages we received -- messages not destined for
    /// any other thread in this program (i.e. "unsolicited messages").
    pub fn chat(
        &mut self,
        local_peer: &LocalPeer,
        peerdb: &mut PeerDB,
        sortdb: &SortitionDB,
        pox_id: &PoxId,
        chainstate: &mut StacksChainState,
        header_cache: &mut BlockHeaderCache,
        burnchain_view: &BurnchainView,
    ) -> Result<Vec<StacksMessage>, net_error> {
        let num_inbound = self.connection.inbox_len();
        test_debug!("{:?}: {} messages pending", &self, num_inbound);

        let mut unsolicited = vec![];
        for _ in 0..num_inbound {
            let update_stats; // whether or not this message can count towards this peer's liveness stats
            let mut msg = match self.connection.next_inbox_message() {
                None => {
                    continue;
                }
                Some(m) => m,
            };

            if !self.validate_inbound_message(&msg, burnchain_view)? {
                continue;
            }

            let (reply_opt, consumed) = if self.connection.has_public_key() {
                // we already have this remote peer's public key, so the message signature will
                // have been verified by the underlying ConnectionP2P.
                update_stats = true;
                self.handle_authenticated_control_message(
                    local_peer,
                    peerdb,
                    burnchain_view,
                    &mut msg,
                )?
            } else {
                // the underlying ConnectionP2P does not yet have a public key installed (i.e.
                // we don't know it yet), so treat this message with a little bit more
                // suspicion.
                // Update stats only if we were asking for this message.
                update_stats = self.connection.is_solicited(&msg);
                self.handle_unauthenticated_control_message(
                    local_peer,
                    peerdb,
                    burnchain_view,
                    &mut msg,
                )?
            };

            match reply_opt {
                None => {}
                Some(mut reply) => {
                    // send back this message to the remote peer
                    test_debug!(
                        "{:?}: Send control-plane reply type {}",
                        &self,
                        reply.payload.get_message_name()
                    );
                    reply.sign(msg.preamble.seq, &local_peer.private_key)?;
                    let reply_handle = self.relay_signed_message(reply)?;
                    self.reply_handles.push_back(reply_handle);
                }
            }

            let now = get_epoch_time_secs();
            let _msgtype = msg.payload.get_message_description().to_owned();
            let _relayers = format!("{:?}", &msg.relayers);
            let _seq = msg.request_id();

            if update_stats {
                // successfully got a message we asked for-- update stats
                if self.stats.first_contact_time == 0 {
                    self.stats.first_contact_time = now;
                }

                let msg_id = msg.payload.get_message_id();
                let count = match self.stats.msg_rx_counts.get(&msg_id) {
                    None => 1,
                    Some(c) => c + 1,
                };

                self.stats.msg_rx_counts.insert(msg_id, count);

                self.stats.msgs_rx += 1;
                self.stats.last_recv_time = now;
                self.stats.last_contact_time = get_epoch_time_secs();
                self.stats.add_healthpoint(true);

                // update chain view from preamble
                if msg.preamble.burn_block_height > self.burnchain_tip_height {
                    self.burnchain_tip_height = msg.preamble.burn_block_height;
                    self.burnchain_tip_burn_header_hash = msg.preamble.burn_block_hash.clone();
                }

                if msg.preamble.burn_stable_block_height > self.burnchain_stable_tip_height {
                    self.burnchain_stable_tip_height = msg.preamble.burn_stable_block_height;
                    self.burnchain_stable_tip_burn_header_hash =
                        msg.preamble.burn_stable_block_hash.clone();
                }

                debug!(
                    "{:?}: remote chain view is ({},{})-({},{})",
                    self,
                    self.burnchain_stable_tip_height,
                    &self.burnchain_stable_tip_burn_header_hash,
                    self.burnchain_tip_height,
                    &self.burnchain_tip_burn_header_hash
                );
            } else {
                // got an unhandled message we didn't ask for
                self.stats.msgs_rx_unsolicited += 1;
            }

            debug!(
                "{:?}: Received message {}, relayed by {}",
                &self, &_msgtype, &_relayers
            );

            // Is there someone else waiting for this message?  If so, pass it along.
            let fulfill_opt = self.connection.fulfill_request(msg);
            match fulfill_opt {
                None => {
                    debug!(
                        "{:?}: Fulfilled pending message request (type {} seq {})",
                        &self, _msgtype, _seq
                    );
                }
                Some(msg) => {
                    if consumed {
                        // already handled
                        debug!(
                            "{:?}: Consumed message (type {} seq {})",
                            &self, _msgtype, _seq
                        );
                    } else {
                        test_debug!(
                            "{:?}: Try handling message (type {} seq {})",
                            &self,
                            _msgtype,
                            _seq
                        );
                        let msg_opt = self.handle_data_message(
                            local_peer,
                            peerdb,
                            sortdb,
                            pox_id,
                            chainstate,
                            header_cache,
                            burnchain_view,
                            msg,
                        )?;
                        match msg_opt {
                            Some(msg) => {
                                debug!("{:?}: Did not handle message (type {} seq {}); passing upstream", &self, _msgtype, _seq);
                                unsolicited.push(msg);
                            }
                            None => {
                                debug!("{:?}: Handled message {} seq {}", &self, _msgtype, _seq);
                            }
                        }
                    }
                }
            }
        }

        Ok(unsolicited)
    }

    /// Remove all timed-out messages, and ding the remote peer as unhealthy
    pub fn clear_timeouts(&mut self) -> () {
        let num_drained = self.connection.drain_timeouts();
        for _ in 0..num_drained {
            self.stats.add_healthpoint(false);
        }
    }

    /// Get a ref to the conversation stats
    pub fn get_stats(&self) -> &NeighborStats {
        &self.stats
    }

    /// Get a mut ref to the conversation stats
    pub fn get_stats_mut(&mut self) -> &mut NeighborStats {
        &mut self.stats
    }
}

#[cfg(test)]
mod test {
    use std::fs;
    use std::io::prelude::*;
    use std::io::Read;
    use std::io::Write;
    use std::net::SocketAddr;
    use std::net::SocketAddrV4;

    use burnchains::bitcoin::address::BitcoinAddress;
    use burnchains::bitcoin::keys::BitcoinPublicKey;
    use burnchains::burnchain::*;
    use burnchains::*;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::*;
    use chainstate::stacks::db::ChainStateBootData;
    use chainstate::*;
    use core::{NETWORK_P2P_PORT, PEER_VERSION_TESTNET};
    use net::connection::*;
    use net::db::*;
    use net::p2p::*;
    use net::test::*;
    use net::*;
    use util::pipe::*;
    use util::secp256k1::*;
    use util::test::*;
    use util::uint::*;
    use vm::costs::ExecutionCost;

    use crate::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash, SortitionId};

    use super::*;

    fn make_test_chain_dbs(
        testname: &str,
        burnchain: &Burnchain,
        network_id: u32,
        key_expires: u64,
        data_url: UrlString,
        asn4_entries: &Vec<ASEntry4>,
        initial_neighbors: &Vec<Neighbor>,
    ) -> (PeerDB, SortitionDB, PoxId, StacksChainState) {
        let test_path = format!("/tmp/blockstack-test-databases-{}", testname);
        match fs::metadata(&test_path) {
            Ok(_) => {
                fs::remove_dir_all(&test_path).unwrap();
            }
            Err(_) => {}
        };

        fs::create_dir_all(&test_path).unwrap();

        let sortdb_path = format!("{}/burn", &test_path);
        let peerdb_path = format!("{}/peers.sqlite", &test_path);
        let chainstate_path = format!("{}/chainstate", &test_path);

        let peerdb = PeerDB::connect(
            &peerdb_path,
            true,
            network_id,
            burnchain.network_id,
            None,
            key_expires,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            NETWORK_P2P_PORT,
            data_url.clone(),
            &asn4_entries,
            Some(&initial_neighbors),
        )
        .unwrap();
        let sortdb = SortitionDB::connect(
            &sortdb_path,
            burnchain.first_block_height,
            &burnchain.first_block_hash,
            get_epoch_time_secs(),
            true,
        )
        .unwrap();

        let first_burnchain_block_height = burnchain.first_block_height;
        let first_burnchain_block_hash = burnchain.first_block_hash;

        let mut boot_data = ChainStateBootData::new(&burnchain, vec![], None);

        let (chainstate, _) = StacksChainState::open_and_exec(
            false,
            network_id,
            &chainstate_path,
            Some(&mut boot_data),
            ExecutionCost::max_value(),
        )
        .unwrap();

        let pox_id = {
            let ic = sortdb.index_conn();
            let tip_sort_id = SortitionDB::get_canonical_sortition_tip(sortdb.conn()).unwrap();
            let sortdb_reader = SortitionHandleConn::open_reader(&ic, &tip_sort_id).unwrap();
            sortdb_reader.get_pox_id().unwrap()
        };

        (peerdb, sortdb, pox_id, chainstate)
    }

    fn convo_send_recv(
        sender: &mut ConversationP2P,
        mut sender_handles: Vec<&mut ReplyHandleP2P>,
        receiver: &mut ConversationP2P,
    ) -> () {
        let (mut pipe_read, mut pipe_write) = Pipe::new();
        pipe_read.set_nonblocking(true);

        loop {
            let mut res = true;
            for i in 0..sender_handles.len() {
                let r = sender_handles[i].try_flush().unwrap();
                res = r && res;
            }

            sender.try_flush().unwrap();
            receiver.try_flush().unwrap();

            pipe_write.try_flush().unwrap();

            let all_relays_flushed =
                receiver.num_pending_outbound() == 0 && sender.num_pending_outbound() == 0;

            let nw = sender.send(&mut pipe_write).unwrap();
            let nr = receiver.recv(&mut pipe_read).unwrap();

            test_debug!(
                "res = {}, all_relays_flushed = {}, nr = {}, nw = {}",
                res,
                all_relays_flushed,
                nr,
                nw
            );
            if res && all_relays_flushed && nr == 0 && nw == 0 {
                break;
            }
        }

        eprintln!("pipe_read = {:?}", pipe_read);
        eprintln!("pipe_write = {:?}", pipe_write);
    }

    fn db_setup(
        peerdb: &mut PeerDB,
        sortdb: &mut SortitionDB,
        socketaddr: &SocketAddr,
        chain_view: &BurnchainView,
    ) -> () {
        {
            let mut tx = peerdb.tx_begin().unwrap();
            PeerDB::set_local_ipaddr(
                &mut tx,
                &PeerAddress::from_socketaddr(socketaddr),
                socketaddr.port(),
            )
            .unwrap();
            tx.commit().unwrap();
        }
        let mut prev_snapshot = SortitionDB::get_first_block_snapshot(sortdb.conn()).unwrap();
        for i in prev_snapshot.block_height..chain_view.burn_block_height + 1 {
            let mut next_snapshot = prev_snapshot.clone();

            let big_i = Uint256::from_u64(i as u64);
            let mut big_i_bytes_32 = [0u8; 32];
            let mut big_i_bytes_20 = [0u8; 20];
            big_i_bytes_32.copy_from_slice(&big_i.to_u8_slice());
            big_i_bytes_20.copy_from_slice(&big_i.to_u8_slice()[0..20]);

            next_snapshot.block_height += 1;
            next_snapshot.parent_burn_header_hash = next_snapshot.burn_header_hash.clone();
            if i == chain_view.burn_block_height {
                next_snapshot.burn_header_hash = chain_view.burn_block_hash.clone();
            } else if i == chain_view.burn_stable_block_height {
                next_snapshot.burn_header_hash = chain_view.burn_stable_block_hash.clone();
            } else {
                next_snapshot.burn_header_hash = BurnchainHeaderHash(big_i_bytes_32.clone());
            }

            next_snapshot.consensus_hash = ConsensusHash(big_i_bytes_20);
            next_snapshot.sortition_id = SortitionId(big_i_bytes_32.clone());
            next_snapshot.parent_sortition_id = prev_snapshot.sortition_id.clone();
            next_snapshot.ops_hash = OpsHash::from_bytes(&big_i_bytes_32).unwrap();
            next_snapshot.winning_stacks_block_hash = BlockHeaderHash(big_i_bytes_32.clone());
            next_snapshot.winning_block_txid = Txid(big_i_bytes_32.clone());
            next_snapshot.total_burn += 1;
            next_snapshot.sortition = true;
            next_snapshot.sortition_hash = next_snapshot
                .sortition_hash
                .mix_burn_header(&BurnchainHeaderHash(big_i_bytes_32.clone()));
            next_snapshot.num_sortitions += 1;

            let mut tx = SortitionHandleTx::begin(sortdb, &prev_snapshot.sortition_id).unwrap();

            let next_index_root = tx
                .append_chain_tip_snapshot(
                    &prev_snapshot,
                    &next_snapshot,
                    &vec![],
                    &vec![],
                    None,
                    None,
                    None,
                )
                .unwrap();
            next_snapshot.index_root = next_index_root;

            test_debug!(
                "i = {}, chain_view.burn_block_height = {}, ch = {}",
                i,
                chain_view.burn_block_height,
                next_snapshot.consensus_hash
            );

            prev_snapshot = next_snapshot;

            tx.commit().unwrap();
        }
    }

    fn testing_burnchain_config() -> Burnchain {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        Burnchain {
            peer_version: PEER_VERSION_TESTNET,
            network_id: 0,
            chain_name: "bitcoin".to_string(),
            network_name: "testnet".to_string(),
            working_dir: "/nope".to_string(),
            consensus_hash_lifetime: 24,
            stable_confirmations: 7,
            first_block_height: 12300,
            initial_reward_start_block: 12300,
            first_block_hash: first_burn_hash.clone(),
            first_block_timestamp: 0,
            pox_constants: PoxConstants::test_default(),
        }
    }

    #[test]
    #[ignore]
    fn convo_handshake_accept() {
        with_timeout(100, || {
            let conn_opts = ConnectionOptions::default();

            let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
            let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

            let burnchain = testing_burnchain_config();

            let mut chain_view = BurnchainView {
                burn_block_height: 12348,
                burn_block_hash: BurnchainHeaderHash([0x11; 32]),
                burn_stable_block_height: 12341,
                burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
                last_burn_block_hashes: HashMap::new(),
            };
            chain_view.make_test_data();

            let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
                "convo_handshake_accept_1",
                &burnchain,
                0x9abcdef0,
                12350,
                "http://peer1.com".into(),
                &vec![],
                &vec![],
            );
            let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
                "convo_handshake_accept_2",
                &burnchain,
                0x9abcdef0,
                12351,
                "http://peer2.com".into(),
                &vec![],
                &vec![],
            );

            db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
            db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

            let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
            let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

            let mut convo_1 =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
            let mut convo_2 =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

            // no peer public keys known yet
            assert!(convo_1.connection.get_public_key().is_none());
            assert!(convo_2.connection.get_public_key().is_none());

            // convo_1 sends a handshake to convo_2
            let handshake_data_1 = HandshakeData::from_local_peer(&local_peer_1);
            let handshake_1 = convo_1
                .sign_message(
                    &chain_view,
                    &local_peer_1.private_key,
                    StacksMessageType::Handshake(handshake_data_1.clone()),
                )
                .unwrap();
            let mut rh_1 = convo_1.send_signed_request(handshake_1, 1000000).unwrap();

            // convo_2 receives it and processes it, and since no one is waiting for it, will forward
            // it along to the chat caller (us)
            test_debug!("send handshake");
            convo_send_recv(&mut convo_1, vec![&mut rh_1], &mut convo_2);
            let unhandled_2 = convo_2
                .chat(
                    &local_peer_2,
                    &mut peerdb_2,
                    &sortdb_2,
                    &pox_id_2,
                    &mut chainstate_2,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            // convo_1 has a handshakeaccept
            test_debug!("send handshake-accept");
            convo_send_recv(&mut convo_2, vec![&mut rh_1], &mut convo_1);
            let unhandled_1 = convo_1
                .chat(
                    &local_peer_1,
                    &mut peerdb_1,
                    &sortdb_1,
                    &pox_id_1,
                    &mut chainstate_1,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            let reply_1 = rh_1.recv(0).unwrap();

            assert_eq!(unhandled_1.len(), 0);
            assert_eq!(unhandled_2.len(), 1);

            // convo 2 returns the handshake from convo 1
            match unhandled_2[0].payload {
                StacksMessageType::Handshake(ref data) => {
                    assert_eq!(handshake_data_1, *data);
                }
                _ => {
                    assert!(false);
                }
            };

            // received a valid HandshakeAccept from peer 2
            match reply_1.payload {
                StacksMessageType::HandshakeAccept(ref data) => {
                    assert_eq!(data.handshake.addrbytes, local_peer_2.addrbytes);
                    assert_eq!(data.handshake.port, local_peer_2.port);
                    assert_eq!(data.handshake.services, local_peer_2.services);
                    assert_eq!(
                        data.handshake.node_public_key,
                        StacksPublicKeyBuffer::from_public_key(&Secp256k1PublicKey::from_private(
                            &local_peer_2.private_key
                        ))
                    );
                    assert_eq!(
                        data.handshake.expire_block_height,
                        local_peer_2.private_key_expire
                    );
                    assert_eq!(data.handshake.data_url, "http://peer2.com".into());
                    assert_eq!(data.heartbeat_interval, conn_opts.heartbeat);
                }
                _ => {
                    assert!(false);
                }
            };

            // convo_2 got updated with convo_1's peer info, but no heartbeat info
            assert_eq!(convo_2.peer_heartbeat, 3600);
            assert_eq!(
                convo_2.connection.get_public_key().unwrap(),
                Secp256k1PublicKey::from_private(&local_peer_1.private_key)
            );
            assert_eq!(convo_2.data_url, "http://peer1.com".into());

            // convo_1 got updated with convo_2's peer info, as well as heartbeat
            assert_eq!(convo_1.peer_heartbeat, conn_opts.heartbeat);
            assert_eq!(
                convo_1.connection.get_public_key().unwrap(),
                Secp256k1PublicKey::from_private(&local_peer_2.private_key)
            );
            assert_eq!(convo_1.data_url, "http://peer2.com".into());
        })
    }

    #[test]
    fn convo_handshake_reject() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
            "convo_handshake_reject_1",
            &burnchain,
            0x9abcdef0,
            12350,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        );
        let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
            "convo_handshake_reject_2",
            &burnchain,
            0x9abcdef0,
            12351,
            "http://peer2.com".into(),
            &vec![],
            &vec![],
        );

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
        db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
        let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

        let mut convo_1 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
        let mut convo_2 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

        // no peer public keys known yet
        assert!(convo_1.connection.get_public_key().is_none());
        assert!(convo_2.connection.get_public_key().is_none());

        // convo_1 sends a _stale_ handshake to convo_2 (wrong public key)
        let mut handshake_data_1 = HandshakeData::from_local_peer(&local_peer_1);
        handshake_data_1.expire_block_height = 12340;
        let handshake_1 = convo_1
            .sign_message(
                &chain_view,
                &local_peer_1.private_key,
                StacksMessageType::Handshake(handshake_data_1.clone()),
            )
            .unwrap();

        let mut rh_1 = convo_1.send_signed_request(handshake_1, 1000000).unwrap();

        // convo_2 receives it and automatically rejects it.
        convo_send_recv(&mut convo_1, vec![&mut rh_1], &mut convo_2);
        let unhandled_2 = convo_2
            .chat(
                &local_peer_2,
                &mut peerdb_2,
                &sortdb_2,
                &pox_id_2,
                &mut chainstate_2,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        // convo_1 has a handshakreject
        convo_send_recv(&mut convo_2, vec![&mut rh_1], &mut convo_1);
        let unhandled_1 = convo_1
            .chat(
                &local_peer_1,
                &mut peerdb_1,
                &sortdb_1,
                &pox_id_1,
                &mut chainstate_1,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        let reply_1 = rh_1.recv(0).unwrap();

        assert_eq!(unhandled_1.len(), 0);
        assert_eq!(unhandled_2.len(), 0);

        // received a valid HandshakeReject from peer 2
        match reply_1.payload {
            StacksMessageType::HandshakeReject => {}
            _ => {
                assert!(false);
            }
        };

        // neither peer updated their info on one another
        assert!(convo_1.connection.get_public_key().is_none());
        assert!(convo_2.connection.get_public_key().is_none());
    }

    #[test]
    fn convo_handshake_badsignature() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
            "convo_handshake_badsignature_1",
            &burnchain,
            0x9abcdef0,
            12350,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        );
        let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
            "convo_handshake_badsignature_2",
            &burnchain,
            0x9abcdef0,
            12351,
            "http://peer2.com".into(),
            &vec![],
            &vec![],
        );

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
        db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
        let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

        let mut convo_1 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
        let mut convo_2 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

        // no peer public keys known yet
        assert!(convo_1.connection.get_public_key().is_none());
        assert!(convo_2.connection.get_public_key().is_none());

        // convo_1 sends an _invalid_ handshake to convo_2 (bad signature)
        let handshake_data_1 = HandshakeData::from_local_peer(&local_peer_1);
        let mut handshake_1 = convo_1
            .sign_message(
                &chain_view,
                &local_peer_1.private_key,
                StacksMessageType::Handshake(handshake_data_1.clone()),
            )
            .unwrap();
        match handshake_1.payload {
            StacksMessageType::Handshake(ref mut data) => {
                data.expire_block_height += 1;
            }
            _ => panic!(),
        };

        let mut rh_1 = convo_1.send_signed_request(handshake_1, 1000000).unwrap();

        // convo_2 receives it and processes it, and barfs
        convo_send_recv(&mut convo_1, vec![&mut rh_1], &mut convo_2);
        let unhandled_2_err = convo_2.chat(
            &local_peer_2,
            &mut peerdb_2,
            &sortdb_2,
            &pox_id_2,
            &mut chainstate_2,
            &mut BlockHeaderCache::new(),
            &chain_view,
        );

        // convo_1 gets a nack and consumes it
        convo_send_recv(&mut convo_2, vec![&mut rh_1], &mut convo_1);
        let unhandled_1 = convo_1
            .chat(
                &local_peer_1,
                &mut peerdb_1,
                &sortdb_1,
                &pox_id_1,
                &mut chainstate_1,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        // the waiting reply aborts on disconnect
        let reply_1_err = rh_1.recv(0);

        assert_eq!(unhandled_2_err.unwrap_err(), net_error::InvalidMessage);
        assert_eq!(reply_1_err, Err(net_error::ConnectionBroken));

        assert_eq!(unhandled_1.len(), 0);

        // neither peer updated their info on one another
        assert!(convo_1.connection.get_public_key().is_none());
        assert!(convo_2.connection.get_public_key().is_none());
    }

    #[test]
    fn convo_handshake_self() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
            "convo_handshake_self_1",
            &burnchain,
            0x9abcdef0,
            12350,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        );
        let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
            "convo_handshake_self_2",
            &burnchain,
            0x9abcdef0,
            12351,
            "http://peer2.com".into(),
            &vec![],
            &vec![],
        );

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
        db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
        let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

        let mut convo_1 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
        let mut convo_2 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

        // no peer public keys known yet
        assert!(convo_1.connection.get_public_key().is_none());
        assert!(convo_2.connection.get_public_key().is_none());

        // convo_1 sends a handshake to itself (not allowed)
        let handshake_data_1 = HandshakeData::from_local_peer(&local_peer_2);
        let handshake_1 = convo_1
            .sign_message(
                &chain_view,
                &local_peer_2.private_key,
                StacksMessageType::Handshake(handshake_data_1.clone()),
            )
            .unwrap();
        let mut rh_1 = convo_1.send_signed_request(handshake_1, 1000000).unwrap();

        // convo_2 receives it and processes it automatically (consuming it), and give back a handshake reject
        convo_send_recv(&mut convo_1, vec![&mut rh_1], &mut convo_2);
        let unhandled_2 = convo_2
            .chat(
                &local_peer_2,
                &mut peerdb_1,
                &sortdb_1,
                &pox_id_1,
                &mut chainstate_1,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        // convo_1 gets a handshake reject and consumes it
        convo_send_recv(&mut convo_2, vec![&mut rh_1], &mut convo_1);
        let unhandled_1 = convo_1
            .chat(
                &local_peer_1,
                &mut peerdb_2,
                &sortdb_2,
                &pox_id_2,
                &mut chainstate_2,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        // get back handshake reject
        let reply_1 = rh_1.recv(0).unwrap();

        assert_eq!(unhandled_1.len(), 0);
        assert_eq!(unhandled_2.len(), 0);

        // received a valid HandshakeReject from peer 2
        match reply_1.payload {
            StacksMessageType::HandshakeReject => {}
            _ => {
                assert!(false);
            }
        };

        // neither peer updated their info on one another
        assert!(convo_1.connection.get_public_key().is_none());
        assert!(convo_2.connection.get_public_key().is_none());
    }

    #[test]
    fn convo_ping() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
            "convo_ping_1",
            &burnchain,
            0x9abcdef0,
            12350,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        );
        let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
            "convo_ping_2",
            &burnchain,
            0x9abcdef0,
            12351,
            "http://peer2.com".into(),
            &vec![],
            &vec![],
        );

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
        db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
        let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

        let mut convo_1 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
        let mut convo_2 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

        // convo_1 sends a handshake to convo_2
        let handshake_data_1 = HandshakeData::from_local_peer(&local_peer_1);
        let handshake_1 = convo_1
            .sign_message(
                &chain_view,
                &local_peer_1.private_key,
                StacksMessageType::Handshake(handshake_data_1.clone()),
            )
            .unwrap();
        let mut rh_handshake_1 = convo_1
            .send_signed_request(handshake_1.clone(), 1000000)
            .unwrap();

        // convo_1 sends a ping to convo_2
        let ping_data_1 = PingData::new();
        let ping_1 = convo_1
            .sign_message(
                &chain_view,
                &local_peer_1.private_key,
                StacksMessageType::Ping(ping_data_1.clone()),
            )
            .unwrap();
        let mut rh_ping_1 = convo_1
            .send_signed_request(ping_1.clone(), 1000000)
            .unwrap();

        // convo_2 receives the handshake and ping and processes both, and since no one is waiting for the handshake, will forward
        // it along to the chat caller (us)
        test_debug!("send handshake {:?}", &handshake_1);
        test_debug!("send ping {:?}", &ping_1);
        convo_send_recv(
            &mut convo_1,
            vec![&mut rh_handshake_1, &mut rh_ping_1],
            &mut convo_2,
        );
        let unhandled_2 = convo_2
            .chat(
                &local_peer_2,
                &mut peerdb_2,
                &sortdb_2,
                &pox_id_2,
                &mut chainstate_2,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        // convo_1 has a handshakeaccept
        test_debug!("reply handshake-accept");
        test_debug!("send pong");
        convo_send_recv(
            &mut convo_2,
            vec![&mut rh_handshake_1, &mut rh_ping_1],
            &mut convo_1,
        );
        let unhandled_1 = convo_1
            .chat(
                &local_peer_1,
                &mut peerdb_1,
                &sortdb_1,
                &pox_id_1,
                &mut chainstate_1,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        let reply_handshake_1 = rh_handshake_1.recv(0).unwrap();
        let reply_ping_1 = rh_ping_1.recv(0).unwrap();

        assert_eq!(unhandled_1.len(), 0);
        assert_eq!(unhandled_2.len(), 1); // only the handshake is given back.  the ping is consumed

        // convo 2 returns the handshake from convo 1
        match unhandled_2[0].payload {
            StacksMessageType::Handshake(ref data) => {
                assert_eq!(handshake_data_1, *data);
            }
            _ => {
                assert!(false);
            }
        };

        // convo 2 replied to convo 1 with a matching pong
        match reply_ping_1.payload {
            StacksMessageType::Pong(ref data) => {
                assert_eq!(data.nonce, ping_data_1.nonce);
            }
            _ => {
                assert!(false);
            }
        }
    }

    #[test]
    fn convo_handshake_ping_loop() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
            "convo_handshake_ping_loop_1",
            &burnchain,
            0x9abcdef0,
            12350,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        );
        let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
            "convo_handshake_ping_loop_2",
            &burnchain,
            0x9abcdef0,
            12351,
            "http://peer2.com".into(),
            &vec![],
            &vec![],
        );

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
        db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
        let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

        let mut convo_1 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
        let mut convo_2 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 1);

        for i in 0..5 {
            // do handshake/ping over and over, with different keys.
            // tests re-keying.

            // convo_1 sends a handshake to convo_2
            let handshake_data_1 = HandshakeData::from_local_peer(&local_peer_1);
            let handshake_1 = convo_1
                .sign_message(
                    &chain_view,
                    &local_peer_1.private_key,
                    StacksMessageType::Handshake(handshake_data_1.clone()),
                )
                .unwrap();
            let mut rh_handshake_1 = convo_1.send_signed_request(handshake_1, 1000000).unwrap();

            // convo_1 sends a ping to convo_2
            let ping_data_1 = PingData::new();
            let ping_1 = convo_1
                .sign_message(
                    &chain_view,
                    &local_peer_1.private_key,
                    StacksMessageType::Ping(ping_data_1.clone()),
                )
                .unwrap();
            let mut rh_ping_1 = convo_1.send_signed_request(ping_1, 1000000).unwrap();

            // convo_2 receives the handshake and ping and processes both, and since no one is waiting for the handshake, will forward
            // it along to the chat caller (us)
            convo_send_recv(
                &mut convo_1,
                vec![&mut rh_handshake_1, &mut rh_ping_1],
                &mut convo_2,
            );
            let unhandled_2 = convo_2
                .chat(
                    &local_peer_2,
                    &mut peerdb_2,
                    &sortdb_2,
                    &pox_id_2,
                    &mut chainstate_2,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            // convo_1 has a handshakeaccept
            convo_send_recv(
                &mut convo_2,
                vec![&mut rh_handshake_1, &mut rh_ping_1],
                &mut convo_1,
            );
            let unhandled_1 = convo_1
                .chat(
                    &local_peer_1,
                    &mut peerdb_1,
                    &sortdb_1,
                    &pox_id_1,
                    &mut chainstate_1,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            let reply_handshake_1 = rh_handshake_1.recv(0).unwrap();
            let reply_ping_1 = rh_ping_1.recv(0).unwrap();

            assert_eq!(unhandled_1.len(), 0);
            assert_eq!(unhandled_2.len(), 1); // only the handshake is given back.  the ping is consumed

            // convo 2 returns the handshake from convo 1
            match unhandled_2[0].payload {
                StacksMessageType::Handshake(ref data) => {
                    assert_eq!(handshake_data_1, *data);
                }
                _ => {
                    assert!(false);
                }
            };

            // convo 2 replied to convo 1 with a matching pong
            match reply_ping_1.payload {
                StacksMessageType::Pong(ref data) => {
                    assert_eq!(data.nonce, ping_data_1.nonce);
                }
                _ => {
                    assert!(false);
                }
            }

            // received a valid HandshakeAccept from peer 2
            match reply_handshake_1.payload {
                StacksMessageType::HandshakeAccept(ref data) => {
                    assert_eq!(data.handshake.addrbytes, local_peer_2.addrbytes);
                    assert_eq!(data.handshake.port, local_peer_2.port);
                    assert_eq!(data.handshake.services, local_peer_2.services);
                    assert_eq!(
                        data.handshake.node_public_key,
                        StacksPublicKeyBuffer::from_public_key(&Secp256k1PublicKey::from_private(
                            &local_peer_2.private_key
                        ))
                    );
                    assert_eq!(
                        data.handshake.expire_block_height,
                        local_peer_2.private_key_expire
                    );
                    assert_eq!(data.heartbeat_interval, conn_opts.heartbeat);
                }
                _ => {
                    assert!(false);
                }
            };

            // convo_2 got updated with convo_1's peer info, and default heartbeat filled in
            assert_eq!(convo_2.peer_heartbeat, 3600);
            assert_eq!(
                convo_2
                    .connection
                    .get_public_key()
                    .unwrap()
                    .to_bytes_compressed(),
                Secp256k1PublicKey::from_private(&local_peer_1.private_key).to_bytes_compressed()
            );

            // convo_1 got updated with convo_2's peer info, as well as heartbeat
            assert_eq!(convo_1.peer_heartbeat, conn_opts.heartbeat);
            assert_eq!(
                convo_1
                    .connection
                    .get_public_key()
                    .unwrap()
                    .to_bytes_compressed(),
                Secp256k1PublicKey::from_private(&local_peer_2.private_key).to_bytes_compressed()
            );

            // regenerate keys and expiries in peer 1
            let new_privkey = Secp256k1PrivateKey::new();
            {
                let mut tx = peerdb_1.tx_begin().unwrap();
                PeerDB::set_local_private_key(&mut tx, &new_privkey, (12350 + i) as u64).unwrap();
                tx.commit().unwrap();
            }
        }
    }

    #[test]
    fn convo_nack_unsolicited() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
            "convo_nack_unsolicited_1",
            &burnchain,
            0x9abcdef0,
            12350,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        );
        let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
            "convo_nack_unsolicited_2",
            &burnchain,
            0x9abcdef0,
            12351,
            "http://peer2.com".into(),
            &vec![],
            &vec![],
        );

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
        db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
        let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

        let mut convo_1 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
        let mut convo_2 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

        // no peer public keys known yet
        assert!(convo_1.connection.get_public_key().is_none());
        assert!(convo_2.connection.get_public_key().is_none());

        // convo_1 sends a ping to convo_2
        let ping_data_1 = PingData::new();
        let ping_1 = convo_1
            .sign_message(
                &chain_view,
                &local_peer_1.private_key,
                StacksMessageType::Ping(ping_data_1.clone()),
            )
            .unwrap();
        let mut rh_ping_1 = convo_1.send_signed_request(ping_1, 1000000).unwrap();

        // convo_2 will reply with a nack since peer_1 hasn't authenticated yet
        convo_send_recv(&mut convo_1, vec![&mut rh_ping_1], &mut convo_2);
        let unhandled_2 = convo_2
            .chat(
                &local_peer_2,
                &mut peerdb_2,
                &sortdb_2,
                &pox_id_2,
                &mut chainstate_2,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        // convo_1 has a nack
        convo_send_recv(&mut convo_2, vec![&mut rh_ping_1], &mut convo_1);
        let unhandled_1 = convo_1
            .chat(
                &local_peer_1,
                &mut peerdb_1,
                &sortdb_1,
                &pox_id_1,
                &mut chainstate_1,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        let reply_1 = rh_ping_1.recv(0).unwrap();

        // convo_2 gives back nothing
        assert_eq!(unhandled_1.len(), 0);
        assert_eq!(unhandled_2.len(), 0);

        // convo_1 got a NACK
        match reply_1.payload {
            StacksMessageType::Nack(ref data) => {
                assert_eq!(data.error_code, NackErrorCodes::HandshakeRequired);
            }
            _ => {
                assert!(false);
            }
        };

        // convo_2 did NOT get updated with convo_1's peer info
        assert_eq!(convo_2.peer_heartbeat, 0);
        assert!(convo_2.connection.get_public_key().is_none());

        // convo_1 did NOT get updated
        assert_eq!(convo_1.peer_heartbeat, 0);
        assert!(convo_2.connection.get_public_key().is_none());
    }

    #[test]
    fn convo_handshake_getblocksinv() {
        with_timeout(100, || {
            let conn_opts = ConnectionOptions::default();

            let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
            let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

            let first_burn_hash = BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap();

            let burnchain = testing_burnchain_config();

            let mut chain_view = BurnchainView {
                burn_block_height: 12331, // burnchain.reward_cycle_to_block_height(burnchain.block_height_to_reward_cycle(12348 - 8).unwrap()),
                burn_block_hash: BurnchainHeaderHash([0x11; 32]),
                burn_stable_block_height: 12331 - 7, // burnchain.reward_cycle_to_block_height(burnchain.block_height_to_reward_cycle(12341 - 8).unwrap() - 1),
                burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
                last_burn_block_hashes: HashMap::new(),
            };
            chain_view.make_test_data();

            let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
                "convo_handshake_getblocksinv_1",
                &burnchain,
                0x9abcdef0,
                12350,
                "http://peer1.com".into(),
                &vec![],
                &vec![],
            );
            let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
                "convo_handshake_getblocksinv_2",
                &burnchain,
                0x9abcdef0,
                12351,
                "http://peer2.com".into(),
                &vec![],
                &vec![],
            );

            db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
            db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

            let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
            let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

            let mut convo_1 =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
            let mut convo_2 =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

            // no peer public keys known yet
            assert!(convo_1.connection.get_public_key().is_none());
            assert!(convo_2.connection.get_public_key().is_none());

            // convo_1 sends a handshake to convo_2
            let handshake_data_1 = HandshakeData::from_local_peer(&local_peer_1);
            let handshake_1 = convo_1
                .sign_message(
                    &chain_view,
                    &local_peer_1.private_key,
                    StacksMessageType::Handshake(handshake_data_1.clone()),
                )
                .unwrap();
            let mut rh_1 = convo_1.send_signed_request(handshake_1, 1000000).unwrap();

            // convo_2 receives it and processes it, and since no one is waiting for it, will forward
            // it along to the chat caller (us)
            test_debug!("send handshake");
            convo_send_recv(&mut convo_1, vec![&mut rh_1], &mut convo_2);
            let unhandled_2 = convo_2
                .chat(
                    &local_peer_2,
                    &mut peerdb_2,
                    &sortdb_2,
                    &pox_id_2,
                    &mut chainstate_2,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            // convo_1 has a handshakeaccept
            test_debug!("send handshake-accept");
            convo_send_recv(&mut convo_2, vec![&mut rh_1], &mut convo_1);
            let unhandled_1 = convo_1
                .chat(
                    &local_peer_1,
                    &mut peerdb_1,
                    &sortdb_1,
                    &pox_id_1,
                    &mut chainstate_1,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            let reply_1 = rh_1.recv(0).unwrap();

            assert_eq!(unhandled_1.len(), 0);
            assert_eq!(unhandled_2.len(), 1);

            // convo 2 returns the handshake from convo 1
            match unhandled_2[0].payload {
                StacksMessageType::Handshake(ref data) => {
                    assert_eq!(handshake_data_1, *data);
                }
                _ => {
                    assert!(false);
                }
            };

            // received a valid HandshakeAccept from peer 2
            match reply_1.payload {
                StacksMessageType::HandshakeAccept(ref data) => {
                    assert_eq!(data.handshake.addrbytes, local_peer_2.addrbytes);
                    assert_eq!(data.handshake.port, local_peer_2.port);
                    assert_eq!(data.handshake.services, local_peer_2.services);
                    assert_eq!(
                        data.handshake.node_public_key,
                        StacksPublicKeyBuffer::from_public_key(&Secp256k1PublicKey::from_private(
                            &local_peer_2.private_key
                        ))
                    );
                    assert_eq!(
                        data.handshake.expire_block_height,
                        local_peer_2.private_key_expire
                    );
                    assert_eq!(data.handshake.data_url, "http://peer2.com".into());
                    assert_eq!(data.heartbeat_interval, conn_opts.heartbeat);
                }
                _ => {
                    assert!(false);
                }
            };

            // convo_1 sends a getblocksinv to convo_2 for all the blocks in the last reward cycle
            let convo_1_chaintip =
                SortitionDB::get_canonical_burn_chain_tip(sortdb_1.conn()).unwrap();
            let convo_1_ancestor = {
                let ic = sortdb_1.index_conn();
                SortitionDB::get_ancestor_snapshot(
                    &ic,
                    convo_1_chaintip.block_height - 10 - 1,
                    &convo_1_chaintip.sortition_id,
                )
                .unwrap()
                .unwrap()
            };

            let getblocksdata_1 = GetBlocksInv {
                consensus_hash: convo_1_ancestor.consensus_hash,
                num_blocks: 10 as u16,
            };
            let getblocksdata_1_msg = convo_1
                .sign_message(
                    &chain_view,
                    &local_peer_1.private_key,
                    StacksMessageType::GetBlocksInv(getblocksdata_1.clone()),
                )
                .unwrap();
            let mut rh_1 = convo_1
                .send_signed_request(getblocksdata_1_msg, 10000000)
                .unwrap();

            // convo_2 receives it, and handles it
            test_debug!("send getblocksinv");
            convo_send_recv(&mut convo_1, vec![&mut rh_1], &mut convo_2);
            let unhandled_2 = convo_2
                .chat(
                    &local_peer_2,
                    &mut peerdb_2,
                    &sortdb_2,
                    &pox_id_2,
                    &mut chainstate_2,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            // convo_1 gets back a blocksinv message
            test_debug!("send blocksinv");
            convo_send_recv(&mut convo_2, vec![&mut rh_1], &mut convo_1);
            let unhandled_1 = convo_1
                .chat(
                    &local_peer_1,
                    &mut peerdb_1,
                    &sortdb_1,
                    &pox_id_1,
                    &mut chainstate_1,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            let reply_1 = rh_1.recv(0).unwrap();

            // no unhandled messages forwarded
            assert_eq!(unhandled_1, vec![]);
            assert_eq!(unhandled_2, vec![]);

            // convo 2 returned a block-inv for all blocks
            match reply_1.payload {
                StacksMessageType::BlocksInv(ref data) => {
                    assert_eq!(data.bitlen, 10);
                    test_debug!("data: {:?}", data);

                    // all burn blocks had sortitions, but we have no Stacks blocks :(
                    for i in 0..data.bitlen {
                        assert!(!data.has_ith_block(i));
                    }
                }
                x => {
                    error!("received invalid payload: {:?}", &x);
                    assert!(false);
                }
            }

            // request for a non-existent consensus hash
            let getblocksdata_diverged_1 = GetBlocksInv {
                consensus_hash: ConsensusHash([0xff; 20]),
                num_blocks: GETPOXINV_MAX_BITLEN as u16,
            };
            let getblocksdata_diverged_1_msg = convo_1
                .sign_message(
                    &chain_view,
                    &local_peer_1.private_key,
                    StacksMessageType::GetBlocksInv(getblocksdata_diverged_1.clone()),
                )
                .unwrap();
            let mut rh_1 = convo_1
                .send_signed_request(getblocksdata_diverged_1_msg, 10000000)
                .unwrap();

            // convo_2 receives it, and handles it
            test_debug!("send getblocksinv (diverged)");
            convo_send_recv(&mut convo_1, vec![&mut rh_1], &mut convo_2);
            let unhandled_2 = convo_2
                .chat(
                    &local_peer_2,
                    &mut peerdb_2,
                    &sortdb_2,
                    &pox_id_2,
                    &mut chainstate_2,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            // convo_1 gets back a nack message
            test_debug!("send nack (diverged)");
            convo_send_recv(&mut convo_2, vec![&mut rh_1], &mut convo_1);
            let unhandled_1 = convo_1
                .chat(
                    &local_peer_1,
                    &mut peerdb_1,
                    &sortdb_1,
                    &pox_id_1,
                    &mut chainstate_1,
                    &mut BlockHeaderCache::new(),
                    &chain_view,
                )
                .unwrap();

            let reply_1 = rh_1.recv(0).unwrap();

            // no unhandled messages forwarded
            assert_eq!(unhandled_1, vec![]);
            assert_eq!(unhandled_2, vec![]);

            // convo 2 returned a nack with the appropriate error message
            match reply_1.payload {
                StacksMessageType::Nack(ref data) => {
                    assert_eq!(data.error_code, NackErrorCodes::NoSuchBurnchainBlock);
                }
                _ => {
                    assert!(false);
                }
            }
        })
    }

    #[test]
    fn convo_natpunch() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let (mut peerdb_1, mut sortdb_1, pox_id_1, mut chainstate_1) = make_test_chain_dbs(
            "convo_natpunch_1",
            &burnchain,
            0x9abcdef0,
            12352,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        );
        let (mut peerdb_2, mut sortdb_2, pox_id_2, mut chainstate_2) = make_test_chain_dbs(
            "convo_natpunch_2",
            &burnchain,
            0x9abcdef0,
            12353,
            "http://peer2.com".into(),
            &vec![],
            &vec![],
        );

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);
        db_setup(&mut peerdb_2, &mut sortdb_2, &socketaddr_2, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();
        let local_peer_2 = PeerDB::get_local_peer(&peerdb_2.conn()).unwrap();

        let mut convo_1 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);
        let mut convo_2 =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr_1, &conn_opts, true, 0);

        // convo_1 sends natpunch request to convo_2
        let natpunch_1 = convo_1
            .sign_message(
                &chain_view,
                &local_peer_1.private_key,
                StacksMessageType::NatPunchRequest(0x12345678),
            )
            .unwrap();
        let mut rh_natpunch_1 = convo_1
            .send_signed_request(natpunch_1.clone(), 1000000)
            .unwrap();

        // convo_2 receives the natpunch request and processes it
        test_debug!("send natpunch {:?}", &natpunch_1);
        convo_send_recv(&mut convo_1, vec![&mut rh_natpunch_1], &mut convo_2);
        let unhandled_2 = convo_2
            .chat(
                &local_peer_2,
                &mut peerdb_2,
                &sortdb_2,
                &pox_id_2,
                &mut chainstate_2,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        // convo_1 gets back a natpunch reply
        test_debug!("reply natpunch-reply");
        convo_send_recv(&mut convo_2, vec![&mut rh_natpunch_1], &mut convo_1);
        let unhandled_1 = convo_1
            .chat(
                &local_peer_1,
                &mut peerdb_1,
                &sortdb_1,
                &pox_id_1,
                &mut chainstate_1,
                &mut BlockHeaderCache::new(),
                &chain_view,
            )
            .unwrap();

        let natpunch_reply_1 = rh_natpunch_1.recv(0).unwrap();

        // handled and consumed
        assert_eq!(unhandled_1.len(), 0);
        assert_eq!(unhandled_2.len(), 0);

        // convo_2 replies the natpunch data for convo_1 -- i.e. what convo_2 thinks convo_1's IP
        // address is
        match natpunch_reply_1.payload {
            StacksMessageType::NatPunchReply(ref data) => {
                assert_eq!(data.addrbytes, PeerAddress::from_socketaddr(&socketaddr_1));
                assert_eq!(data.nonce, 0x12345678);
            }
            _ => {
                assert!(false);
            }
        }
    }

    #[test]
    fn convo_is_preamble_valid() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr_1 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);
        let socketaddr_2 = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 2, 3, 4)), 8081);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let mut peerdb_1 = PeerDB::connect_memory(
            0x9abcdef0,
            0,
            12350,
            "http://peer1.com".into(),
            &vec![],
            &vec![],
        )
        .unwrap();

        let mut sortdb_1 = SortitionDB::connect_test(12300, &first_burn_hash).unwrap();

        db_setup(&mut peerdb_1, &mut sortdb_1, &socketaddr_1, &chain_view);

        let local_peer_1 = PeerDB::get_local_peer(&peerdb_1.conn()).unwrap();

        // network ID check
        {
            let mut convo_bad =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);

            let ping_data = PingData::new();
            convo_bad.network_id += 1;
            let ping_bad = convo_bad
                .sign_message(
                    &chain_view,
                    &local_peer_1.private_key,
                    StacksMessageType::Ping(ping_data.clone()),
                )
                .unwrap();
            convo_bad.network_id -= 1;

            assert_eq!(
                convo_bad.is_preamble_valid(&ping_bad, &chain_view),
                Err(net_error::InvalidMessage)
            );
        }

        // stable block height check
        {
            let mut convo_bad =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);

            let ping_data = PingData::new();

            let mut chain_view_bad = chain_view.clone();
            chain_view_bad.burn_stable_block_height -= 1;

            let ping_bad = convo_bad
                .sign_message(
                    &chain_view_bad,
                    &local_peer_1.private_key,
                    StacksMessageType::Ping(ping_data.clone()),
                )
                .unwrap();

            assert_eq!(
                convo_bad.is_preamble_valid(&ping_bad, &chain_view),
                Err(net_error::InvalidMessage)
            );
        }

        // unstable burn header hash mismatch
        {
            let mut convo_bad =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);

            let ping_data = PingData::new();

            let mut chain_view_bad = chain_view.clone();
            let old = chain_view_bad.burn_block_hash.clone();
            chain_view_bad.burn_block_hash = BurnchainHeaderHash([0x33; 32]);
            chain_view_bad.last_burn_block_hashes.insert(
                chain_view_bad.burn_block_height,
                chain_view_bad.burn_block_hash.clone(),
            );

            let ping_bad = convo_bad
                .sign_message(
                    &chain_view_bad,
                    &local_peer_1.private_key,
                    StacksMessageType::Ping(ping_data.clone()),
                )
                .unwrap();

            // considered valid as long as the stable burn header hash is valid
            assert_eq!(
                convo_bad.is_preamble_valid(&ping_bad, &chain_view),
                Ok(true)
            );
        }

        // stable burn header hash mismatch
        {
            let mut convo_bad =
                ConversationP2P::new(123, 456, &burnchain, &socketaddr_2, &conn_opts, true, 0);

            let ping_data = PingData::new();

            let mut chain_view_bad = chain_view.clone();
            let old = chain_view_bad.burn_stable_block_hash.clone();
            chain_view_bad.burn_stable_block_hash = BurnchainHeaderHash([0x11; 32]);
            chain_view_bad.last_burn_block_hashes.insert(
                chain_view_bad.burn_stable_block_height,
                chain_view_bad.burn_stable_block_hash.clone(),
            );

            let ping_bad = convo_bad
                .sign_message(
                    &chain_view_bad,
                    &local_peer_1.private_key,
                    StacksMessageType::Ping(ping_data.clone()),
                )
                .unwrap();

            assert_eq!(
                convo_bad.is_preamble_valid(&ping_bad, &chain_view),
                Err(net_error::InvalidMessage)
            );
        }
    }

    #[test]
    fn convo_process_relayers() {
        let conn_opts = ConnectionOptions::default();
        let socketaddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8090);

        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let burnchain = testing_burnchain_config();

        let mut chain_view = BurnchainView {
            burn_block_height: 12348,
            burn_block_hash: BurnchainHeaderHash([0x11; 32]),
            burn_stable_block_height: 12341,
            burn_stable_block_hash: BurnchainHeaderHash([0x22; 32]),
            last_burn_block_hashes: HashMap::new(),
        };
        chain_view.make_test_data();

        let local_peer = LocalPeer::new(
            123,
            burnchain.network_id,
            PeerAddress::from_ipv4(127, 0, 0, 1),
            NETWORK_P2P_PORT,
            None,
            get_epoch_time_secs() + 123456,
            UrlString::try_from("http://foo.com").unwrap(),
        );
        let mut convo =
            ConversationP2P::new(123, 456, &burnchain, &socketaddr, &conn_opts, true, 0);

        let payload = StacksMessageType::Nack(NackData { error_code: 123 });
        let msg = convo
            .sign_reply(&chain_view, &local_peer.private_key, payload, 123)
            .unwrap();

        // cycles
        let relay_cycles = vec![
            RelayData {
                peer: NeighborAddress {
                    addrbytes: PeerAddress([0u8; 16]),
                    port: 123,
                    public_key_hash: Hash160([0u8; 20]),
                },
                seq: 123,
            },
            RelayData {
                peer: NeighborAddress {
                    addrbytes: PeerAddress([1u8; 16]),
                    port: 456,
                    public_key_hash: Hash160([0u8; 20]),
                },
                seq: 456,
            },
        ];

        // contains localpeer
        let self_sent = vec![RelayData {
            peer: NeighborAddress {
                addrbytes: local_peer.addrbytes.clone(),
                port: local_peer.port,
                public_key_hash: Hash160::from_node_public_key(&StacksPublicKey::from_private(
                    &local_peer.private_key,
                )),
            },
            seq: 789,
        }];

        // allowed
        let mut relayers = vec![
            RelayData {
                peer: NeighborAddress {
                    addrbytes: PeerAddress([0u8; 16]),
                    port: 123,
                    public_key_hash: Hash160([0u8; 20]),
                },
                seq: 123,
            },
            RelayData {
                peer: NeighborAddress {
                    addrbytes: PeerAddress([1u8; 16]),
                    port: 456,
                    public_key_hash: Hash160([1u8; 20]),
                },
                seq: 456,
            },
        ];

        assert!(!convo.process_relayers(&local_peer, &msg.preamble, &relay_cycles));
        assert!(!convo.process_relayers(&local_peer, &msg.preamble, &self_sent));

        assert!(convo.process_relayers(&local_peer, &msg.preamble, &relayers));

        // stats updated
        assert_eq!(convo.stats.relayed_messages.len(), 2);
        let relayer_map = convo.stats.take_relayers();
        assert_eq!(convo.stats.relayed_messages.len(), 0);

        for r in relayers.drain(..) {
            assert!(relayer_map.contains_key(&r.peer));

            let stats = relayer_map.get(&r.peer).unwrap();
            assert_eq!(stats.num_messages, 1);
            assert_eq!(stats.num_bytes, (msg.preamble.payload_len - 1) as u64);
        }
    }
}

// TODO: test bandwidth limits
