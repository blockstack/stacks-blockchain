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

use std::borrow::Borrow;
use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet};
use std::convert::From;
use std::convert::TryFrom;
use std::error;
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::io;
use std::io::prelude::*;
use std::io::{Read, Write};
use std::net::IpAddr;
use std::net::Ipv4Addr;
use std::net::Ipv6Addr;
use std::net::SocketAddr;
use std::ops::Deref;
use std::str::FromStr;

use rand::thread_rng;
use rand::RngCore;
use regex::Regex;
use rusqlite;
use serde::de::Error as de_Error;
use serde::ser::Error as ser_Error;
use serde::{Deserialize, Serialize};
use serde_json;
use url;

use burnchains::Txid;
use chainstate::burn::ConsensusHash;
use chainstate::stacks::db::blocks::MemPoolRejection;
use chainstate::stacks::index::Error as marf_error;
use chainstate::stacks::Error as chainstate_error;
use chainstate::stacks::{
    Error as chain_error, StacksBlock, StacksMicroblock, StacksPublicKey, StacksTransaction,
};
use clarity_vm::clarity::Error as clarity_error;
use codec::Error as codec_error;
use codec::StacksMessageCodec;
use core::mempool::*;
use core::POX_REWARD_CYCLE_LENGTH;
use net::atlas::{Attachment, AttachmentInstance};
use util::db::DBConn;
use util::db::Error as db_error;
use util::get_epoch_time_secs;
use util::hash::Hash160;
use util::hash::DOUBLE_SHA256_ENCODED_SIZE;
use util::hash::HASH160_ENCODED_SIZE;
use util::hash::{hex_bytes, to_hex};
use util::log;
use util::secp256k1::MessageSignature;
use util::secp256k1::Secp256k1PublicKey;
use util::secp256k1::MESSAGE_SIGNATURE_ENCODED_SIZE;
use util::strings::UrlString;
use vm::types::TraitIdentifier;
use vm::{
    analysis::contract_interface_builder::ContractInterface, types::PrincipalData, ClarityName,
    ContractName, Value,
};

use crate::codec::BURNCHAIN_HEADER_HASH_ENCODED_SIZE;
use crate::types::chainstate::BlockHeaderHash;
use crate::types::chainstate::PoxId;
use crate::types::chainstate::{BurnchainHeaderHash, StacksAddress, StacksBlockId};
use crate::types::StacksPublicKeyBuffer;
use crate::util::hash::Sha256Sum;

use self::dns::*;
pub use self::http::StacksHttp;

pub mod asn;
pub mod atlas;
pub mod chat;
pub mod codec;
pub mod connection;
pub mod db;
pub mod dns;
pub mod download;
pub mod http;
pub mod inv;
pub mod neighbors;
pub mod p2p;
pub mod poll;
pub mod prune;
pub mod relay;
pub mod rpc;
pub mod server;

#[derive(Debug)]
pub enum Error {
    /// Failed to encode
    SerializeError(String),
    /// Failed to read
    ReadError(io::Error),
    /// Failed to decode
    DeserializeError(String),
    /// Failed to write
    WriteError(io::Error),
    /// Underflow -- not enough bytes to form the message
    UnderflowError(String),
    /// Overflow -- message too big
    OverflowError(String),
    /// Wrong protocol family
    WrongProtocolFamily,
    /// Array is too big
    ArrayTooLong,
    /// Receive timed out
    RecvTimeout,
    /// Error signing a message
    SigningError(String),
    /// Error verifying a message
    VerifyingError(String),
    /// Read stream is drained.  Try again
    TemporarilyDrained,
    /// Read stream has reached EOF (socket closed, end-of-file reached, etc.)
    PermanentlyDrained,
    /// Failed to read from the FS
    FilesystemError,
    /// Database error
    DBError(db_error),
    /// Socket mutex was poisoned
    SocketMutexPoisoned,
    /// Socket not instantiated
    SocketNotConnectedToPeer,
    /// Not connected to peer
    ConnectionBroken,
    /// Connection could not be (re-)established
    ConnectionError,
    /// Too many outgoing messages
    OutboxOverflow,
    /// Too many incoming messages
    InboxOverflow,
    /// Send error
    SendError(String),
    /// Recv error
    RecvError(String),
    /// Invalid message
    InvalidMessage,
    /// Invalid network handle
    InvalidHandle,
    /// Network handle is full
    FullHandle,
    /// Invalid handshake
    InvalidHandshake,
    /// Stale neighbor
    StaleNeighbor,
    /// No such neighbor
    NoSuchNeighbor,
    /// Failed to bind
    BindError,
    /// Failed to poll
    PollError,
    /// Failed to accept
    AcceptError,
    /// Failed to register socket with poller
    RegisterError,
    /// Failed to query socket metadata
    SocketError,
    /// server is not bound to a socket
    NotConnected,
    /// Remote peer is not connected
    PeerNotConnected,
    /// Too many peers
    TooManyPeers,
    /// Peer already connected
    AlreadyConnected(usize, NeighborKey),
    /// Message already in progress
    InProgress,
    /// Peer is denied
    Denied,
    /// Data URL is not known
    NoDataUrl,
    /// Peer is transmitting too fast
    PeerThrottled,
    /// Error resolving a DNS name
    LookupError(String),
    /// MARF error, percolated up from chainstate
    MARFError(marf_error),
    /// Clarity VM error, percolated up from chainstate
    ClarityError(clarity_error),
    /// Catch-all for chainstate errors that don't map cleanly into network errors
    ChainstateError(String),
    /// Catch-all for errors that a client should receive more information about
    ClientError(ClientError),
    /// Coordinator hung up
    CoordinatorClosed,
    /// view of state is stale (e.g. from the sortition db)
    StaleView,
    /// Tried to connect to myself
    ConnectionCycle,
    /// Requested data not found
    NotFoundError,
    /// Transient error (akin to EAGAIN)
    Transient(String),
}

impl From<codec_error> for Error {
    fn from(e: codec_error) -> Self {
        match e {
            codec_error::SerializeError(s) => Error::SerializeError(s),
            codec_error::ReadError(e) => Error::ReadError(e),
            codec_error::DeserializeError(s) => Error::DeserializeError(s),
            codec_error::WriteError(e) => Error::WriteError(e),
            codec_error::UnderflowError(s) => Error::UnderflowError(s),
            codec_error::OverflowError(s) => Error::OverflowError(s),
            codec_error::ArrayTooLong => Error::ArrayTooLong,
        }
    }
}

/// Enum for passing data for ClientErrors
#[derive(Debug, Clone, PartialEq)]
pub enum ClientError {
    /// Catch-all
    Message(String),
    /// 404
    NotFound(String),
}

impl error::Error for ClientError {
    fn cause(&self) -> Option<&dyn error::Error> {
        None
    }
}

impl fmt::Display for ClientError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ClientError::Message(s) => write!(f, "{}", s),
            ClientError::NotFound(s) => write!(f, "HTTP path not matched: {}", s),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::SerializeError(ref s) => fmt::Display::fmt(s, f),
            Error::DeserializeError(ref s) => fmt::Display::fmt(s, f),
            Error::ReadError(ref io) => fmt::Display::fmt(io, f),
            Error::WriteError(ref io) => fmt::Display::fmt(io, f),
            Error::UnderflowError(ref s) => fmt::Display::fmt(s, f),
            Error::OverflowError(ref s) => fmt::Display::fmt(s, f),
            Error::WrongProtocolFamily => write!(f, "Improper use of protocol family"),
            Error::ArrayTooLong => write!(f, "Array too long"),
            Error::RecvTimeout => write!(f, "Packet receive timeout"),
            Error::SigningError(ref s) => fmt::Display::fmt(s, f),
            Error::VerifyingError(ref s) => fmt::Display::fmt(s, f),
            Error::TemporarilyDrained => {
                write!(f, "Temporarily out of bytes to read; try again later")
            }
            Error::PermanentlyDrained => write!(f, "Out of bytes to read"),
            Error::FilesystemError => write!(f, "Disk I/O error"),
            Error::DBError(ref e) => fmt::Display::fmt(e, f),
            Error::SocketMutexPoisoned => write!(f, "socket mutex was poisoned"),
            Error::SocketNotConnectedToPeer => write!(f, "not connected to peer"),
            Error::ConnectionBroken => write!(f, "connection to peer node is broken"),
            Error::ConnectionError => write!(f, "connection to peer could not be (re-)established"),
            Error::OutboxOverflow => write!(f, "too many outgoing messages queued"),
            Error::InboxOverflow => write!(f, "too many messages pending"),
            Error::SendError(ref s) => fmt::Display::fmt(s, f),
            Error::RecvError(ref s) => fmt::Display::fmt(s, f),
            Error::InvalidMessage => write!(f, "invalid message (malformed or bad signature)"),
            Error::InvalidHandle => write!(f, "invalid network handle"),
            Error::FullHandle => write!(f, "network handle is full and needs to be drained"),
            Error::InvalidHandshake => write!(f, "invalid handshake from remote peer"),
            Error::StaleNeighbor => write!(f, "neighbor is too far behind the chain tip"),
            Error::NoSuchNeighbor => write!(f, "no such neighbor"),
            Error::BindError => write!(f, "Failed to bind to the given address"),
            Error::PollError => write!(f, "Failed to poll"),
            Error::AcceptError => write!(f, "Failed to accept connection"),
            Error::RegisterError => write!(f, "Failed to register socket with poller"),
            Error::SocketError => write!(f, "Socket error"),
            Error::NotConnected => write!(f, "Not connected to peer network"),
            Error::PeerNotConnected => write!(f, "Remote peer is not connected to us"),
            Error::TooManyPeers => write!(f, "Too many peer connections open"),
            Error::AlreadyConnected(ref _id, ref _nk) => write!(f, "Peer already connected"),
            Error::InProgress => write!(f, "Message already in progress"),
            Error::Denied => write!(f, "Peer is denied"),
            Error::NoDataUrl => write!(f, "No data URL available"),
            Error::PeerThrottled => write!(f, "Peer is transmitting too fast"),
            Error::LookupError(ref s) => fmt::Display::fmt(s, f),
            Error::ChainstateError(ref s) => fmt::Display::fmt(s, f),
            Error::ClarityError(ref e) => fmt::Display::fmt(e, f),
            Error::MARFError(ref e) => fmt::Display::fmt(e, f),
            Error::ClientError(ref e) => write!(f, "ClientError: {}", e),
            Error::CoordinatorClosed => write!(f, "Coordinator hung up"),
            Error::StaleView => write!(f, "State view is stale"),
            Error::ConnectionCycle => write!(f, "Tried to connect to myself"),
            Error::NotFoundError => write!(f, "Requested data not found"),
            Error::Transient(ref s) => write!(f, "Transient network error: {}", s),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Error::SerializeError(ref _s) => None,
            Error::ReadError(ref io) => Some(io),
            Error::DeserializeError(ref _s) => None,
            Error::WriteError(ref io) => Some(io),
            Error::UnderflowError(ref _s) => None,
            Error::OverflowError(ref _s) => None,
            Error::WrongProtocolFamily => None,
            Error::ArrayTooLong => None,
            Error::RecvTimeout => None,
            Error::SigningError(ref _s) => None,
            Error::VerifyingError(ref _s) => None,
            Error::TemporarilyDrained => None,
            Error::PermanentlyDrained => None,
            Error::FilesystemError => None,
            Error::DBError(ref e) => Some(e),
            Error::SocketMutexPoisoned => None,
            Error::SocketNotConnectedToPeer => None,
            Error::ConnectionBroken => None,
            Error::ConnectionError => None,
            Error::OutboxOverflow => None,
            Error::InboxOverflow => None,
            Error::SendError(ref _s) => None,
            Error::RecvError(ref _s) => None,
            Error::InvalidMessage => None,
            Error::InvalidHandle => None,
            Error::FullHandle => None,
            Error::InvalidHandshake => None,
            Error::StaleNeighbor => None,
            Error::NoSuchNeighbor => None,
            Error::BindError => None,
            Error::PollError => None,
            Error::AcceptError => None,
            Error::RegisterError => None,
            Error::SocketError => None,
            Error::NotConnected => None,
            Error::PeerNotConnected => None,
            Error::TooManyPeers => None,
            Error::AlreadyConnected(ref _id, ref _nk) => None,
            Error::InProgress => None,
            Error::Denied => None,
            Error::NoDataUrl => None,
            Error::PeerThrottled => None,
            Error::LookupError(ref _s) => None,
            Error::ChainstateError(ref _s) => None,
            Error::ClientError(ref e) => Some(e),
            Error::ClarityError(ref e) => Some(e),
            Error::MARFError(ref e) => Some(e),
            Error::CoordinatorClosed => None,
            Error::StaleView => None,
            Error::ConnectionCycle => None,
            Error::NotFoundError => None,
            Error::Transient(ref _s) => None,
        }
    }
}

impl From<chain_error> for Error {
    fn from(e: chain_error) -> Error {
        match e {
            chain_error::InvalidStacksBlock(s) => {
                Error::ChainstateError(format!("Invalid stacks block: {}", s))
            }
            chain_error::InvalidStacksMicroblock(msg, hash) => {
                Error::ChainstateError(format!("Invalid stacks microblock {:?}: {}", hash, msg))
            }
            chain_error::InvalidStacksTransaction(s, _) => {
                Error::ChainstateError(format!("Invalid stacks transaction: {}", s))
            }
            chain_error::PostConditionFailed(s) => {
                Error::ChainstateError(format!("Postcondition failed: {}", s))
            }
            chain_error::ClarityError(e) => Error::ClarityError(e),
            chain_error::DBError(e) => Error::DBError(e),
            chain_error::NetError(e) => e,
            chain_error::MARFError(e) => Error::MARFError(e),
            chain_error::ReadError(e) => Error::ReadError(e),
            chain_error::WriteError(e) => Error::WriteError(e),
            _ => Error::ChainstateError(format!("Stacks chainstate error: {:?}", &e)),
        }
    }
}

impl From<db_error> for Error {
    fn from(e: db_error) -> Error {
        Error::DBError(e)
    }
}

impl From<rusqlite::Error> for Error {
    fn from(e: rusqlite::Error) -> Error {
        Error::DBError(db_error::SqliteError(e))
    }
}

#[cfg(test)]
impl PartialEq for Error {
    /// (make I/O errors comparable for testing purposes)
    fn eq(&self, other: &Self) -> bool {
        let s1 = format!("{:?}", self);
        let s2 = format!("{:?}", other);
        s1 == s2
    }
}

/// A container for an IPv4 or IPv6 address.
/// Rules:
/// -- If this is an IPv6 address, the octets are in network byte order
/// -- If this is an IPv4 address, the octets must encode an IPv6-to-IPv4-mapped address
pub struct PeerAddress([u8; 16]);
impl_array_newtype!(PeerAddress, u8, 16);
impl_array_hexstring_fmt!(PeerAddress);
impl_byte_array_newtype!(PeerAddress, u8, 16);

impl Serialize for PeerAddress {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let inst = format!("{}", self.to_socketaddr(0).ip());
        s.serialize_str(inst.as_str())
    }
}

impl<'de> Deserialize<'de> for PeerAddress {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<PeerAddress, D::Error> {
        let inst = String::deserialize(d)?;
        let ip = inst.parse::<IpAddr>().map_err(de_Error::custom)?;

        Ok(PeerAddress::from_ip(&ip))
    }
}

impl PeerAddress {
    /// Is this an IPv4 address?
    pub fn is_ipv4(&self) -> bool {
        self.ipv4_octets().is_some()
    }

    /// Get the octet representation of this peer address as an IPv4 address.
    /// The last 4 bytes of the list contain the IPv4 address.
    /// This method returns None if the bytes don't encode a valid IPv4-mapped address (i.e. ::ffff:0:0/96)
    pub fn ipv4_octets(&self) -> Option<[u8; 4]> {
        if self.0[0..12]
            != [
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
            ]
        {
            return None;
        }
        let mut ret = [0u8; 4];
        ret.copy_from_slice(&self.0[12..16]);
        Some(ret)
    }

    /// Return the bit representation of this peer address as an IPv4 address, in network byte
    /// order.  Return None if this is not an IPv4 address.
    pub fn ipv4_bits(&self) -> Option<u32> {
        let octets_opt = self.ipv4_octets();
        if octets_opt.is_none() {
            return None;
        }

        let octets = octets_opt.unwrap();
        Some(
            ((octets[0] as u32) << 24)
                | ((octets[1] as u32) << 16)
                | ((octets[2] as u32) << 8)
                | (octets[3] as u32),
        )
    }

    /// Convert to SocketAddr
    pub fn to_socketaddr(&self, port: u16) -> SocketAddr {
        if self.is_ipv4() {
            SocketAddr::new(
                IpAddr::V4(Ipv4Addr::new(
                    self.0[12], self.0[13], self.0[14], self.0[15],
                )),
                port,
            )
        } else {
            let addr_words: [u16; 8] = [
                ((self.0[0] as u16) << 8) | (self.0[1] as u16),
                ((self.0[2] as u16) << 8) | (self.0[3] as u16),
                ((self.0[4] as u16) << 8) | (self.0[5] as u16),
                ((self.0[6] as u16) << 8) | (self.0[7] as u16),
                ((self.0[8] as u16) << 8) | (self.0[9] as u16),
                ((self.0[10] as u16) << 8) | (self.0[11] as u16),
                ((self.0[12] as u16) << 8) | (self.0[13] as u16),
                ((self.0[14] as u16) << 8) | (self.0[15] as u16),
            ];

            SocketAddr::new(
                IpAddr::V6(Ipv6Addr::new(
                    addr_words[0],
                    addr_words[1],
                    addr_words[2],
                    addr_words[3],
                    addr_words[4],
                    addr_words[5],
                    addr_words[6],
                    addr_words[7],
                )),
                port,
            )
        }
    }

    /// Convert from socket address
    pub fn from_socketaddr(addr: &SocketAddr) -> PeerAddress {
        PeerAddress::from_ip(&addr.ip())
    }

    /// Convert from IP address
    pub fn from_ip(addr: &IpAddr) -> PeerAddress {
        match addr {
            IpAddr::V4(ref addr) => {
                let octets = addr.octets();
                PeerAddress([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
                    octets[0], octets[1], octets[2], octets[3],
                ])
            }
            IpAddr::V6(ref addr) => {
                let words = addr.segments();
                PeerAddress([
                    (words[0] >> 8) as u8,
                    (words[0] & 0xff) as u8,
                    (words[1] >> 8) as u8,
                    (words[1] & 0xff) as u8,
                    (words[2] >> 8) as u8,
                    (words[2] & 0xff) as u8,
                    (words[3] >> 8) as u8,
                    (words[3] & 0xff) as u8,
                    (words[4] >> 8) as u8,
                    (words[4] & 0xff) as u8,
                    (words[5] >> 8) as u8,
                    (words[5] & 0xff) as u8,
                    (words[6] >> 8) as u8,
                    (words[6] & 0xff) as u8,
                    (words[7] >> 8) as u8,
                    (words[7] & 0xff) as u8,
                ])
            }
        }
    }

    /// Convert from ipv4 octets
    pub fn from_ipv4(o1: u8, o2: u8, o3: u8, o4: u8) -> PeerAddress {
        PeerAddress([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, o1, o2, o3, o4,
        ])
    }

    /// Is this the any-network address?  i.e. 0.0.0.0 (v4) or :: (v6)?
    pub fn is_anynet(&self) -> bool {
        self.0 == [0x00; 16] || self == &PeerAddress::from_ipv4(0, 0, 0, 0)
    }

    /// Is this a private IP address?
    pub fn is_in_private_range(&self) -> bool {
        if self.is_ipv4() {
            // 10.0.0.0/8, 172.16.0.0/12, or 192.168.0.0/16
            self.0[12] == 10
                || (self.0[12] == 172 && self.0[13] >= 16 && self.0[13] <= 31)
                || (self.0[12] == 192 && self.0[13] == 168)
        } else {
            self.0[0] >= 0xfc
        }
    }
}

pub const STACKS_PUBLIC_KEY_ENCODED_SIZE: u32 = 33;

/// supported HTTP content types
#[derive(Debug, Clone, PartialEq)]
pub enum HttpContentType {
    Bytes,
    Text,
    JSON,
}

impl fmt::Display for HttpContentType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl HttpContentType {
    pub fn as_str(&self) -> &'static str {
        match *self {
            HttpContentType::Bytes => "application/octet-stream",
            HttpContentType::Text => "text/plain",
            HttpContentType::JSON => "application/json",
        }
    }
}

impl FromStr for HttpContentType {
    type Err = codec_error;

    fn from_str(header: &str) -> Result<HttpContentType, codec_error> {
        let s = header.to_string().to_lowercase();
        if s == "application/octet-stream" {
            Ok(HttpContentType::Bytes)
        } else if s == "text/plain" {
            Ok(HttpContentType::Text)
        } else if s == "application/json" {
            Ok(HttpContentType::JSON)
        } else {
            Err(codec_error::DeserializeError(
                "Unsupported HTTP content type".to_string(),
            ))
        }
    }
}

/// HTTP request preamble
#[derive(Debug, Clone, PartialEq)]
pub struct HttpRequestPreamble {
    pub version: HttpVersion,
    pub verb: String,
    pub path: String,
    pub host: PeerHost,
    pub content_type: Option<HttpContentType>,
    pub content_length: Option<u32>,
    pub keep_alive: bool,
    pub headers: HashMap<String, String>,
}

/// HTTP response preamble
#[derive(Debug, Clone, PartialEq)]
pub struct HttpResponsePreamble {
    pub status_code: u16,
    pub reason: String,
    pub keep_alive: bool,
    pub content_length: Option<u32>, // if not given, then content will be transfer-encoed: chunked
    pub content_type: HttpContentType, // required header
    pub request_id: u32,             // X-Request-ID
    pub headers: HashMap<String, String>,
}

/// Maximum size an HTTP request or response preamble can be (within reason)
pub const HTTP_PREAMBLE_MAX_ENCODED_SIZE: u32 = 4096;
pub const HTTP_PREAMBLE_MAX_NUM_HEADERS: usize = 64;

/// P2P message preamble -- included in all p2p network messages
#[derive(Debug, Clone, PartialEq)]
pub struct Preamble {
    pub peer_version: u32,                           // software version
    pub network_id: u32,                             // mainnet, testnet, etc.
    pub seq: u32, // message sequence number -- pairs this message to a request
    pub burn_block_height: u64, // last-seen block height (at chain tip)
    pub burn_block_hash: BurnchainHeaderHash, // hash of the last-seen burn block
    pub burn_stable_block_height: u64, // latest stable block height (e.g. chain tip minus 7)
    pub burn_stable_block_hash: BurnchainHeaderHash, // latest stable burnchain header hash.
    pub additional_data: u32, // RESERVED; pointer to additional data (should be all 0's if not used)
    pub signature: MessageSignature, // signature from the peer that sent this
    pub payload_len: u32,     // length of the following payload, including relayers vector
}

/// Request for a block inventory or a list of blocks.
/// Aligned to a PoX reward cycle.
#[derive(Debug, Clone, PartialEq)]
pub struct GetBlocksInv {
    pub consensus_hash: ConsensusHash, // consensus hash at the start of the reward cycle
    pub num_blocks: u16,               // number of blocks to ask for
}

/// A bit vector that describes which block and microblock data node has data for in a given burn
/// chain block range.  Sent in reply to a GetBlocksInv.
#[derive(Debug, Clone, PartialEq)]
pub struct BlocksInvData {
    pub bitlen: u16, // number of bits represented in bitvec (not to exceed PoX reward cycle length).  Bits correspond to sortitions on the canonical burn chain fork.
    pub block_bitvec: Vec<u8>, // bitmap of which blocks the peer has, in sortition order.  block_bitvec[i] & (1 << j) != 0 means that this peer has the block for sortition 8*i + j
    pub microblocks_bitvec: Vec<u8>, // bitmap of which confirmed micrblocks the peer has, in sortition order.  microblocks_bitvec[i] & (1 << j) != 0 means that this peer has the microblocks produced by sortition 8*i + j
}

/// Request for a PoX bitvector range.
/// Requests bits for [start_reward_cycle, start_reward_cycle + num_anchor_blocks)
#[derive(Debug, Clone, PartialEq)]
pub struct GetPoxInv {
    pub consensus_hash: ConsensusHash,
    pub num_cycles: u16, // how many bits to expect
}

/// Response to a GetPoxInv request
#[derive(Debug, Clone, PartialEq)]
pub struct PoxInvData {
    pub bitlen: u16,         // number of bits represented
    pub pox_bitvec: Vec<u8>, // a bit will be '1' if the node knows for sure the status of its reward cycle's anchor block; 0 if not.
}

/// Blocks pushed
#[derive(Debug, Clone, PartialEq)]
pub struct BlocksData {
    pub blocks: Vec<(ConsensusHash, StacksBlock)>,
}

/// Microblocks pushed
#[derive(Debug, Clone, PartialEq)]
pub struct MicroblocksData {
    pub index_anchor_block: StacksBlockId,
    pub microblocks: Vec<StacksMicroblock>,
}

/// Block available hint
#[derive(Debug, Clone, PartialEq)]
pub struct BlocksAvailableData {
    pub available: Vec<(ConsensusHash, BurnchainHeaderHash)>,
}

/// A descriptor of a peer
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NeighborAddress {
    #[serde(rename = "ip")]
    pub addrbytes: PeerAddress,
    pub port: u16,
    pub public_key_hash: Hash160, // used as a hint; useful for when a node trusts another node to be honest about this
}

impl fmt::Display for NeighborAddress {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{:?}://{:?}",
            &self.public_key_hash,
            &self.addrbytes.to_socketaddr(self.port)
        )
    }
}

impl fmt::Debug for NeighborAddress {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{:?}://{:?}",
            &self.public_key_hash,
            &self.addrbytes.to_socketaddr(self.port)
        )
    }
}

impl NeighborAddress {
    pub fn clear_public_key(&mut self) -> () {
        self.public_key_hash = Hash160([0u8; 20]);
    }

    pub fn from_neighbor_key(nk: NeighborKey, pkh: Hash160) -> NeighborAddress {
        NeighborAddress {
            addrbytes: nk.addrbytes,
            port: nk.port,
            public_key_hash: pkh,
        }
    }
}

/// A descriptor of a list of known peers
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NeighborsData {
    pub neighbors: Vec<NeighborAddress>,
}

/// Handshake request -- this is the first message sent to a peer.
/// The remote peer will reply a HandshakeAccept with just a preamble
/// if the peer accepts.  Otherwise it will get a HandshakeReject with just
/// a preamble.
///
/// To keep peer knowledge fresh, nodes will send handshakes to each other
/// as heartbeat messages.
#[derive(Debug, Clone, PartialEq)]
pub struct HandshakeData {
    pub addrbytes: PeerAddress,
    pub port: u16,
    pub services: u16, // bit field representing services this node offers
    pub node_public_key: StacksPublicKeyBuffer,
    pub expire_block_height: u64, // burn block height after which this node's key will be revoked,
    pub data_url: UrlString,
}

#[repr(u8)]
pub enum ServiceFlags {
    RELAY = 0x01,
    RPC = 0x02,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HandshakeAcceptData {
    pub handshake: HandshakeData, // this peer's handshake information
    pub heartbeat_interval: u32,  // hint as to how long this peer will remember you
}

#[derive(Debug, Clone, PartialEq)]
pub struct NackData {
    pub error_code: u32,
}
pub mod NackErrorCodes {
    pub const HandshakeRequired: u32 = 1;
    pub const NoSuchBurnchainBlock: u32 = 2;
    pub const Throttled: u32 = 3;
    pub const InvalidPoxFork: u32 = 4;
    pub const InvalidMessage: u32 = 5;
}

#[derive(Debug, Clone, PartialEq)]
pub struct PingData {
    pub nonce: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PongData {
    pub nonce: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct NatPunchData {
    pub addrbytes: PeerAddress,
    pub port: u16,
    pub nonce: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RelayData {
    pub peer: NeighborAddress,
    pub seq: u32,
}

/// All P2P message types
#[derive(Debug, Clone, PartialEq)]
pub enum StacksMessageType {
    Handshake(HandshakeData),
    HandshakeAccept(HandshakeAcceptData),
    HandshakeReject,
    GetNeighbors,
    Neighbors(NeighborsData),
    GetBlocksInv(GetBlocksInv),
    BlocksInv(BlocksInvData),
    GetPoxInv(GetPoxInv),
    PoxInv(PoxInvData),
    BlocksAvailable(BlocksAvailableData),
    MicroblocksAvailable(BlocksAvailableData),
    Blocks(BlocksData),
    Microblocks(MicroblocksData),
    Transaction(StacksTransaction),
    Nack(NackData),
    Ping(PingData),
    Pong(PongData),
    NatPunchRequest(u32),
    NatPunchReply(NatPunchData),
}

/// Peer address variants
#[derive(Clone, PartialEq)]
pub enum PeerHost {
    DNS(String, u16),
    IP(PeerAddress, u16),
}

impl fmt::Display for PeerHost {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PeerHost::DNS(ref s, ref p) => write!(f, "{}:{}", s, p),
            PeerHost::IP(ref a, ref p) => write!(f, "{}", a.to_socketaddr(*p)),
        }
    }
}

impl fmt::Debug for PeerHost {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PeerHost::DNS(ref s, ref p) => write!(f, "PeerHost::DNS({},{})", s, p),
            PeerHost::IP(ref a, ref p) => write!(f, "PeerHost::IP({:?},{})", a, p),
        }
    }
}

impl Hash for PeerHost {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match *self {
            PeerHost::DNS(ref name, ref port) => {
                "DNS".hash(state);
                name.hash(state);
                port.hash(state);
            }
            PeerHost::IP(ref addrbytes, ref port) => {
                "IP".hash(state);
                addrbytes.hash(state);
                port.hash(state);
            }
        }
    }
}

impl PeerHost {
    pub fn hostname(&self) -> String {
        match *self {
            PeerHost::DNS(ref s, _) => s.clone(),
            PeerHost::IP(ref a, ref p) => format!("{}", a.to_socketaddr(*p).ip()),
        }
    }

    pub fn port(&self) -> u16 {
        match *self {
            PeerHost::DNS(_, ref p) => *p,
            PeerHost::IP(_, ref p) => *p,
        }
    }

    pub fn from_host_port(host: String, port: u16) -> PeerHost {
        // try as IP, and fall back to DNS
        match host.parse::<IpAddr>() {
            Ok(addr) => PeerHost::IP(PeerAddress::from_ip(&addr), port),
            Err(_) => PeerHost::DNS(host, port),
        }
    }

    pub fn from_socketaddr(socketaddr: &SocketAddr) -> PeerHost {
        PeerHost::IP(PeerAddress::from_socketaddr(socketaddr), socketaddr.port())
    }

    pub fn try_from_url(url_str: &UrlString) -> Option<PeerHost> {
        let url = match url_str.parse_to_block_url() {
            Ok(url) => url,
            Err(_e) => {
                return None;
            }
        };

        let port = match url.port_or_known_default() {
            Some(port) => port,
            None => {
                return None;
            }
        };

        match url.host() {
            Some(url::Host::Domain(name)) => Some(PeerHost::DNS(name.to_string(), port)),
            Some(url::Host::Ipv4(addr)) => Some(PeerHost::from_socketaddr(&SocketAddr::new(
                IpAddr::V4(addr),
                port,
            ))),
            Some(url::Host::Ipv6(addr)) => Some(PeerHost::from_socketaddr(&SocketAddr::new(
                IpAddr::V6(addr),
                port,
            ))),
            None => None,
        }
    }
}

/// The data we return on GET /v2/info
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RPCPeerInfoData {
    pub peer_version: u32,
    pub pox_consensus: ConsensusHash,
    pub burn_block_height: u64,
    pub stable_pox_consensus: ConsensusHash,
    pub stable_burn_block_height: u64,
    pub server_version: String,
    pub network_id: u32,
    pub parent_network_id: u32,
    pub stacks_tip_height: u64,
    pub stacks_tip: BlockHeaderHash,
    pub stacks_tip_consensus_hash: ConsensusHash,
    pub genesis_chainstate_hash: Sha256Sum,
    pub unanchored_tip: StacksBlockId,
    pub unanchored_seq: u16,
    pub exit_at_block_height: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RPCPoxCurrentCycleInfo {
    pub id: u64,
    pub min_threshold_ustx: u64,
    pub stacked_ustx: u64,
    pub is_pox_active: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RPCPoxNextCycleInfo {
    pub id: u64,
    pub min_threshold_ustx: u64,
    pub min_increment_ustx: u64,
    pub stacked_ustx: u64,
    pub prepare_phase_start_block_height: u64,
    pub blocks_until_prepare_phase: i64,
    pub reward_phase_start_block_height: u64,
    pub blocks_until_reward_phase: u64,
    pub ustx_until_pox_rejection: u64,
}

/// The data we return on GET /v2/pox
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RPCPoxInfoData {
    pub contract_id: String,
    pub pox_activation_threshold_ustx: u64,
    pub first_burnchain_block_height: u64,
    pub prepare_phase_block_length: u64,
    pub reward_phase_block_length: u64,
    pub reward_slots: u64,
    pub rejection_fraction: u64,
    pub total_liquid_supply_ustx: u64,
    pub current_cycle: RPCPoxCurrentCycleInfo,
    pub next_cycle: RPCPoxNextCycleInfo,

    // below are included for backwards-compatibility
    pub min_amount_ustx: u64,
    pub prepare_cycle_length: u64,
    pub reward_cycle_id: u64,
    pub reward_cycle_length: u64,
    pub rejection_votes_left_required: u64,
    pub next_reward_cycle_in: u64,
}

#[derive(Debug, Clone, PartialEq, Copy, Hash)]
#[repr(u8)]
pub enum HttpVersion {
    Http10 = 0x10,
    Http11 = 0x11,
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub struct HttpRequestMetadata {
    pub version: HttpVersion,
    pub peer: PeerHost,
    pub keep_alive: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MapEntryResponse {
    pub data: String,
    #[serde(rename = "proof")]
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub marf_proof: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ContractSrcResponse {
    pub source: String,
    pub publish_height: u32,
    #[serde(rename = "proof")]
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub marf_proof: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GetIsTraitImplementedResponse {
    pub is_implemented: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CallReadOnlyResponse {
    pub okay: bool,
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<String>,
    #[serde(default)]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cause: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AccountEntryResponse {
    pub balance: String,
    pub locked: String,
    pub unlock_height: u64,
    pub nonce: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub balance_proof: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub nonce_proof: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UnconfirmedTransactionStatus {
    Microblock {
        block_hash: BlockHeaderHash,
        seq: u16,
    },
    Mempool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct UnconfirmedTransactionResponse {
    pub tx: String,
    pub status: UnconfirmedTransactionStatus,
}

#[derive(Serialize, Deserialize)]
pub struct PostTransactionRequestBody {
    pub tx: String,
    pub attachment: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct GetAttachmentResponse {
    pub attachment: Attachment,
}

impl Serialize for GetAttachmentResponse {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let hex_encoded = to_hex(&self.attachment.content[..]);
        s.serialize_str(hex_encoded.as_str())
    }
}

impl<'de> Deserialize<'de> for GetAttachmentResponse {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<GetAttachmentResponse, D::Error> {
        let payload = String::deserialize(d)?;
        let hex_encoded = payload.parse::<String>().map_err(de_Error::custom)?;
        let bytes = hex_bytes(&hex_encoded).map_err(de_Error::custom)?;
        let attachment = Attachment::new(bytes);
        Ok(GetAttachmentResponse { attachment })
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GetAttachmentsInvResponse {
    pub block_id: StacksBlockId,
    pub pages: Vec<AttachmentPage>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AttachmentPage {
    pub index: u32,
    pub inventory: Vec<u8>,
}

/// Request ID to use or expect from non-Stacks HTTP clients.
/// In particular, if a HTTP response does not contain the x-request-id header, then it's assumed
/// to be this value.  This is needed to support fetching immutables like block and microblock data
/// from non-Stacks nodes (like Gaia hubs, CDNs, vanilla HTTP servers, and so on).
pub const HTTP_REQUEST_ID_RESERVED: u32 = 0;

impl HttpRequestMetadata {
    pub fn new(host: String, port: u16) -> HttpRequestMetadata {
        HttpRequestMetadata {
            version: HttpVersion::Http11,
            peer: PeerHost::from_host_port(host, port),
            keep_alive: true,
        }
    }

    pub fn from_host(peer_host: PeerHost) -> HttpRequestMetadata {
        HttpRequestMetadata {
            version: HttpVersion::Http11,
            peer: peer_host,
            keep_alive: true,
        }
    }

    pub fn from_preamble(preamble: &HttpRequestPreamble) -> HttpRequestMetadata {
        HttpRequestMetadata {
            version: preamble.version,
            peer: preamble.host.clone(),
            keep_alive: preamble.keep_alive,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct CallReadOnlyRequestBody {
    pub sender: String,
    pub arguments: Vec<String>,
}

/// Items in the NeighborsInfo -- combines NeighborKey and NeighborAddress
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RPCNeighbor {
    pub network_id: u32,
    pub peer_version: u32,
    #[serde(rename = "ip")]
    pub addrbytes: PeerAddress,
    pub port: u16,
    pub public_key_hash: Hash160,
    pub authenticated: bool,
}

impl RPCNeighbor {
    pub fn from_neighbor_key_and_pubkh(nk: NeighborKey, pkh: Hash160, auth: bool) -> RPCNeighbor {
        RPCNeighbor {
            network_id: nk.network_id,
            peer_version: nk.peer_version,
            addrbytes: nk.addrbytes,
            port: nk.port,
            public_key_hash: pkh,
            authenticated: auth,
        }
    }
}

/// Struct given back from a call to `/v2/neighbors`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RPCNeighborsInfo {
    pub sample: Vec<RPCNeighbor>,
    pub inbound: Vec<RPCNeighbor>,
    pub outbound: Vec<RPCNeighbor>,
}

/// All HTTP request paths we support, and the arguments they carry in their paths
#[derive(Debug, Clone, PartialEq)]
pub enum HttpRequestType {
    GetInfo(HttpRequestMetadata),
    GetPoxInfo(HttpRequestMetadata, Option<StacksBlockId>),
    GetNeighbors(HttpRequestMetadata),
    GetBlock(HttpRequestMetadata, StacksBlockId),
    GetMicroblocksIndexed(HttpRequestMetadata, StacksBlockId),
    GetMicroblocksConfirmed(HttpRequestMetadata, StacksBlockId),
    GetMicroblocksUnconfirmed(HttpRequestMetadata, StacksBlockId, u16),
    GetTransactionUnconfirmed(HttpRequestMetadata, Txid),
    PostTransaction(HttpRequestMetadata, StacksTransaction, Option<Attachment>),
    PostBlock(HttpRequestMetadata, ConsensusHash, StacksBlock),
    PostMicroblock(HttpRequestMetadata, StacksMicroblock, Option<StacksBlockId>),
    GetAccount(
        HttpRequestMetadata,
        PrincipalData,
        Option<StacksBlockId>,
        bool,
    ),
    GetMapEntry(
        HttpRequestMetadata,
        StacksAddress,
        ContractName,
        ClarityName,
        Value,
        Option<StacksBlockId>,
        bool,
    ),
    CallReadOnlyFunction(
        HttpRequestMetadata,
        StacksAddress,
        ContractName,
        PrincipalData,
        ClarityName,
        Vec<Value>,
        Option<StacksBlockId>,
    ),
    GetTransferCost(HttpRequestMetadata),
    GetContractSrc(
        HttpRequestMetadata,
        StacksAddress,
        ContractName,
        Option<StacksBlockId>,
        bool,
    ),
    GetContractABI(
        HttpRequestMetadata,
        StacksAddress,
        ContractName,
        Option<StacksBlockId>,
    ),
    OptionsPreflight(HttpRequestMetadata, String),
    GetAttachment(HttpRequestMetadata, Hash160),
    GetAttachmentsInv(HttpRequestMetadata, StacksBlockId, HashSet<u32>),
    GetIsTraitImplemented(
        HttpRequestMetadata,
        StacksAddress,
        ContractName,
        TraitIdentifier,
        Option<StacksBlockId>,
    ),
    /// catch-all for any errors we should surface from parsing
    ClientError(HttpRequestMetadata, ClientError),
}

/// The fields that Actually Matter to http responses
#[derive(Debug, Clone, PartialEq)]
pub struct HttpResponseMetadata {
    pub client_version: HttpVersion,
    pub client_keep_alive: bool,
    pub request_id: u32,
    pub content_length: Option<u32>,
}

impl HttpResponseMetadata {
    pub fn make_request_id() -> u32 {
        let mut rng = thread_rng();
        let mut request_id = HTTP_REQUEST_ID_RESERVED;
        while request_id == HTTP_REQUEST_ID_RESERVED {
            request_id = rng.next_u32();
        }
        request_id
    }

    pub fn new(
        client_version: HttpVersion,
        request_id: u32,
        content_length: Option<u32>,
        client_keep_alive: bool,
    ) -> HttpResponseMetadata {
        HttpResponseMetadata {
            client_version: client_version,
            client_keep_alive: client_keep_alive,
            request_id: request_id,
            content_length: content_length,
        }
    }

    pub fn from_preamble(
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
    ) -> HttpResponseMetadata {
        HttpResponseMetadata {
            client_version: request_version,
            client_keep_alive: preamble.keep_alive,
            request_id: preamble.request_id,
            content_length: preamble.content_length.clone(),
        }
    }

    pub fn empty_error() -> HttpResponseMetadata {
        HttpResponseMetadata {
            client_version: HttpVersion::Http11,
            client_keep_alive: false,
            request_id: HttpResponseMetadata::make_request_id(),
            content_length: Some(0),
        }
    }
}

impl From<&HttpRequestType> for HttpResponseMetadata {
    fn from(req: &HttpRequestType) -> HttpResponseMetadata {
        let metadata = req.metadata();
        HttpResponseMetadata::new(
            metadata.version,
            HttpResponseMetadata::make_request_id(),
            None,
            metadata.keep_alive,
        )
    }
}

/// All data-plane message types a peer can reply with.
#[derive(Debug, Clone, PartialEq)]
pub enum HttpResponseType {
    PeerInfo(HttpResponseMetadata, RPCPeerInfoData),
    PoxInfo(HttpResponseMetadata, RPCPoxInfoData),
    Neighbors(HttpResponseMetadata, RPCNeighborsInfo),
    Block(HttpResponseMetadata, StacksBlock),
    BlockStream(HttpResponseMetadata),
    Microblocks(HttpResponseMetadata, Vec<StacksMicroblock>),
    MicroblockStream(HttpResponseMetadata),
    TransactionID(HttpResponseMetadata, Txid),
    StacksBlockAccepted(HttpResponseMetadata, StacksBlockId, bool),
    MicroblockHash(HttpResponseMetadata, BlockHeaderHash),
    TokenTransferCost(HttpResponseMetadata, u64),
    GetMapEntry(HttpResponseMetadata, MapEntryResponse),
    CallReadOnlyFunction(HttpResponseMetadata, CallReadOnlyResponse),
    GetAccount(HttpResponseMetadata, AccountEntryResponse),
    GetContractABI(HttpResponseMetadata, ContractInterface),
    GetContractSrc(HttpResponseMetadata, ContractSrcResponse),
    GetIsTraitImplemented(HttpResponseMetadata, GetIsTraitImplementedResponse),
    UnconfirmedTransaction(HttpResponseMetadata, UnconfirmedTransactionResponse),
    GetAttachment(HttpResponseMetadata, GetAttachmentResponse),
    GetAttachmentsInv(HttpResponseMetadata, GetAttachmentsInvResponse),
    OptionsPreflight(HttpResponseMetadata),
    // peer-given error responses
    BadRequest(HttpResponseMetadata, String),
    BadRequestJSON(HttpResponseMetadata, serde_json::Value),
    Unauthorized(HttpResponseMetadata, String),
    PaymentRequired(HttpResponseMetadata, String),
    Forbidden(HttpResponseMetadata, String),
    NotFound(HttpResponseMetadata, String),
    ServerError(HttpResponseMetadata, String),
    ServiceUnavailable(HttpResponseMetadata, String),
    Error(HttpResponseMetadata, u16, String),
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum UrlScheme {
    Http,
    Https,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum StacksMessageID {
    Handshake = 0,
    HandshakeAccept = 1,
    HandshakeReject = 2,
    GetNeighbors = 3,
    Neighbors = 4,
    GetBlocksInv = 5,
    BlocksInv = 6,
    GetPoxInv = 7,
    PoxInv = 8,
    BlocksAvailable = 9,
    MicroblocksAvailable = 10,
    Blocks = 11,
    Microblocks = 12,
    Transaction = 13,
    Nack = 14,
    Ping = 15,
    Pong = 16,
    NatPunchRequest = 17,
    NatPunchReply = 18,
    Reserved = 255,
}

/// Message type for all P2P Stacks network messages
#[derive(Debug, Clone, PartialEq)]
pub struct StacksMessage {
    pub preamble: Preamble,
    pub relayers: Vec<RelayData>,
    pub payload: StacksMessageType,
}

/// Message type for HTTP
#[derive(Debug, Clone, PartialEq)]
pub enum StacksHttpMessage {
    Request(HttpRequestType),
    Response(HttpResponseType),
}

/// HTTP message preamble
#[derive(Debug, Clone, PartialEq)]
pub enum StacksHttpPreamble {
    Request(HttpRequestPreamble),
    Response(HttpResponsePreamble),
}

/// Network messages implement this to have multiple messages in flight.
pub trait MessageSequence {
    fn request_id(&self) -> u32;
    fn get_message_name(&self) -> &'static str;
}

pub trait ProtocolFamily {
    type Preamble: StacksMessageCodec + Send + Sync + Clone + PartialEq + std::fmt::Debug;
    type Message: MessageSequence + Send + Sync + Clone + PartialEq + std::fmt::Debug;

    /// Return the maximum possible length of the serialized Preamble type
    fn preamble_size_hint(&mut self) -> usize;

    /// Determine how long the message payload will be, given the Preamble (may return None if the
    /// payload length cannot be determined solely by the Preamble).
    fn payload_len(&mut self, preamble: &Self::Preamble) -> Option<usize>;

    /// Given a byte buffer of a length at last that of the value returned by preamble_size_hint,
    /// parse a Preamble and return both the Preamble and the number of bytes actually consumed by it.
    fn read_preamble(&mut self, buf: &[u8]) -> Result<(Self::Preamble, usize), Error>;

    /// Given a preamble and a byte buffer, parse out a message and return both the message and the
    /// number of bytes actually consumed by it.  Only used if the message is _not_ streamed.  The
    /// buf slice is guaranteed to have at least `payload_len()` bytes if `payload_len()` returns
    /// Some(...).
    fn read_payload(
        &mut self,
        preamble: &Self::Preamble,
        buf: &[u8],
    ) -> Result<(Self::Message, usize), Error>;

    /// Given a preamble and a Read, attempt to stream a message.  This will be called if
    /// `payload_len()` returns None.  This method will be repeatedly called with new data until a
    /// message can be obtained; therefore, the ProtocolFamily implementation will need to do its
    /// own bufferring and state-tracking.
    fn stream_payload<R: Read>(
        &mut self,
        preamble: &Self::Preamble,
        fd: &mut R,
    ) -> Result<(Option<(Self::Message, usize)>, usize), Error>;

    /// Given a public key, a preamble, and the yet-to-be-parsed message bytes, verify the message
    /// authenticity.  Not all protocols need to do this.
    fn verify_payload_bytes(
        &mut self,
        key: &StacksPublicKey,
        preamble: &Self::Preamble,
        bytes: &[u8],
    ) -> Result<(), Error>;

    /// Given a Write and a Message, write it out.  This method is also responsible for generating
    /// and writing out a Preamble for its Message.
    fn write_message<W: Write>(&mut self, fd: &mut W, message: &Self::Message)
        -> Result<(), Error>;
}

// these implement the ProtocolFamily trait
#[derive(Debug, Clone, PartialEq)]
pub struct StacksP2P {}

// an array in our protocol can't exceed this many items
pub const ARRAY_MAX_LEN: u32 = u32::max_value();

// maximum number of neighbors in a NeighborsData
pub const MAX_NEIGHBORS_DATA_LEN: u32 = 128;

// number of peers to relay to, depending on outbound or inbound
pub const MAX_BROADCAST_OUTBOUND_RECEIVERS: usize = 8;
pub const MAX_BROADCAST_INBOUND_RECEIVERS: usize = 16;

// maximum number of blocks that can be announced as available
pub const BLOCKS_AVAILABLE_MAX_LEN: u32 = 32;

// maximum number of PoX reward cycles we can ask about
#[cfg(not(test))]
pub const GETPOXINV_MAX_BITLEN: u64 = 4096;
#[cfg(test)]
pub const GETPOXINV_MAX_BITLEN: u64 = 8;

// maximum number of blocks that can be pushed at once (even if the entire message is undersized).
// This bound is needed since it bounds the amount of I/O a peer can be asked to do to validate the
// message.
pub const BLOCKS_PUSHED_MAX: u32 = 32;

impl_byte_array_message_codec!(ConsensusHash, 20);
impl_byte_array_message_codec!(Hash160, 20);
impl_byte_array_message_codec!(BurnchainHeaderHash, 32);
impl_byte_array_message_codec!(BlockHeaderHash, 32);
impl_byte_array_message_codec!(StacksBlockId, 32);
impl_byte_array_message_codec!(MessageSignature, 65);
impl_byte_array_message_codec!(PeerAddress, 16);
impl_byte_array_message_codec!(StacksPublicKeyBuffer, 33);

impl_byte_array_serde!(ConsensusHash);

/// neighbor identifier
#[derive(Clone, Eq, PartialOrd, Ord)]
pub struct NeighborKey {
    pub peer_version: u32,
    pub network_id: u32,
    pub addrbytes: PeerAddress,
    pub port: u16,
}

impl Hash for NeighborKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // ignores peer version and network ID -- we don't accept or deal with messages that have
        // incompatible versions or network IDs in the first place
        let peer_major_version = self.peer_version & 0xff000000;
        peer_major_version.hash(state);
        self.addrbytes.hash(state);
        self.port.hash(state);
    }
}

impl PartialEq for NeighborKey {
    fn eq(&self, other: &NeighborKey) -> bool {
        // only check major version byte in peer_version
        self.network_id == other.network_id
            && (self.peer_version & 0xff000000) == (other.peer_version & 0xff000000)
            && self.addrbytes == other.addrbytes
            && self.port == other.port
    }
}

impl fmt::Display for NeighborKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let peer_version_str = if self.peer_version > 0 {
            format!("{:08x}", self.peer_version)
        } else {
            "UNKNOWN".to_string()
        };
        let network_id_str = if self.network_id > 0 {
            format!("{:08x}", self.network_id)
        } else {
            "UNKNOWN".to_string()
        };
        write!(
            f,
            "{}+{}://{:?}",
            peer_version_str,
            network_id_str,
            &self.addrbytes.to_socketaddr(self.port)
        )
    }
}

impl fmt::Debug for NeighborKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl NeighborKey {
    pub fn empty() -> NeighborKey {
        NeighborKey {
            peer_version: 0,
            network_id: 0,
            addrbytes: PeerAddress([0u8; 16]),
            port: 0,
        }
    }

    pub fn from_neighbor_address(
        peer_version: u32,
        network_id: u32,
        na: &NeighborAddress,
    ) -> NeighborKey {
        NeighborKey {
            peer_version: peer_version,
            network_id: network_id,
            addrbytes: na.addrbytes.clone(),
            port: na.port,
        }
    }
}

/// Entry in the neighbor set
#[derive(Debug, Clone, PartialEq)]
pub struct Neighbor {
    pub addr: NeighborKey,

    // fields below this can change at runtime
    pub public_key: Secp256k1PublicKey,
    pub expire_block: u64,
    pub last_contact_time: u64, // time when we last authenticated with this peer via a Handshake

    pub allowed: i64, // allow deadline (negative == "forever")
    pub denied: i64,  // deny deadline (negative == "forever")

    pub asn: u32, // AS number
    pub org: u32, // organization identifier

    pub in_degree: u32,  // number of peers who list this peer as a neighbor
    pub out_degree: u32, // number of neighbors this peer has
}

impl Neighbor {
    pub fn is_allowed(&self) -> bool {
        self.allowed < 0 || (self.allowed as u64) > get_epoch_time_secs()
    }

    pub fn is_always_allowed(&self) -> bool {
        self.allowed < 0
    }

    pub fn is_denied(&self) -> bool {
        self.denied < 0 || (self.denied as u64) > get_epoch_time_secs()
    }
}

impl fmt::Display for Neighbor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}@{}", self.public_key.to_hex(), self.addr)
    }
}

pub const NUM_NEIGHBORS: usize = 32;

// maximum number of unconfirmed microblocks can get streamed to us
pub const MAX_MICROBLOCKS_UNCONFIRMED: usize = 1024;

// how long a peer will be denied for if it misbehaves
#[cfg(test)]
pub const DENY_BAN_DURATION: u64 = 30; // seconds
#[cfg(not(test))]
pub const DENY_BAN_DURATION: u64 = 86400; // seconds (1 day)

pub const DENY_MIN_BAN_DURATION: u64 = 2;

/// Result of doing network work
pub struct NetworkResult {
    pub download_pox_id: Option<PoxId>, // PoX ID as it was when we begin downloading blocks (set if we have downloaded new blocks)
    pub unhandled_messages: HashMap<NeighborKey, Vec<StacksMessage>>,
    pub blocks: Vec<(ConsensusHash, StacksBlock, u64)>, // blocks we downloaded, and time taken
    pub confirmed_microblocks: Vec<(ConsensusHash, Vec<StacksMicroblock>, u64)>, // confiremd microblocks we downloaded, and time taken
    pub pushed_transactions: HashMap<NeighborKey, Vec<(Vec<RelayData>, StacksTransaction)>>, // all transactions pushed to us and their message relay hints
    pub pushed_blocks: HashMap<NeighborKey, Vec<BlocksData>>, // all blocks pushed to us
    pub pushed_microblocks: HashMap<NeighborKey, Vec<(Vec<RelayData>, MicroblocksData)>>, // all microblocks pushed to us, and the relay hints from the message
    pub uploaded_transactions: Vec<StacksTransaction>, // transactions sent to us by the http server
    pub uploaded_blocks: Vec<BlocksData>,              // blocks sent to us via the http server
    pub uploaded_microblocks: Vec<MicroblocksData>,    // microblocks sent to us by the http server
    pub attachments: Vec<(AttachmentInstance, Attachment)>,
    pub num_state_machine_passes: u64,
    pub num_inv_sync_passes: u64,
    pub num_download_passes: u64,
}

impl NetworkResult {
    pub fn new(
        num_state_machine_passes: u64,
        num_inv_sync_passes: u64,
        num_download_passes: u64,
    ) -> NetworkResult {
        NetworkResult {
            unhandled_messages: HashMap::new(),
            download_pox_id: None,
            blocks: vec![],
            confirmed_microblocks: vec![],
            pushed_transactions: HashMap::new(),
            pushed_blocks: HashMap::new(),
            pushed_microblocks: HashMap::new(),
            uploaded_transactions: vec![],
            uploaded_blocks: vec![],
            uploaded_microblocks: vec![],
            attachments: vec![],
            num_state_machine_passes: num_state_machine_passes,
            num_inv_sync_passes: num_inv_sync_passes,
            num_download_passes: num_download_passes,
        }
    }

    pub fn has_blocks(&self) -> bool {
        self.blocks.len() > 0 || self.pushed_blocks.len() > 0
    }

    pub fn has_microblocks(&self) -> bool {
        self.confirmed_microblocks.len() > 0
            || self.pushed_microblocks.len() > 0
            || self.uploaded_microblocks.len() > 0
    }

    pub fn has_transactions(&self) -> bool {
        self.pushed_transactions.len() > 0 || self.uploaded_transactions.len() > 0
    }

    pub fn has_attachments(&self) -> bool {
        self.attachments.len() > 0
    }

    pub fn transactions(&self) -> Vec<StacksTransaction> {
        self.pushed_transactions
            .values()
            .flat_map(|pushed_txs| pushed_txs.iter().map(|(_, tx)| tx.clone()))
            .chain(self.uploaded_transactions.iter().map(|x| x.clone()))
            .collect()
    }

    pub fn has_data_to_store(&self) -> bool {
        self.has_blocks()
            || self.has_microblocks()
            || self.has_transactions()
            || self.has_attachments()
    }

    pub fn consume_unsolicited(
        &mut self,
        unhandled_messages: HashMap<NeighborKey, Vec<StacksMessage>>,
    ) -> () {
        for (neighbor_key, messages) in unhandled_messages.into_iter() {
            for message in messages.into_iter() {
                match message.payload {
                    StacksMessageType::Blocks(block_data) => {
                        if let Some(blocks_msgs) = self.pushed_blocks.get_mut(&neighbor_key) {
                            blocks_msgs.push(block_data);
                        } else {
                            self.pushed_blocks
                                .insert(neighbor_key.clone(), vec![block_data]);
                        }
                    }
                    StacksMessageType::Microblocks(mblock_data) => {
                        if let Some(mblocks_msgs) = self.pushed_microblocks.get_mut(&neighbor_key) {
                            mblocks_msgs.push((message.relayers, mblock_data));
                        } else {
                            self.pushed_microblocks.insert(
                                neighbor_key.clone(),
                                vec![(message.relayers, mblock_data)],
                            );
                        }
                    }
                    StacksMessageType::Transaction(tx_data) => {
                        if let Some(tx_msgs) = self.pushed_transactions.get_mut(&neighbor_key) {
                            tx_msgs.push((message.relayers, tx_data));
                        } else {
                            self.pushed_transactions
                                .insert(neighbor_key.clone(), vec![(message.relayers, tx_data)]);
                        }
                    }
                    _ => {
                        // forward along
                        if let Some(messages) = self.unhandled_messages.get_mut(&neighbor_key) {
                            messages.push(message);
                        } else {
                            self.unhandled_messages
                                .insert(neighbor_key.clone(), vec![message]);
                        }
                    }
                }
            }
        }
    }

    pub fn consume_http_uploads(&mut self, mut msgs: Vec<StacksMessageType>) -> () {
        for msg in msgs.drain(..) {
            match msg {
                StacksMessageType::Transaction(tx_data) => {
                    self.uploaded_transactions.push(tx_data);
                }
                StacksMessageType::Blocks(block_data) => {
                    self.uploaded_blocks.push(block_data);
                }
                StacksMessageType::Microblocks(mblock_data) => {
                    self.uploaded_microblocks.push(mblock_data);
                }
                _ => {
                    // drop
                    warn!("Dropping unknown HTTP message");
                }
            }
        }
    }
}

pub trait Requestable: std::fmt::Display {
    fn get_url(&self) -> &UrlString;

    fn make_request_type(&self, peer_host: PeerHost) -> HttpRequestType;
}

#[cfg(test)]
pub mod test {
    use std::collections::HashMap;
    use std::fs;
    use std::io;
    use std::io::Cursor;
    use std::io::ErrorKind;
    use std::io::Read;
    use std::io::Write;
    use std::net::*;
    use std::ops::Deref;
    use std::ops::DerefMut;
    use std::sync::mpsc::sync_channel;
    use std::thread;

    use mio;
    use rand;
    use rand::RngCore;

    use address::*;
    use burnchains::bitcoin::address::*;
    use burnchains::bitcoin::keys::*;
    use burnchains::bitcoin::*;
    use burnchains::burnchain::*;
    use burnchains::db::BurnchainDB;
    use burnchains::test::*;
    use burnchains::*;
    use chainstate::burn::db::sortdb;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::operations::*;
    use chainstate::burn::*;
    use chainstate::coordinator::tests::*;
    use chainstate::coordinator::*;
    use chainstate::stacks::boot::*;
    use chainstate::stacks::db::StacksChainState;
    use chainstate::stacks::db::*;
    use chainstate::stacks::miner::test::*;
    use chainstate::stacks::miner::*;
    use chainstate::stacks::*;
    use chainstate::*;
    use core::NETWORK_P2P_PORT;
    use net::asn::*;
    use net::atlas::*;
    use net::chat::*;
    use net::codec::*;
    use net::connection::*;
    use net::db::*;
    use net::neighbors::*;
    use net::p2p::*;
    use net::poll::*;
    use net::relay::*;
    use net::rpc::RPCHandlerArgs;
    use net::Error as net_error;
    use util::get_epoch_time_secs;
    use util::hash::*;
    use util::secp256k1::*;
    use util::strings::*;
    use util::uint::*;
    use util::vrf::*;
    use vm::costs::ExecutionCost;
    use vm::database::STXBalance;
    use vm::types::*;

    use crate::codec::StacksMessageCodec;
    use crate::types::chainstate::StacksMicroblockHeader;
    use crate::types::proof::TrieHash;
    use crate::util::boot::boot_code_test_addr;

    use super::*;

    impl StacksMessageCodec for BlockstackOperationType {
        fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
            match self {
                BlockstackOperationType::LeaderKeyRegister(ref op) => op.consensus_serialize(fd),
                BlockstackOperationType::LeaderBlockCommit(ref op) => op.consensus_serialize(fd),
                BlockstackOperationType::UserBurnSupport(ref op) => op.consensus_serialize(fd),
                BlockstackOperationType::TransferStx(_)
                | BlockstackOperationType::PreStx(_)
                | BlockstackOperationType::StackStx(_) => Ok(()),
            }
        }

        fn consensus_deserialize<R: Read>(
            fd: &mut R,
        ) -> Result<BlockstackOperationType, codec_error> {
            panic!("not used");
        }
    }

    // emulate a socket
    pub struct NetCursor<T> {
        c: Cursor<T>,
        closed: bool,
        block: bool,
        read_error: Option<io::ErrorKind>,
        write_error: Option<io::ErrorKind>,
    }

    impl<T> NetCursor<T> {
        pub fn new(inner: T) -> NetCursor<T> {
            NetCursor {
                c: Cursor::new(inner),
                closed: false,
                block: false,
                read_error: None,
                write_error: None,
            }
        }

        pub fn close(&mut self) -> () {
            self.closed = true;
        }

        pub fn block(&mut self) -> () {
            self.block = true;
        }

        pub fn unblock(&mut self) -> () {
            self.block = false;
        }

        pub fn set_read_error(&mut self, e: Option<io::ErrorKind>) -> () {
            self.read_error = e;
        }

        pub fn set_write_error(&mut self, e: Option<io::ErrorKind>) -> () {
            self.write_error = e;
        }
    }

    impl<T> Deref for NetCursor<T> {
        type Target = Cursor<T>;
        fn deref(&self) -> &Cursor<T> {
            &self.c
        }
    }

    impl<T> DerefMut for NetCursor<T> {
        fn deref_mut(&mut self) -> &mut Cursor<T> {
            &mut self.c
        }
    }

    impl<T> Read for NetCursor<T>
    where
        T: AsRef<[u8]>,
    {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            if self.block {
                return Err(io::Error::from(ErrorKind::WouldBlock));
            }
            if self.closed {
                return Ok(0);
            }
            match self.read_error {
                Some(ref e) => {
                    return Err(io::Error::from((*e).clone()));
                }
                None => {}
            }

            let sz = self.c.read(buf)?;
            if sz == 0 {
                // when reading from a non-blocking socket, a return value of 0 indicates the
                // remote end was closed.  For this reason, when we're out of bytes to read on our
                // inner cursor, but still have bytes, we need to re-interpret this as EWOULDBLOCK.
                return Err(io::Error::from(ErrorKind::WouldBlock));
            } else {
                return Ok(sz);
            }
        }
    }

    impl Write for NetCursor<&mut [u8]> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            if self.block {
                return Err(io::Error::from(ErrorKind::WouldBlock));
            }
            if self.closed {
                return Err(io::Error::from(ErrorKind::Other)); // EBADF
            }
            match self.write_error {
                Some(ref e) => {
                    return Err(io::Error::from((*e).clone()));
                }
                None => {}
            }
            self.c.write(buf)
        }
        fn flush(&mut self) -> io::Result<()> {
            self.c.flush()
        }
    }

    impl Write for NetCursor<&mut Vec<u8>> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.c.write(buf)
        }
        fn flush(&mut self) -> io::Result<()> {
            self.c.flush()
        }
    }

    impl Write for NetCursor<Vec<u8>> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.c.write(buf)
        }
        fn flush(&mut self) -> io::Result<()> {
            self.c.flush()
        }
    }

    /// make a TCP server and a pair of TCP client sockets
    pub fn make_tcp_sockets() -> (
        mio::tcp::TcpListener,
        mio::tcp::TcpStream,
        mio::tcp::TcpStream,
    ) {
        let mut rng = rand::thread_rng();
        let (std_listener, port) = {
            let std_listener;
            let mut next_port;
            loop {
                next_port = 1024 + (rng.next_u32() % (65535 - 1024));
                let hostport = format!("127.0.0.1:{}", next_port);
                std_listener = match std::net::TcpListener::bind(
                    &hostport.parse::<std::net::SocketAddr>().unwrap(),
                ) {
                    Ok(sock) => sock,
                    Err(e) => match e.kind() {
                        io::ErrorKind::AddrInUse => {
                            continue;
                        }
                        _ => {
                            assert!(false, "TcpListener::bind({}): {:?}", &hostport, &e);
                            unreachable!();
                        }
                    },
                };
                break;
            }
            (std_listener, next_port)
        };

        let std_sock_1 = std::net::TcpStream::connect(
            &format!("127.0.0.1:{}", port)
                .parse::<std::net::SocketAddr>()
                .unwrap(),
        )
        .unwrap();
        let sock_1 = mio::tcp::TcpStream::from_stream(std_sock_1).unwrap();
        let (std_sock_2, _) = std_listener.accept().unwrap();
        let sock_2 = mio::tcp::TcpStream::from_stream(std_sock_2).unwrap();

        sock_1.set_nodelay(true).unwrap();
        sock_2.set_nodelay(true).unwrap();

        let listener = mio::tcp::TcpListener::from_std(std_listener).unwrap();

        (listener, sock_1, sock_2)
    }

    // describes a peer's initial configuration
    #[derive(Debug, Clone)]
    pub struct TestPeerConfig {
        pub network_id: u32,
        pub peer_version: u32,
        pub current_block: u64,
        pub private_key: Secp256k1PrivateKey,
        pub private_key_expire: u64,
        pub initial_neighbors: Vec<Neighbor>,
        pub asn4_entries: Vec<ASEntry4>,
        pub burnchain: Burnchain,
        pub connection_opts: ConnectionOptions,
        pub server_port: u16,
        pub http_port: u16,
        pub asn: u32,
        pub org: u32,
        pub allowed: i64,
        pub denied: i64,
        pub data_url: UrlString,
        pub test_name: String,
        pub initial_balances: Vec<(PrincipalData, u64)>,
        pub initial_lockups: Vec<ChainstateAccountLockup>,
        pub spending_account: TestMiner,
        pub setup_code: String,
    }

    impl TestPeerConfig {
        pub fn default() -> TestPeerConfig {
            let conn_opts = ConnectionOptions::default();
            let start_block = 0;
            let mut burnchain = Burnchain::default_unittest(
                start_block,
                &BurnchainHeaderHash::from_hex(
                    "0000000000000000000000000000000000000000000000000000000000000000",
                )
                .unwrap(),
            );
            burnchain.pox_constants =
                PoxConstants::new(5, 3, 3, 25, 5, u64::max_value(), u64::max_value());

            let mut spending_account = TestMinerFactory::new().next_miner(
                &burnchain,
                1,
                1,
                AddressHashMode::SerializeP2PKH,
            );
            spending_account.test_with_tx_fees = false; // manually set transaction fees

            TestPeerConfig {
                network_id: 0x80000000,
                peer_version: 0x01020304,
                current_block: start_block + (burnchain.consensus_hash_lifetime + 1) as u64,
                private_key: Secp256k1PrivateKey::new(),
                private_key_expire: start_block + conn_opts.private_key_lifetime,
                initial_neighbors: vec![],
                asn4_entries: vec![],
                burnchain: burnchain,
                connection_opts: conn_opts,
                server_port: 32000,
                http_port: 32001,
                asn: 0,
                org: 0,
                allowed: 0,
                denied: 0,
                data_url: "".into(),
                test_name: "".into(),
                initial_balances: vec![],
                initial_lockups: vec![],
                spending_account: spending_account,
                setup_code: "".into(),
            }
        }

        pub fn from_port(p: u16) -> TestPeerConfig {
            let mut config = TestPeerConfig {
                server_port: p,
                http_port: p + 1,
                ..TestPeerConfig::default()
            };
            config.data_url =
                UrlString::try_from(format!("http://localhost:{}", config.http_port).as_str())
                    .unwrap();
            config
        }

        pub fn new(test_name: &str, p2p_port: u16, rpc_port: u16) -> TestPeerConfig {
            let mut config = TestPeerConfig {
                test_name: test_name.into(),
                server_port: p2p_port,
                http_port: rpc_port,
                ..TestPeerConfig::default()
            };
            config.data_url =
                UrlString::try_from(format!("http://localhost:{}", config.http_port).as_str())
                    .unwrap();
            config
        }

        pub fn add_neighbor(&mut self, n: &Neighbor) -> () {
            self.initial_neighbors.push(n.clone());
        }

        pub fn to_neighbor(&self) -> Neighbor {
            Neighbor {
                addr: NeighborKey {
                    peer_version: self.peer_version,
                    network_id: self.network_id,
                    addrbytes: PeerAddress([
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 127, 0, 0, 1,
                    ]),
                    port: self.server_port,
                },
                public_key: Secp256k1PublicKey::from_private(&self.private_key),
                expire_block: self.private_key_expire,

                // not known yet
                last_contact_time: 0,
                allowed: self.allowed,
                denied: self.denied,
                asn: self.asn,
                org: self.org,
                in_degree: 0,
                out_degree: 0,
            }
        }

        pub fn to_peer_host(&self) -> PeerHost {
            PeerHost::IP(
                PeerAddress([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 127, 0, 0, 1]),
                self.http_port,
            )
        }
    }

    pub fn dns_thread_start(max_inflight: u64) -> (DNSClient, thread::JoinHandle<()>) {
        let (mut resolver, client) = DNSResolver::new(max_inflight);
        let jh = thread::spawn(move || {
            resolver.thread_main();
        });
        (client, jh)
    }

    pub fn dns_thread_shutdown(dns_client: DNSClient, thread_handle: thread::JoinHandle<()>) {
        drop(dns_client);
        thread_handle.join().unwrap();
    }

    pub struct TestPeer<'a> {
        pub config: TestPeerConfig,
        pub network: PeerNetwork,
        pub sortdb: Option<SortitionDB>,
        pub miner: TestMiner,
        pub stacks_node: Option<TestStacksNode>,
        pub relayer: Relayer,
        pub mempool: Option<MemPoolDB>,
        pub chainstate_path: String,
        pub coord: ChainsCoordinator<'a, NullEventDispatcher, (), OnChainRewardSetProvider>,
    }

    impl<'a> TestPeer<'a> {
        pub fn new(mut config: TestPeerConfig) -> TestPeer<'a> {
            let test_path = format!(
                "/tmp/blockstack-test-peer-{}-{}",
                &config.test_name, config.server_port
            );
            match fs::metadata(&test_path) {
                Ok(_) => {
                    fs::remove_dir_all(&test_path).unwrap();
                }
                Err(_) => {}
            };

            fs::create_dir_all(&test_path).unwrap();

            let mut miner_factory = TestMinerFactory::new();
            let mut miner =
                miner_factory.next_miner(&config.burnchain, 1, 1, AddressHashMode::SerializeP2PKH);

            // manually set fees
            miner.test_with_tx_fees = false;

            let mut burnchain = get_burnchain(&test_path, None);
            burnchain.first_block_height = config.burnchain.first_block_height;
            burnchain.first_block_hash = config.burnchain.first_block_hash;
            burnchain.pox_constants = config.burnchain.pox_constants;

            config.burnchain = burnchain.clone();

            let mut sortdb = SortitionDB::connect(
                &config.burnchain.get_db_path(),
                config.burnchain.first_block_height,
                &config.burnchain.first_block_hash,
                0,
                true,
            )
            .unwrap();

            let first_burnchain_block_height = config.burnchain.first_block_height;
            let first_burnchain_block_hash = config.burnchain.first_block_hash;

            let _burnchain_blocks_db = BurnchainDB::connect(
                &config.burnchain.get_burnchaindb_path(),
                first_burnchain_block_height,
                &first_burnchain_block_hash,
                0,
                true,
            )
            .unwrap();

            let chainstate_path = get_chainstate_path_str(&test_path);
            let peerdb_path = format!("{}/peers.sqlite", &test_path);

            let mut peerdb = PeerDB::connect(
                &peerdb_path,
                true,
                config.network_id,
                config.burnchain.network_id,
                None,
                config.private_key_expire,
                PeerAddress::from_ipv4(127, 0, 0, 1),
                NETWORK_P2P_PORT,
                config.data_url.clone(),
                &config.asn4_entries,
                Some(&config.initial_neighbors),
            )
            .unwrap();
            {
                // bootstrap nodes *always* allowed
                let mut tx = peerdb.tx_begin().unwrap();
                for initial_neighbor in config.initial_neighbors.iter() {
                    PeerDB::set_allow_peer(
                        &mut tx,
                        initial_neighbor.addr.network_id,
                        &initial_neighbor.addr.addrbytes,
                        initial_neighbor.addr.port,
                        -1,
                    )
                    .unwrap();
                }
                tx.commit().unwrap();
            }

            let atlasdb_path = format!("{}/atlas.sqlite", &test_path);
            let atlasdb =
                AtlasDB::connect(AtlasConfig::default(false), &atlasdb_path, true).unwrap();

            let conf = config.clone();
            let post_flight_callback = move |clarity_tx: &mut ClarityTx| {
                if conf.setup_code.len() > 0 {
                    clarity_tx.connection().as_transaction(|clarity| {
                        let boot_code_addr = boot_code_test_addr();
                        let boot_code_account = StacksAccount {
                            principal: boot_code_addr.to_account_principal(),
                            nonce: 0,
                            stx_balance: STXBalance::zero(),
                        };

                        let boot_code_auth = TransactionAuth::Standard(
                            TransactionSpendingCondition::Singlesig(SinglesigSpendingCondition {
                                signer: boot_code_addr.bytes.clone(),
                                hash_mode: SinglesigHashMode::P2PKH,
                                key_encoding: TransactionPublicKeyEncoding::Uncompressed,
                                nonce: 0,
                                tx_fee: 0,
                                signature: MessageSignature::empty(),
                            }),
                        );

                        debug!(
                            "Instantiate test-specific boot code contract '{}.{}' ({} bytes)...",
                            &boot_code_addr.to_string(),
                            &conf.test_name,
                            conf.setup_code.len()
                        );

                        let smart_contract =
                            TransactionPayload::SmartContract(TransactionSmartContract {
                                name: ContractName::try_from(conf.test_name.as_str())
                                    .expect("FATAL: invalid boot-code contract name"),
                                code_body: StacksString::from_str(&conf.setup_code)
                                    .expect("FATAL: invalid boot code body"),
                            });

                        let boot_code_smart_contract = StacksTransaction::new(
                            TransactionVersion::Testnet,
                            boot_code_auth.clone(),
                            smart_contract,
                        );
                        StacksChainState::process_transaction_payload(
                            clarity,
                            &boot_code_smart_contract,
                            &boot_code_account,
                        )
                        .unwrap();
                    });
                }
            };

            let mut boot_data = ChainStateBootData::new(
                &config.burnchain,
                config.initial_balances.clone(),
                Some(Box::new(post_flight_callback)),
            );

            if !config.initial_lockups.is_empty() {
                let lockups = config.initial_lockups.clone();
                boot_data.get_bulk_initial_lockups =
                    Some(Box::new(move || Box::new(lockups.into_iter().map(|e| e))));
            }

            let (chainstate, _) = StacksChainState::open_and_exec(
                false,
                config.network_id,
                &chainstate_path,
                Some(&mut boot_data),
                ExecutionCost::max_value(),
            )
            .unwrap();

            let (tx, _) = sync_channel(100000);
            let mut coord = ChainsCoordinator::test_new(
                &burnchain,
                config.network_id,
                &test_path,
                OnChainRewardSetProvider(),
                tx,
            );
            coord.handle_new_burnchain_block().unwrap();

            let mut stacks_node = TestStacksNode::from_chainstate(chainstate);

            {
                // pre-populate burnchain
                let prev_snapshot = SortitionDB::get_first_block_snapshot(sortdb.conn()).unwrap();
                let mut fork = TestBurnchainFork::new(
                    prev_snapshot.block_height,
                    &prev_snapshot.burn_header_hash,
                    &prev_snapshot.index_root,
                    0,
                );
                for i in prev_snapshot.block_height..config.current_block {
                    let burn_block = {
                        let ic = sortdb.index_conn();
                        let mut burn_block = fork.next_block(&ic);
                        stacks_node.add_key_register(&mut burn_block, &mut miner);
                        burn_block
                    };
                    fork.append_block(burn_block);

                    fork.mine_pending_blocks_pox(&mut sortdb, &config.burnchain, &mut coord);
                }
            }

            let local_addr =
                SocketAddr::new(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)), config.server_port);
            let http_local_addr =
                SocketAddr::new(IpAddr::V4(Ipv4Addr::new(0, 0, 0, 0)), config.http_port);

            {
                let mut tx = peerdb.tx_begin().unwrap();
                PeerDB::set_local_ipaddr(
                    &mut tx,
                    &PeerAddress::from_socketaddr(&SocketAddr::new(
                        IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)),
                        config.server_port,
                    )),
                    config.server_port,
                )
                .unwrap();
                PeerDB::set_local_services(&mut tx, ServiceFlags::RELAY as u16).unwrap();
                PeerDB::set_local_private_key(
                    &mut tx,
                    &config.private_key,
                    config.private_key_expire,
                )
                .unwrap();

                tx.commit().unwrap();
            }

            let local_peer = PeerDB::get_local_peer(peerdb.conn()).unwrap();
            let burnchain_view = {
                let chaintip = SortitionDB::get_canonical_burn_chain_tip(&sortdb.conn()).unwrap();
                SortitionDB::get_burnchain_view(&sortdb.conn(), &config.burnchain, &chaintip)
                    .unwrap()
            };
            let mut peer_network = PeerNetwork::new(
                peerdb,
                atlasdb,
                local_peer,
                config.peer_version,
                config.burnchain.clone(),
                burnchain_view,
                config.connection_opts.clone(),
            );

            peer_network.bind(&local_addr, &http_local_addr).unwrap();
            let relayer = Relayer::from_p2p(&mut peer_network);
            let mempool = MemPoolDB::open(false, config.network_id, &chainstate_path).unwrap();

            TestPeer {
                config: config,
                network: peer_network,
                sortdb: Some(sortdb),
                miner: miner,
                stacks_node: Some(stacks_node),
                relayer: relayer,
                mempool: Some(mempool),
                chainstate_path: chainstate_path,
                coord: coord,
            }
        }

        pub fn connect_initial(&mut self) -> Result<(), net_error> {
            let local_peer = PeerDB::get_local_peer(self.network.peerdb.conn()).unwrap();
            let chain_view = match self.sortdb {
                Some(ref mut sortdb) => {
                    let chaintip =
                        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
                    SortitionDB::get_burnchain_view(
                        &sortdb.conn(),
                        &self.config.burnchain,
                        &chaintip,
                    )
                    .unwrap()
                }
                None => panic!("Misconfigured peer: no sortdb"),
            };

            self.network.local_peer = local_peer;
            self.network.chain_view = chain_view;

            for n in self.config.initial_neighbors.iter() {
                self.network.connect_peer(&n.addr).and_then(|e| Ok(()))?;
            }
            Ok(())
        }

        pub fn local_peer(&self) -> &LocalPeer {
            &self.network.local_peer
        }

        pub fn step(&mut self) -> Result<NetworkResult, net_error> {
            let mut sortdb = self.sortdb.take().unwrap();
            let mut stacks_node = self.stacks_node.take().unwrap();
            let mut mempool = self.mempool.take().unwrap();

            let ret = self.network.run(
                &mut sortdb,
                &mut stacks_node.chainstate,
                &mut mempool,
                None,
                false,
                false,
                10,
                &RPCHandlerArgs::default(),
                &mut HashSet::new(),
            );

            self.sortdb = Some(sortdb);
            self.stacks_node = Some(stacks_node);
            self.mempool = Some(mempool);

            ret
        }

        pub fn step_dns(&mut self, dns_client: &mut DNSClient) -> Result<NetworkResult, net_error> {
            let mut sortdb = self.sortdb.take().unwrap();
            let mut stacks_node = self.stacks_node.take().unwrap();
            let mut mempool = self.mempool.take().unwrap();

            let ret = self.network.run(
                &mut sortdb,
                &mut stacks_node.chainstate,
                &mut mempool,
                Some(dns_client),
                false,
                false,
                10,
                &RPCHandlerArgs::default(),
                &mut HashSet::new(),
            );

            self.sortdb = Some(sortdb);
            self.stacks_node = Some(stacks_node);
            self.mempool = Some(mempool);

            ret
        }

        pub fn for_each_convo_p2p<F, R>(&mut self, mut f: F) -> Vec<Result<R, net_error>>
        where
            F: FnMut(usize, &mut ConversationP2P) -> Result<R, net_error>,
        {
            let mut ret = vec![];
            for (event_id, convo) in self.network.peers.iter_mut() {
                let res = f(*event_id, convo);
                ret.push(res);
            }
            ret
        }

        // this is a fake block -- don't try inserting it
        pub fn empty_burnchain_block(&self, block_height: u64) -> BurnchainBlock {
            assert!(block_height + 1 >= self.config.burnchain.first_block_height);
            let prev_block_height = block_height - 1;

            let block_hash_i = Uint256::from_u64(block_height);
            let mut block_hash_bytes = [0u8; 32];
            block_hash_bytes.copy_from_slice(&block_hash_i.to_u8_slice());

            let prev_block_hash_i = Uint256::from_u64(prev_block_height);
            let mut prev_block_hash_bytes = [0u8; 32];
            prev_block_hash_bytes.copy_from_slice(&prev_block_hash_i.to_u8_slice());

            BurnchainBlock::Bitcoin(BitcoinBlock {
                block_height: block_height + 1,
                block_hash: BurnchainHeaderHash(block_hash_bytes),
                parent_block_hash: BurnchainHeaderHash(prev_block_hash_bytes),
                txs: vec![],
                timestamp: get_epoch_time_secs(),
            })
        }

        fn make_empty_burnchain_block(&mut self) -> BurnchainBlock {
            let empty_block = {
                let sortdb = self.sortdb.take().unwrap();
                let sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
                let empty_block = self.empty_burnchain_block(sn.block_height);
                self.sortdb = Some(sortdb);
                empty_block
            };
            empty_block
        }

        pub fn next_burnchain_block(
            &mut self,
            blockstack_ops: Vec<BlockstackOperationType>,
        ) -> (u64, BurnchainHeaderHash, ConsensusHash) {
            self.inner_next_burnchain_block(blockstack_ops, true, true)
        }

        pub fn next_burnchain_block_raw(
            &mut self,
            blockstack_ops: Vec<BlockstackOperationType>,
        ) -> (u64, BurnchainHeaderHash, ConsensusHash) {
            self.inner_next_burnchain_block(blockstack_ops, false, false)
        }

        pub fn set_ops_consensus_hash(
            blockstack_ops: &mut Vec<BlockstackOperationType>,
            ch: &ConsensusHash,
        ) {
            for op in blockstack_ops.iter_mut() {
                match op {
                    BlockstackOperationType::LeaderKeyRegister(ref mut data) => {
                        data.consensus_hash = (*ch).clone();
                    }
                    BlockstackOperationType::UserBurnSupport(ref mut data) => {
                        data.consensus_hash = (*ch).clone();
                    }
                    _ => {}
                }
            }
        }

        pub fn set_ops_burn_header_hash(
            blockstack_ops: &mut Vec<BlockstackOperationType>,
            bhh: &BurnchainHeaderHash,
        ) {
            for op in blockstack_ops.iter_mut() {
                op.set_burn_header_hash(bhh.clone());
            }
        }

        fn inner_next_burnchain_block(
            &mut self,
            mut blockstack_ops: Vec<BlockstackOperationType>,
            set_consensus_hash: bool,
            set_burn_hash: bool,
        ) -> (u64, BurnchainHeaderHash, ConsensusHash) {
            let sortdb = self.sortdb.take().unwrap();
            let (block_height, block_hash) = {
                let tip = SortitionDB::get_canonical_burn_chain_tip(&sortdb.conn()).unwrap();

                if set_consensus_hash {
                    TestPeer::set_ops_consensus_hash(&mut blockstack_ops, &tip.consensus_hash);
                }

                // quick'n'dirty hash of all operations and block height
                let mut op_buf = vec![];
                for op in blockstack_ops.iter() {
                    op.consensus_serialize(&mut op_buf).unwrap();
                }
                op_buf.append(&mut (tip.block_height + 1).to_be_bytes().to_vec());
                let h = Sha512Trunc256Sum::from_data(&op_buf);
                let mut hash_buf = [0u8; 32];
                hash_buf.copy_from_slice(&h.0);

                let block_header_hash = BurnchainHeaderHash(hash_buf);
                let block_header = BurnchainBlockHeader::from_parent_snapshot(
                    &tip,
                    block_header_hash.clone(),
                    blockstack_ops.len() as u64,
                );

                if set_burn_hash {
                    TestPeer::set_ops_burn_header_hash(&mut blockstack_ops, &block_header_hash);
                }

                let mut burnchain_db =
                    BurnchainDB::open(&self.config.burnchain.get_burnchaindb_path(), true).unwrap();
                burnchain_db
                    .raw_store_burnchain_block(block_header.clone(), blockstack_ops)
                    .unwrap();

                (block_header.block_height, block_header_hash)
            };

            self.coord.handle_new_burnchain_block().unwrap();

            let pox_id = {
                let ic = sortdb.index_conn();
                let tip_sort_id = SortitionDB::get_canonical_sortition_tip(sortdb.conn()).unwrap();
                let sortdb_reader = SortitionHandleConn::open_reader(&ic, &tip_sort_id).unwrap();
                sortdb_reader.get_pox_id().unwrap()
            };

            test_debug!(
                "\n\n{:?}: after burn block {:?}, tip PoX ID is {:?}\n\n",
                &self.to_neighbor().addr,
                &block_hash,
                &pox_id
            );

            let tip = SortitionDB::get_canonical_burn_chain_tip(&sortdb.conn()).unwrap();
            self.sortdb = Some(sortdb);
            (block_height, block_hash, tip.consensus_hash)
        }

        pub fn preprocess_stacks_block(&mut self, block: &StacksBlock) -> Result<bool, String> {
            let sortdb = self.sortdb.take().unwrap();
            let mut node = self.stacks_node.take().unwrap();
            let res = {
                let sn = {
                    let ic = sortdb.index_conn();
                    let tip = SortitionDB::get_canonical_burn_chain_tip(&ic).unwrap();
                    let sn_opt = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                        &ic,
                        &tip.sortition_id,
                        &block.block_hash(),
                    )
                    .unwrap();
                    if sn_opt.is_none() {
                        return Err(format!(
                            "No such block in canonical burn fork: {}",
                            &block.block_hash()
                        ));
                    }
                    sn_opt.unwrap()
                };

                let parent_sn = {
                    let db_handle = sortdb.index_handle(&sn.sortition_id);
                    let parent_sn = db_handle
                        .get_block_snapshot(&sn.parent_burn_header_hash)
                        .unwrap();
                    parent_sn.unwrap()
                };

                let ic = sortdb.index_conn();
                node.chainstate
                    .preprocess_anchored_block(
                        &ic,
                        &sn.consensus_hash,
                        block,
                        &parent_sn.consensus_hash,
                        5,
                    )
                    .map_err(|e| format!("Failed to preprocess anchored block: {:?}", &e))
            };
            if res.is_ok() {
                let pox_id = {
                    let ic = sortdb.index_conn();
                    let tip_sort_id =
                        SortitionDB::get_canonical_sortition_tip(sortdb.conn()).unwrap();
                    let sortdb_reader =
                        SortitionHandleConn::open_reader(&ic, &tip_sort_id).unwrap();
                    sortdb_reader.get_pox_id().unwrap()
                };
                test_debug!(
                    "\n\n{:?}: after stacks block {:?}, tip PoX ID is {:?}\n\n",
                    &self.to_neighbor().addr,
                    &block.block_hash(),
                    &pox_id
                );
                self.coord.handle_new_stacks_block().unwrap();
            }

            self.sortdb = Some(sortdb);
            self.stacks_node = Some(node);
            res
        }

        pub fn preprocess_stacks_microblocks(
            &mut self,
            microblocks: &Vec<StacksMicroblock>,
        ) -> Result<bool, String> {
            assert!(microblocks.len() > 0);
            let sortdb = self.sortdb.take().unwrap();
            let mut node = self.stacks_node.take().unwrap();
            let res = {
                let anchor_block_hash = microblocks[0].header.prev_block.clone();
                let sn = {
                    let ic = sortdb.index_conn();
                    let tip = SortitionDB::get_canonical_burn_chain_tip(&ic).unwrap();
                    let sn_opt = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                        &ic,
                        &tip.sortition_id,
                        &anchor_block_hash,
                    )
                    .unwrap();
                    if sn_opt.is_none() {
                        return Err(format!(
                            "No such block in canonical burn fork: {}",
                            &anchor_block_hash
                        ));
                    }
                    sn_opt.unwrap()
                };

                let mut res = Ok(true);
                for mblock in microblocks.iter() {
                    res = node
                        .chainstate
                        .preprocess_streamed_microblock(
                            &sn.consensus_hash,
                            &anchor_block_hash,
                            mblock,
                        )
                        .map_err(|e| format!("Failed to preprocess microblock: {:?}", &e));

                    if res.is_err() {
                        break;
                    }
                }
                res
            };

            self.sortdb = Some(sortdb);
            self.stacks_node = Some(node);
            res
        }

        pub fn process_stacks_epoch_at_tip(
            &mut self,
            block: &StacksBlock,
            microblocks: &Vec<StacksMicroblock>,
        ) -> () {
            let sortdb = self.sortdb.take().unwrap();
            let mut node = self.stacks_node.take().unwrap();
            {
                let ic = sortdb.index_conn();
                let tip = SortitionDB::get_canonical_burn_chain_tip(&ic).unwrap();
                node.chainstate
                    .preprocess_stacks_epoch(&ic, &tip, block, microblocks)
                    .unwrap();
            }
            self.coord.handle_new_stacks_block().unwrap();

            let pox_id = {
                let ic = sortdb.index_conn();
                let tip_sort_id = SortitionDB::get_canonical_sortition_tip(sortdb.conn()).unwrap();
                let sortdb_reader = SortitionHandleConn::open_reader(&ic, &tip_sort_id).unwrap();
                sortdb_reader.get_pox_id().unwrap()
            };
            test_debug!(
                "\n\n{:?}: after stacks block {:?}, tip PoX ID is {:?}\n\n",
                &self.to_neighbor().addr,
                &block.block_hash(),
                &pox_id
            );

            self.sortdb = Some(sortdb);
            self.stacks_node = Some(node);
        }

        pub fn process_stacks_epoch(
            &mut self,
            block: &StacksBlock,
            consensus_hash: &ConsensusHash,
            microblocks: &Vec<StacksMicroblock>,
        ) -> () {
            let sortdb = self.sortdb.take().unwrap();
            let mut node = self.stacks_node.take().unwrap();
            {
                let ic = sortdb.index_conn();
                Relayer::process_new_anchored_block(
                    &ic,
                    &mut node.chainstate,
                    consensus_hash,
                    block,
                    0,
                )
                .unwrap();

                let block_hash = block.block_hash();
                for mblock in microblocks.iter() {
                    node.chainstate
                        .preprocess_streamed_microblock(consensus_hash, &block_hash, mblock)
                        .unwrap();
                }
            }
            self.coord.handle_new_stacks_block().unwrap();

            let pox_id = {
                let ic = sortdb.index_conn();
                let tip_sort_id = SortitionDB::get_canonical_sortition_tip(sortdb.conn()).unwrap();
                let sortdb_reader = SortitionHandleConn::open_reader(&ic, &tip_sort_id).unwrap();
                sortdb_reader.get_pox_id().unwrap()
            };

            test_debug!(
                "\n\n{:?}: after stacks block {:?}, tip PoX ID is {:?}\n\n",
                &self.to_neighbor().addr,
                &block.block_hash(),
                &pox_id
            );

            self.sortdb = Some(sortdb);
            self.stacks_node = Some(node);
        }

        pub fn add_empty_burnchain_block(&mut self) -> (u64, BurnchainHeaderHash, ConsensusHash) {
            self.next_burnchain_block(vec![])
        }

        pub fn chainstate(&mut self) -> &mut StacksChainState {
            &mut self.stacks_node.as_mut().unwrap().chainstate
        }

        pub fn sortdb(&mut self) -> &mut SortitionDB {
            self.sortdb.as_mut().unwrap()
        }

        pub fn with_db_state<F, R>(&mut self, f: F) -> Result<R, net_error>
        where
            F: FnOnce(
                &mut SortitionDB,
                &mut StacksChainState,
                &mut Relayer,
                &mut MemPoolDB,
            ) -> Result<R, net_error>,
        {
            let mut sortdb = self.sortdb.take().unwrap();
            let mut stacks_node = self.stacks_node.take().unwrap();
            let mut mempool = self.mempool.take().unwrap();

            let res = f(
                &mut sortdb,
                &mut stacks_node.chainstate,
                &mut self.relayer,
                &mut mempool,
            );

            self.stacks_node = Some(stacks_node);
            self.sortdb = Some(sortdb);
            self.mempool = Some(mempool);
            res
        }

        pub fn with_mining_state<F, R>(&mut self, f: F) -> Result<R, net_error>
        where
            F: FnOnce(
                &mut SortitionDB,
                &mut TestMiner,
                &mut TestMiner,
                &mut TestStacksNode,
            ) -> Result<R, net_error>,
        {
            let mut stacks_node = self.stacks_node.take().unwrap();
            let mut sortdb = self.sortdb.take().unwrap();
            let res = f(
                &mut sortdb,
                &mut self.miner,
                &mut self.config.spending_account,
                &mut stacks_node,
            );
            self.sortdb = Some(sortdb);
            self.stacks_node = Some(stacks_node);
            res
        }

        pub fn with_network_state<F, R>(&mut self, f: F) -> Result<R, net_error>
        where
            F: FnOnce(
                &mut SortitionDB,
                &mut StacksChainState,
                &mut PeerNetwork,
                &mut Relayer,
                &mut MemPoolDB,
            ) -> Result<R, net_error>,
        {
            let mut sortdb = self.sortdb.take().unwrap();
            let mut stacks_node = self.stacks_node.take().unwrap();
            let mut mempool = self.mempool.take().unwrap();

            let res = f(
                &mut sortdb,
                &mut stacks_node.chainstate,
                &mut self.network,
                &mut self.relayer,
                &mut mempool,
            );

            self.stacks_node = Some(stacks_node);
            self.sortdb = Some(sortdb);
            self.mempool = Some(mempool);
            res
        }

        pub fn with_peer_state<F, R>(&mut self, f: F) -> Result<R, net_error>
        where
            F: FnOnce(
                &mut TestPeer,
                &mut SortitionDB,
                &mut StacksChainState,
                &mut MemPoolDB,
            ) -> Result<R, net_error>,
        {
            let mut sortdb = self.sortdb.take().unwrap();
            let mut stacks_node = self.stacks_node.take().unwrap();
            let mut mempool = self.mempool.take().unwrap();

            let res = f(self, &mut sortdb, &mut stacks_node.chainstate, &mut mempool);

            self.stacks_node = Some(stacks_node);
            self.sortdb = Some(sortdb);
            self.mempool = Some(mempool);
            res
        }

        // Make a tenure
        pub fn make_tenure<F>(
            &mut self,
            mut tenure_builder: F,
        ) -> (
            Vec<BlockstackOperationType>,
            StacksBlock,
            Vec<StacksMicroblock>,
        )
        where
            F: FnMut(
                &mut TestMiner,
                &mut SortitionDB,
                &mut StacksChainState,
                VRFProof,
                Option<&StacksBlock>,
                Option<&StacksMicroblockHeader>,
            ) -> (StacksBlock, Vec<StacksMicroblock>),
        {
            let mut sortdb = self.sortdb.take().unwrap();
            let mut burn_block = {
                let sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
                TestBurnchainBlock::new(&sn, 0)
            };

            let last_sortition_block =
                SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap(); // no forks here

            let mut stacks_node = self.stacks_node.take().unwrap();

            let parent_block_opt = stacks_node.get_last_anchored_block(&self.miner);
            let parent_microblock_header_opt =
                get_last_microblock_header(&stacks_node, &self.miner, parent_block_opt.as_ref());
            let last_key = stacks_node.get_last_key(&self.miner);

            let network_id = self.config.network_id;
            let chainstate_path = self.chainstate_path.clone();
            let burn_block_height = burn_block.block_height;

            let proof = self
                .miner
                .make_proof(
                    &last_key.public_key,
                    &burn_block.parent_snapshot.sortition_hash,
                )
                .expect(&format!(
                    "FATAL: no private key for {}",
                    last_key.public_key.to_hex()
                ));

            let (stacks_block, microblocks) = tenure_builder(
                &mut self.miner,
                &mut sortdb,
                &mut stacks_node.chainstate,
                proof,
                parent_block_opt.as_ref(),
                parent_microblock_header_opt.as_ref(),
            );

            let mut block_commit_op = stacks_node.make_tenure_commitment(
                &mut sortdb,
                &mut burn_block,
                &mut self.miner,
                &stacks_block,
                &microblocks,
                1000,
                &last_key,
                Some(&last_sortition_block),
            );
            let leader_key_op = stacks_node.add_key_register(&mut burn_block, &mut self.miner);

            // patch in reward set info
            match get_next_recipients(
                &last_sortition_block,
                &mut stacks_node.chainstate,
                &mut sortdb,
                &self.config.burnchain,
                &OnChainRewardSetProvider(),
            ) {
                Ok(recipients) => {
                    block_commit_op.commit_outs = match recipients {
                        Some(info) => {
                            let mut recipients = info
                                .recipients
                                .into_iter()
                                .map(|x| x.0)
                                .collect::<Vec<StacksAddress>>();
                            if recipients.len() == 1 {
                                recipients.push(StacksAddress::burn_address(false));
                            }
                            recipients
                        }
                        None => vec![],
                    };
                    test_debug!(
                        "Block commit at height {} has {} recipients: {:?}",
                        block_commit_op.block_height,
                        block_commit_op.commit_outs.len(),
                        &block_commit_op.commit_outs
                    );
                }
                Err(e) => {
                    panic!("Failure fetching recipient set: {:?}", e);
                }
            };

            self.stacks_node = Some(stacks_node);
            self.sortdb = Some(sortdb);
            (
                vec![
                    BlockstackOperationType::LeaderKeyRegister(leader_key_op),
                    BlockstackOperationType::LeaderBlockCommit(block_commit_op),
                ],
                stacks_block,
                microblocks,
            )
        }

        // have this peer produce an anchored block and microblock tail using its internal miner.
        pub fn make_default_tenure(
            &mut self,
        ) -> (
            Vec<BlockstackOperationType>,
            StacksBlock,
            Vec<StacksMicroblock>,
        ) {
            let mut sortdb = self.sortdb.take().unwrap();
            let mut burn_block = {
                let sn = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
                TestBurnchainBlock::new(&sn, 0)
            };

            let mut stacks_node = self.stacks_node.take().unwrap();

            let parent_block_opt = stacks_node.get_last_anchored_block(&self.miner);
            let parent_microblock_header_opt =
                get_last_microblock_header(&stacks_node, &self.miner, parent_block_opt.as_ref());
            let last_key = stacks_node.get_last_key(&self.miner);

            let network_id = self.config.network_id;
            let chainstate_path = self.chainstate_path.clone();
            let burn_block_height = burn_block.block_height;

            let (stacks_block, microblocks, block_commit_op) = stacks_node.mine_stacks_block(
                &mut sortdb,
                &mut self.miner,
                &mut burn_block,
                &last_key,
                parent_block_opt.as_ref(),
                1000,
                |mut builder, ref mut miner, ref sortdb| {
                    let (mut miner_chainstate, _) =
                        StacksChainState::open(false, network_id, &chainstate_path).unwrap();
                    let sort_iconn = sortdb.index_conn();
                    let mut epoch = builder
                        .epoch_begin(&mut miner_chainstate, &sort_iconn)
                        .unwrap();

                    let (stacks_block, microblocks) =
                        mine_smart_contract_block_contract_call_microblock(
                            &mut epoch,
                            &mut builder,
                            miner,
                            burn_block_height as usize,
                            parent_microblock_header_opt.as_ref(),
                        );

                    builder.epoch_finish(epoch);
                    (stacks_block, microblocks)
                },
            );

            let leader_key_op = stacks_node.add_key_register(&mut burn_block, &mut self.miner);

            self.stacks_node = Some(stacks_node);
            self.sortdb = Some(sortdb);
            (
                vec![
                    BlockstackOperationType::LeaderKeyRegister(leader_key_op),
                    BlockstackOperationType::LeaderBlockCommit(block_commit_op),
                ],
                stacks_block,
                microblocks,
            )
        }

        pub fn to_neighbor(&self) -> Neighbor {
            self.config.to_neighbor()
        }

        pub fn to_peer_host(&self) -> PeerHost {
            self.config.to_peer_host()
        }

        pub fn get_public_key(&self) -> Secp256k1PublicKey {
            let local_peer = PeerDB::get_local_peer(&self.network.peerdb.conn()).unwrap();
            Secp256k1PublicKey::from_private(&local_peer.private_key)
        }

        pub fn get_peerdb_conn(&self) -> &DBConn {
            self.network.peerdb.conn()
        }

        pub fn get_burnchain_view(&mut self) -> Result<BurnchainView, db_error> {
            let sortdb = self.sortdb.take().unwrap();
            let view_res = {
                let chaintip = SortitionDB::get_canonical_burn_chain_tip(&sortdb.conn()).unwrap();
                SortitionDB::get_burnchain_view(&sortdb.conn(), &self.config.burnchain, &chaintip)
            };
            self.sortdb = Some(sortdb);
            view_res
        }

        pub fn dump_frontier(&self) -> () {
            let conn = self.network.peerdb.conn();
            let peers = PeerDB::get_all_peers(conn).unwrap();
            debug!("--- BEGIN ALL PEERS ({}) ---", peers.len());
            debug!("{:#?}", &peers);
            debug!("--- END ALL PEERS ({}) -----", peers.len());
        }
    }
}
