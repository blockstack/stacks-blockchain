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

use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt;
use std::io;
use std::io::prelude::*;
use std::io::{Read, Write};
use std::mem;
use std::net::SocketAddr;
use std::str;
use std::str::FromStr;
use std::time::SystemTime;

use percent_encoding::percent_decode_str;
use regex::{Captures, Regex};
use serde::{Deserialize, Serialize};
use serde_json;
use time;
use url::{form_urlencoded, Url};

use burnchains::{Address, Txid};
use chainstate::burn::ConsensusHash;
use chainstate::stacks::{StacksBlock, StacksMicroblock, StacksPublicKey, StacksTransaction};
use deps::httparse;
use net::atlas::Attachment;
use net::CallReadOnlyRequestBody;
use net::ClientError;
use net::Error as net_error;
use net::Error::ClarityError;
use net::HttpContentType;
use net::HttpRequestMetadata;
use net::HttpRequestPreamble;
use net::HttpRequestType;
use net::HttpResponseMetadata;
use net::HttpResponsePreamble;
use net::HttpResponseType;
use net::HttpVersion;
use net::MessageSequence;
use net::NeighborAddress;
use net::PeerAddress;
use net::PeerHost;
use net::ProtocolFamily;
use net::StacksHttpMessage;
use net::StacksHttpPreamble;
use net::UnconfirmedTransactionResponse;
use net::UnconfirmedTransactionStatus;
use net::HTTP_PREAMBLE_MAX_ENCODED_SIZE;
use net::HTTP_PREAMBLE_MAX_NUM_HEADERS;
use net::HTTP_REQUEST_ID_RESERVED;
use net::MAX_MICROBLOCKS_UNCONFIRMED;
use net::{GetAttachmentResponse, GetAttachmentsInvResponse, PostTransactionRequestBody};
use util::hash::hex_bytes;
use util::hash::to_hex;
use util::hash::Hash160;
use util::log;
use util::retry::BoundReader;
use util::retry::RetryReader;
use vm::types::{StandardPrincipalData, TraitIdentifier};
use vm::{
    ast::parser::{
        CLARITY_NAME_REGEX, CONTRACT_NAME_REGEX, PRINCIPAL_DATA_REGEX, STANDARD_PRINCIPAL_REGEX,
    },
    types::{PrincipalData, BOUND_VALUE_SERIALIZATION_HEX},
    ClarityName, ContractName, Value,
};

use crate::codec::{
    read_next, write_next, Error as codec_error, StacksMessageCodec, MAX_MESSAGE_LEN,
    MAX_PAYLOAD_LEN,
};
use crate::types::chainstate::{BlockHeaderHash, StacksAddress, StacksBlockId};

lazy_static! {
    static ref PATH_GETINFO: Regex = Regex::new(r#"^/v2/info$"#).unwrap();
    static ref PATH_GETPOXINFO: Regex = Regex::new(r#"^/v2/pox$"#).unwrap();
    static ref PATH_GETNEIGHBORS: Regex = Regex::new(r#"^/v2/neighbors$"#).unwrap();
    static ref PATH_GETBLOCK: Regex = Regex::new(r#"^/v2/blocks/([0-9a-f]{64})$"#).unwrap();
    static ref PATH_GETMICROBLOCKS_INDEXED: Regex =
        Regex::new(r#"^/v2/microblocks/([0-9a-f]{64})$"#).unwrap();
    static ref PATH_GETMICROBLOCKS_CONFIRMED: Regex =
        Regex::new(r#"^/v2/microblocks/confirmed/([0-9a-f]{64})$"#).unwrap();
    static ref PATH_GETMICROBLOCKS_UNCONFIRMED: Regex =
        Regex::new(r#"^/v2/microblocks/unconfirmed/([0-9a-f]{64})/([0-9]{1,5})$"#).unwrap();
    static ref PATH_GETTRANSACTION_UNCONFIRMED: Regex =
        Regex::new(r#"^/v2/transactions/unconfirmed/([0-9a-f]{64})$"#).unwrap();
    static ref PATH_POSTTRANSACTION: Regex = Regex::new(r#"^/v2/transactions$"#).unwrap();
    static ref PATH_POSTBLOCK: Regex = Regex::new(r#"^/v2/blocks/upload/([0-9a-f]{40})$"#).unwrap();
    static ref PATH_POSTMICROBLOCK: Regex = Regex::new(r#"^/v2/microblocks$"#).unwrap();
    static ref PATH_GET_ACCOUNT: Regex = Regex::new(&format!(
        "^/v2/accounts/(?P<principal>{})$",
        *PRINCIPAL_DATA_REGEX
    ))
    .unwrap();
    static ref PATH_GET_MAP_ENTRY: Regex = Regex::new(&format!(
        "^/v2/map_entry/(?P<address>{})/(?P<contract>{})/(?P<map>{})$",
        *STANDARD_PRINCIPAL_REGEX, *CONTRACT_NAME_REGEX, *CLARITY_NAME_REGEX
    ))
    .unwrap();
    static ref PATH_POST_CALL_READ_ONLY: Regex = Regex::new(&format!(
        "^/v2/contracts/call-read/(?P<address>{})/(?P<contract>{})/(?P<function>{})$",
        *STANDARD_PRINCIPAL_REGEX, *CONTRACT_NAME_REGEX, *CLARITY_NAME_REGEX
    ))
    .unwrap();
    static ref PATH_GET_CONTRACT_SRC: Regex = Regex::new(&format!(
        "^/v2/contracts/source/(?P<address>{})/(?P<contract>{})$",
        *STANDARD_PRINCIPAL_REGEX, *CONTRACT_NAME_REGEX
    ))
    .unwrap();
    static ref PATH_GET_IS_TRAIT_IMPLEMENTED: Regex = Regex::new(&format!(
        "^/v2/traits/(?P<address>{})/(?P<contract>{})/(?P<traitContractAddr>{})/(?P<traitContractName>{})/(?P<traitName>{})$",
        *STANDARD_PRINCIPAL_REGEX, *CONTRACT_NAME_REGEX, *STANDARD_PRINCIPAL_REGEX, *CONTRACT_NAME_REGEX, *CLARITY_NAME_REGEX
    ))
    .unwrap();
    static ref PATH_GET_CONTRACT_ABI: Regex = Regex::new(&format!(
        "^/v2/contracts/interface/(?P<address>{})/(?P<contract>{})$",
        *STANDARD_PRINCIPAL_REGEX, *CONTRACT_NAME_REGEX
    ))
    .unwrap();
    static ref PATH_GET_TRANSFER_COST: Regex = Regex::new("^/v2/fees/transfer$").unwrap();
    static ref PATH_GET_ATTACHMENTS_INV: Regex = Regex::new("^/v2/attachments/inv$").unwrap();
    static ref PATH_GET_ATTACHMENT: Regex =
        Regex::new(r#"^/v2/attachments/([0-9a-f]{40})$"#).unwrap();
    static ref PATH_OPTIONS_WILDCARD: Regex = Regex::new("^/v2/.{0,4096}$").unwrap();
}

/// HTTP headers that we really care about
#[derive(Debug, Clone, PartialEq)]
enum HttpReservedHeader {
    ContentLength(u32),
    ContentType(HttpContentType),
    XRequestID(u32),
    Host(PeerHost),
}

/// Stacks block accepted struct
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
struct StacksBlockAcceptedData {
    stacks_block_id: StacksBlockId,
    accepted: bool,
}

impl FromStr for PeerHost {
    type Err = net_error;

    fn from_str(header: &str) -> Result<PeerHost, net_error> {
        // we're looser than the RFC allows for DNS names -- anything that doesn't parse to an IP
        // address will be parsed to a DNS name.
        // try as IP:port
        match header.parse::<SocketAddr>() {
            Ok(socketaddr) => Ok(PeerHost::IP(
                PeerAddress::from_socketaddr(&socketaddr),
                socketaddr.port(),
            )),
            Err(_) => {
                // maybe missing :port
                let hostport = format!("{}:80", header);
                match hostport.parse::<SocketAddr>() {
                    Ok(socketaddr) => Ok(PeerHost::IP(
                        PeerAddress::from_socketaddr(&socketaddr),
                        socketaddr.port(),
                    )),
                    Err(_) => {
                        // try as DNS-name:port
                        let host;
                        let port;
                        let parts: Vec<&str> = header.split(":").collect();
                        if parts.len() == 0 {
                            return Err(net_error::DeserializeError(
                                "Failed to parse PeerHost: no parts".to_string(),
                            ));
                        } else if parts.len() == 1 {
                            // no port
                            host = Some(parts[0].to_string());
                            port = Some(80);
                        } else {
                            let np = parts.len();
                            if parts[np - 1].chars().all(char::is_numeric) {
                                // ends in :port
                                let host_str = parts[0..np - 1].join(":");
                                if host_str.len() == 0 {
                                    return Err(net_error::DeserializeError(
                                        "Empty host".to_string(),
                                    ));
                                }
                                host = Some(host_str);

                                let port_res = parts[np - 1].parse::<u16>();
                                port = match port_res {
                                    Ok(p) => Some(p),
                                    Err(_) => {
                                        return Err(net_error::DeserializeError(
                                            "Failed to parse PeerHost: invalid port".to_string(),
                                        ));
                                    }
                                };
                            } else {
                                // only host
                                host = Some(header.to_string());
                                port = Some(80);
                            }
                        }

                        match (host, port) {
                            (Some(h), Some(p)) => Ok(PeerHost::DNS(h, p)),
                            (_, _) => Err(net_error::DeserializeError(
                                "Failed to parse PeerHost: failed to extract host and/or port"
                                    .to_string(),
                            )), // I don't think this is reachable
                        }
                    }
                }
            }
        }
    }
}

impl HttpReservedHeader {
    pub fn is_reserved(header: &str) -> bool {
        let hdr = header.to_string();
        match hdr.as_str() {
            "content-length" | "content-type" | "x-request-id" | "host" => true,
            _ => false,
        }
    }

    pub fn try_from_str(header: &str, value: &str) -> Option<HttpReservedHeader> {
        let hdr = header.to_string().to_lowercase();
        match hdr.as_str() {
            "content-length" => match value.parse::<u32>() {
                Ok(cl) => Some(HttpReservedHeader::ContentLength(cl)),
                Err(_) => None,
            },
            "content-type" => match value.parse::<HttpContentType>() {
                Ok(ct) => Some(HttpReservedHeader::ContentType(ct)),
                Err(_) => None,
            },
            "x-request-id" => match value.parse::<u32>() {
                Ok(rid) => Some(HttpReservedHeader::XRequestID(rid)),
                Err(_) => None,
            },
            "host" => match value.parse::<PeerHost>() {
                Ok(ph) => Some(HttpReservedHeader::Host(ph)),
                Err(_) => None,
            },
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Copy)]
enum HttpChunkedTransferParseMode {
    ChunkBoundary,
    Chunk,
    ChunkTrailer,
    EOF,
}

#[derive(Debug, Clone, PartialEq, Copy)]
struct HttpChunkedTransferReaderState {
    parse_step: HttpChunkedTransferParseMode,
    chunk_size: u64,
    chunk_read: u64,
    max_size: u64,
    total_size: u64,
    last_chunk_size: u64,

    // for parsing a chunk boundary
    // (we don't use extensions, so 16 bytes for size + 2 for \r\n delimiter ought to be enough)
    chunk_buffer: [u8; 18],
    i: usize,
}

impl HttpChunkedTransferReaderState {
    pub fn new(max_size: u64) -> HttpChunkedTransferReaderState {
        HttpChunkedTransferReaderState {
            parse_step: HttpChunkedTransferParseMode::ChunkBoundary,
            chunk_size: 0,
            chunk_read: 0,
            max_size: max_size,
            total_size: 0,
            last_chunk_size: u64::max_value(), // if this ever becomes 0, then we should expect chunk boundary '0\r\n\r\n' and EOF
            chunk_buffer: [0u8; 18],
            i: 0,
        }
    }

    pub fn is_eof(&self) -> bool {
        self.parse_step == HttpChunkedTransferParseMode::EOF
    }
}

/// read adapter for chunked transfer encoding
struct HttpChunkedTransferReader<'a, R: Read> {
    fd: &'a mut R,
    state: HttpChunkedTransferReaderState,
}

impl<'a, R: Read> HttpChunkedTransferReader<'a, R> {
    pub fn from_reader(r: &'a mut R, max_size: u64) -> HttpChunkedTransferReader<'a, R> {
        HttpChunkedTransferReader {
            fd: r,
            state: HttpChunkedTransferReaderState::new(max_size),
        }
    }

    pub fn from_state(
        r: &'a mut R,
        state: HttpChunkedTransferReaderState,
    ) -> HttpChunkedTransferReader<'a, R> {
        HttpChunkedTransferReader {
            fd: r,
            state: state,
        }
    }
}

impl HttpChunkedTransferReaderState {
    /// Read until we have a chunk marker we can parse completely.
    /// Interruptable -- call repeatedly on EINTR.
    /// Reads at most one byte.
    fn read_chunk_boundary<R: Read>(&mut self, fd: &mut R) -> io::Result<usize> {
        assert_eq!(self.parse_step, HttpChunkedTransferParseMode::ChunkBoundary);

        // next byte
        let mut b = [0u8; 1];

        trace!("Read {} bytes", b.len());
        let nr = fd.read(&mut b)?;
        if nr == 0 {
            return Ok(nr);
        }
        trace!("Got {} bytes", nr);

        self.chunk_buffer[self.i] = b[0];
        self.i += 1;

        if self.i >= self.chunk_buffer.len() {
            // don't allow ridiculous extension lengths
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                net_error::DeserializeError("Invalid HTTP chunk boundary: too long".to_string()),
            ));
        }

        let (offset, chunk_len) = match httparse::parse_chunk_size(&self.chunk_buffer[0..self.i]) {
            Ok(httparse::Status::Partial) => {
                return Ok(nr);
            }
            Ok(httparse::Status::Complete((offset, chunk_len))) => (offset, chunk_len),
            Err(_) => {
                test_debug!(
                    "Invalid chunk boundary: {:?}",
                    self.chunk_buffer[0..self.i].to_vec()
                );
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Invalid HTTP chunk boundary: could not parse".to_string(),
                ));
            }
        };

        trace!("chunk offset: {}. chunk len: {}", offset, chunk_len);
        if chunk_len > MAX_MESSAGE_LEN as u64 {
            trace!("chunk buffer: {:?}", &self.chunk_buffer[0..self.i]);
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                net_error::DeserializeError("Invalid HTTP chunk: too big".to_string()),
            ));
        }

        // got an offset/len.
        // offset ought to equal the number of bytes taken by the encoded chunk boundary.
        assert_eq!(offset, self.i);

        // reset buffers
        self.i = 0;
        self.chunk_size = chunk_len;
        self.chunk_read = 0;

        // begin reading chunk
        trace!("begin reading chunk");
        self.parse_step = HttpChunkedTransferParseMode::Chunk;
        Ok(nr)
    }

    /// Read a chunk -- read up to self.chunk_size bytes over successive calls.
    /// Reads at most self.chunk_size bytes.
    fn read_chunk_bytes<R: Read>(&mut self, fd: &mut R, buf: &mut [u8]) -> io::Result<usize> {
        assert_eq!(self.parse_step, HttpChunkedTransferParseMode::Chunk);

        if self.total_size >= self.max_size && self.chunk_size > 0 {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                net_error::OverflowError("HTTP body exceeds maximum expected length".to_string()),
            ));
        }

        let remaining =
            if self.chunk_size - self.chunk_read <= (self.max_size - self.total_size) as u64 {
                self.chunk_size - self.chunk_read
            } else {
                (self.max_size - self.total_size) as u64
            };

        let nr = if (buf.len() as u64) < remaining {
            // can fill buffer
            trace!("Read {} bytes (fill buffer)", buf.len());
            fd.read(buf)? as u64
        } else {
            // will read up to a chunk boundary
            trace!("Read {} bytes (fill remainder)", remaining);
            fd.read(&mut buf[0..(remaining as usize)])? as u64
        };

        trace!("Got {} bytes", nr);

        self.chunk_read += nr;

        if self.chunk_read >= self.chunk_size {
            // done reading; proceed to consume trailer
            trace!(
                "begin reading trailer ({} >= {})",
                self.chunk_read,
                self.chunk_size
            );
            self.parse_step = HttpChunkedTransferParseMode::ChunkTrailer;
        }

        self.total_size += nr;
        Ok(nr as usize)
    }

    /// Read chunk trailer -- read end-of-chunk \r\n
    /// Returns number of bytes read on success
    /// Reads at most 2 bytes.
    fn read_chunk_trailer<R: Read>(&mut self, fd: &mut R) -> io::Result<usize> {
        assert_eq!(self.parse_step, HttpChunkedTransferParseMode::ChunkTrailer);

        let mut nr = 0;

        // read trailer
        if self.i < 2 {
            let mut trailer_buf = [0u8; 2];

            trace!("Read at most {} bytes", 2 - self.i);
            nr = fd.read(&mut trailer_buf[self.i..2])?;
            if nr == 0 {
                return Ok(nr);
            }

            self.chunk_buffer[self.i..2].copy_from_slice(&trailer_buf[self.i..2]);
            self.i += nr;
        }

        if self.i == 2 {
            // expect '\r\n'
            if &self.chunk_buffer[0..2] != &[0x0d, 0x0a] {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    net_error::DeserializeError("Invalid chunk trailer".to_string()),
                ));
            }

            // end of chunk
            self.last_chunk_size = self.chunk_size;
            self.i = 0;

            trace!("begin reading boundary");
            self.parse_step = HttpChunkedTransferParseMode::ChunkBoundary;
        }

        trace!("Consumed {} bytes of chunk boundary (i = {})", nr, self.i);
        Ok(nr)
    }

    /// Read from a Read.
    /// Returns (number of bytes decoded, number of bytes consumed from the Read)
    fn do_read<R: Read>(&mut self, fd: &mut R, buf: &mut [u8]) -> io::Result<(usize, usize)> {
        let mut decoded = 0;
        let mut consumed = 0;
        while decoded < buf.len() {
            match self.parse_step {
                HttpChunkedTransferParseMode::ChunkBoundary => {
                    let count = self.read_chunk_boundary(fd)?;
                    if count == 0 {
                        break;
                    }
                    consumed += count;
                }
                HttpChunkedTransferParseMode::Chunk => {
                    let nr = self.read_chunk_bytes(fd, &mut buf[decoded..])?;
                    if nr == 0 && self.parse_step == HttpChunkedTransferParseMode::Chunk {
                        // still trying to read the chunk, but got 0 bytes
                        break;
                    }
                    decoded += nr;
                    consumed += nr;
                }
                HttpChunkedTransferParseMode::ChunkTrailer => {
                    let count = self.read_chunk_trailer(fd)?;
                    if count == 0 {
                        break;
                    }
                    consumed += count;
                    if self.last_chunk_size == 0 {
                        // we're done
                        trace!("finished last chunk");
                        self.parse_step = HttpChunkedTransferParseMode::EOF;
                        break;
                    }
                }
                HttpChunkedTransferParseMode::EOF => {
                    break;
                }
            }
        }
        Ok((decoded, consumed))
    }
}

impl<'a, R: Read> Read for HttpChunkedTransferReader<'a, R> {
    /// Read a HTTP chunk-encoded stream.
    /// Returns number of decoded bytes (i.e. number of bytes copied to buf, as expected)
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.state
            .do_read(self.fd, buf)
            .and_then(|(decoded, _)| Ok(decoded))
    }
}

pub struct HttpChunkedTransferWriterState {
    chunk_size: usize,
    chunk_buf: Vec<u8>,
    corked: bool,
}

impl HttpChunkedTransferWriterState {
    pub fn new(chunk_size: usize) -> HttpChunkedTransferWriterState {
        HttpChunkedTransferWriterState {
            chunk_size: chunk_size,
            chunk_buf: vec![],
            corked: false,
        }
    }
}

pub struct HttpChunkedTransferWriter<'a, 'state, W: Write> {
    fd: &'a mut W,
    state: &'state mut HttpChunkedTransferWriterState,
}

impl<'a, 'state, W: Write> HttpChunkedTransferWriter<'a, 'state, W> {
    pub fn from_writer_state(
        fd: &'a mut W,
        state: &'state mut HttpChunkedTransferWriterState,
    ) -> HttpChunkedTransferWriter<'a, 'state, W> {
        HttpChunkedTransferWriter {
            fd: fd,
            state: state,
        }
    }

    fn send_chunk(fd: &mut W, chunk_size: usize, bytes: &[u8]) -> io::Result<usize> {
        let to_send = if chunk_size < bytes.len() {
            chunk_size
        } else {
            bytes.len()
        };

        fd.write_all(format!("{:x}\r\n", to_send).as_bytes())?;
        fd.write_all(&bytes[0..to_send])?;
        fd.write_all("\r\n".as_bytes())?;
        Ok(to_send)
    }

    fn flush_chunk(&mut self) -> io::Result<usize> {
        let sent = HttpChunkedTransferWriter::send_chunk(
            &mut self.fd,
            self.state.chunk_size,
            &self.state.chunk_buf,
        )?;
        self.state.chunk_buf.clear();
        Ok(sent)
    }

    fn buf_chunk(&mut self, buf: &[u8]) -> usize {
        let to_copy = if self.state.chunk_size - self.state.chunk_buf.len() < buf.len() {
            self.state.chunk_size - self.state.chunk_buf.len()
        } else {
            buf.len()
        };

        self.state.chunk_buf.extend_from_slice(&buf[0..to_copy]);
        to_copy
    }

    pub fn cork(&mut self) -> () {
        // block future flushes from sending trailing empty chunks -- we're done sending
        self.state.corked = true;
    }

    pub fn corked(&self) -> bool {
        self.state.corked
    }
}

impl<'a, 'state, W: Write> Write for HttpChunkedTransferWriter<'a, 'state, W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let mut written = 0;
        while written < buf.len() && !self.state.corked {
            if self.state.chunk_buf.len() > 0 {
                if self.state.chunk_buf.len() < self.state.chunk_size {
                    let nw = self.buf_chunk(&buf[written..]);
                    written += nw;
                }
                if self.state.chunk_buf.len() >= self.state.chunk_size {
                    self.flush_chunk()?;
                }
            } else {
                if written + self.state.chunk_size < buf.len() {
                    let nw = HttpChunkedTransferWriter::send_chunk(
                        &mut self.fd,
                        self.state.chunk_size,
                        &buf[written..(written + self.state.chunk_size)],
                    )?;
                    written += nw;
                } else {
                    let nw = self.buf_chunk(&buf[written..]);
                    written += nw;
                }
            }
        }
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        // send out any buffered chunk data
        if !self.state.corked {
            self.flush_chunk().and_then(|nw| {
                if nw > 0 {
                    // send empty chunk
                    self.fd
                        .write_all(format!("0\r\n\r\n").as_bytes())
                        .and_then(|_nw| Ok(()))
                } else {
                    Ok(())
                }
            })
        } else {
            Ok(())
        }
    }
}

impl HttpRequestPreamble {
    pub fn new(
        version: HttpVersion,
        verb: String,
        path: String,
        hostname: String,
        port: u16,
        keep_alive: bool,
    ) -> HttpRequestPreamble {
        HttpRequestPreamble {
            version: version,
            verb: verb,
            path: path,
            host: PeerHost::from_host_port(hostname, port),
            content_type: None,
            content_length: None,
            keep_alive: keep_alive,
            headers: HashMap::new(),
        }
    }

    pub fn new_serialized<W: Write, F>(
        fd: &mut W,
        version: &HttpVersion,
        verb: &str,
        path: &str,
        host: &PeerHost,
        keep_alive: bool,
        content_length: Option<u32>,
        content_type: Option<&HttpContentType>,
        mut write_headers: F,
    ) -> Result<(), codec_error>
    where
        F: FnMut(&mut W) -> Result<(), codec_error>,
    {
        // "$verb $path HTTP/1.${version}\r\n"
        fd.write_all(verb.as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(" ".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(path.as_bytes())
            .map_err(codec_error::WriteError)?;

        match *version {
            HttpVersion::Http10 => {
                fd.write_all(" HTTP/1.0\r\n".as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
            HttpVersion::Http11 => {
                fd.write_all(" HTTP/1.1\r\n".as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
        }

        // "User-Agent: $agent\r\nHost: $host\r\n"
        fd.write_all("User-Agent: stacks/2.0\r\nHost: ".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(format!("{}", host).as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("\r\n".as_bytes())
            .map_err(codec_error::WriteError)?;

        // content-type
        match content_type {
            Some(ref c) => {
                fd.write_all("Content-Type: ".as_bytes())
                    .map_err(codec_error::WriteError)?;
                fd.write_all(c.as_str().as_bytes())
                    .map_err(codec_error::WriteError)?;
                fd.write_all("\r\n".as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
            None => {}
        }

        // content-length
        match content_length {
            Some(l) => {
                fd.write_all("Content-Length: ".as_bytes())
                    .map_err(codec_error::WriteError)?;
                fd.write_all(format!("{}", l).as_bytes())
                    .map_err(codec_error::WriteError)?;
                fd.write_all("\r\n".as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
            None => {}
        }

        match *version {
            HttpVersion::Http10 => {
                if keep_alive {
                    fd.write_all("Connection: keep-alive\r\n".as_bytes())
                        .map_err(codec_error::WriteError)?;
                }
            }
            HttpVersion::Http11 => {
                if !keep_alive {
                    fd.write_all("Connection: close\r\n".as_bytes())
                        .map_err(codec_error::WriteError)?;
                }
            }
        }

        // headers
        write_headers(fd)?;

        // end-of-headers
        fd.write_all("\r\n".as_bytes())
            .map_err(codec_error::WriteError)?;
        Ok(())
    }

    #[cfg(test)]
    pub fn from_headers(
        version: HttpVersion,
        verb: String,
        path: String,
        hostname: String,
        port: u16,
        keep_alive: bool,
        mut keys: Vec<String>,
        values: Vec<String>,
    ) -> HttpRequestPreamble {
        assert_eq!(keys.len(), values.len());
        let mut req = HttpRequestPreamble::new(version, verb, path, hostname, port, keep_alive);

        for (k, v) in keys.drain(..).zip(values) {
            req.add_header(k, v);
        }
        req
    }

    pub fn add_header(&mut self, key: String, value: String) -> () {
        let hdr = key.to_lowercase();
        if HttpReservedHeader::is_reserved(&hdr) {
            match HttpReservedHeader::try_from_str(&hdr, &value) {
                Some(h) => match h {
                    HttpReservedHeader::Host(ph) => {
                        self.host = ph;
                        return;
                    }
                    HttpReservedHeader::ContentType(ct) => {
                        self.content_type = Some(ct);
                        return;
                    }
                    _ => {} // can just fall through and insert
                },
                None => {
                    return;
                }
            }
        }

        self.headers.insert(hdr, value);
    }

    /// Content-Length for this request.
    /// If there is no valid Content-Length header, then
    /// the Content-Length is 0
    pub fn get_content_length(&self) -> u32 {
        self.content_length.unwrap_or(0)
    }

    /// Set the content-length for this request
    pub fn set_content_length(&mut self, len: u32) -> () {
        self.content_length = Some(len);
    }

    /// Set the content-type for this request
    pub fn set_content_type(&mut self, content_type: HttpContentType) -> () {
        self.content_type = Some(content_type)
    }
}

fn empty_headers<W: Write>(_fd: &mut W) -> Result<(), codec_error> {
    Ok(())
}

fn keep_alive_headers<W: Write>(fd: &mut W, md: &HttpResponseMetadata) -> Result<(), codec_error> {
    match md.client_version {
        HttpVersion::Http10 => {
            // client expects explicit keep-alive
            if md.client_keep_alive {
                fd.write_all("Connection: keep-alive\r\n".as_bytes())
                    .map_err(codec_error::WriteError)?;
            } else {
                fd.write_all("Connection: close\r\n".as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
        }
        HttpVersion::Http11 => {
            // only need "connection: close" if we're explicitly _not_ doing keep-alive
            if !md.client_keep_alive {
                fd.write_all("Connection: close\r\n".as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
        }
    }
    Ok(())
}

fn write_headers<W: Write>(
    fd: &mut W,
    headers: &HashMap<String, String>,
) -> Result<(), codec_error> {
    for (ref key, ref value) in headers.iter() {
        fd.write_all(key.as_str().as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(": ".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(value.as_str().as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("\r\n".as_bytes())
            .map_err(codec_error::WriteError)?;
    }
    Ok(())
}

fn default_accept_header() -> String {
    format!(
        "Accept: {}, {}, {}",
        HttpContentType::Bytes,
        HttpContentType::JSON,
        HttpContentType::Text
    )
}

/// Read from a stream until we see '\r\n\r\n', with the purpose of reading an HTTP preamble.
/// It's gonna be important here that R does some bufferring, since this reads byte by byte.
/// EOF if we read 0 bytes.
fn read_to_crlf2<R: Read>(fd: &mut R) -> Result<Vec<u8>, codec_error> {
    let mut ret = Vec::with_capacity(HTTP_PREAMBLE_MAX_ENCODED_SIZE as usize);
    while ret.len() < HTTP_PREAMBLE_MAX_ENCODED_SIZE as usize {
        let mut b = [0u8];
        fd.read_exact(&mut b).map_err(codec_error::ReadError)?;
        ret.push(b[0]);

        if ret.len() > 4 {
            let last_4 = &ret[(ret.len() - 4)..ret.len()];

            // '\r\n\r\n' is [0x0d, 0x0a, 0x0d, 0x0a]
            if last_4 == &[0x0d, 0x0a, 0x0d, 0x0a] {
                break;
            }
        }
    }
    Ok(ret)
}

impl StacksMessageCodec for HttpRequestPreamble {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        HttpRequestPreamble::new_serialized(
            fd,
            &self.version,
            &self.verb,
            &self.path,
            &self.host,
            self.keep_alive,
            self.content_length.clone(),
            self.content_type.as_ref(),
            |ref mut fd| write_headers(fd, &self.headers),
        )
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<HttpRequestPreamble, codec_error> {
        // realistically, there won't be more than HTTP_PREAMBLE_MAX_NUM_HEADERS headers
        let mut headers = [httparse::EMPTY_HEADER; HTTP_PREAMBLE_MAX_NUM_HEADERS];
        let mut req = httparse::Request::new(&mut headers);

        let buf_read = read_to_crlf2(fd)?;

        // consume request
        match req.parse(&buf_read).map_err(|e| {
            codec_error::DeserializeError(format!("Failed to parse HTTP request: {:?}", &e))
        })? {
            httparse::Status::Partial => {
                // partial
                return Err(codec_error::UnderflowError(
                    "Not enough bytes to form a HTTP request preamble".to_string(),
                ));
            }
            httparse::Status::Complete(_) => {
                // consumed all headers.  body_offset points to the start of the request body
                let version = match req
                    .version
                    .ok_or(codec_error::DeserializeError("No HTTP version".to_string()))?
                {
                    0 => HttpVersion::Http10,
                    1 => HttpVersion::Http11,
                    _ => {
                        return Err(codec_error::DeserializeError(
                            "Invalid HTTP version".to_string(),
                        ));
                    }
                };

                let verb = req
                    .method
                    .ok_or(codec_error::DeserializeError("No HTTP method".to_string()))?
                    .to_string();
                let path = req
                    .path
                    .ok_or(codec_error::DeserializeError("No HTTP path".to_string()))?
                    .to_string();

                let mut peerhost = None;
                let mut content_type = None;
                let mut content_length = None;
                let mut keep_alive = match version {
                    HttpVersion::Http10 => false,
                    HttpVersion::Http11 => true,
                };

                let mut headers: HashMap<String, String> = HashMap::new();
                let mut all_headers: HashSet<String> = HashSet::new();

                for i in 0..req.headers.len() {
                    let value = String::from_utf8(req.headers[i].value.to_vec()).map_err(|_e| {
                        codec_error::DeserializeError(
                            "Invalid HTTP header value: not utf-8".to_string(),
                        )
                    })?;
                    if !value.is_ascii() {
                        return Err(codec_error::DeserializeError(format!(
                            "Invalid HTTP request: header value is not ASCII-US"
                        )));
                    }
                    if value.len() > HTTP_PREAMBLE_MAX_ENCODED_SIZE as usize {
                        return Err(codec_error::DeserializeError(format!(
                            "Invalid HTTP request: header value is too big"
                        )));
                    }

                    let key = req.headers[i].name.to_string().to_lowercase();
                    if headers.contains_key(&key) || all_headers.contains(&key) {
                        return Err(codec_error::DeserializeError(format!(
                            "Invalid HTTP request: duplicate header \"{}\"",
                            key
                        )));
                    }
                    all_headers.insert(key.clone());

                    if key == "host" {
                        peerhost = match value.parse::<PeerHost>() {
                            Ok(ph) => Some(ph),
                            Err(_) => None,
                        };
                    } else if key == "content-type" {
                        // parse
                        let ctype = value.to_lowercase().parse::<HttpContentType>()?;
                        content_type = Some(ctype);
                    } else if key == "content-length" {
                        // parse
                        content_length = match value.parse::<u32>() {
                            Ok(len) => Some(len),
                            Err(_) => None,
                        }
                    } else if key == "connection" {
                        // parse
                        if value.to_lowercase() == "close" {
                            keep_alive = false;
                        } else if value.to_lowercase() == "keep-alive" {
                            keep_alive = true;
                        } else {
                            return Err(codec_error::DeserializeError(
                                "Inavlid HTTP request: invalid Connection: header".to_string(),
                            ));
                        }
                    } else {
                        headers.insert(key, value);
                    }
                }

                if peerhost.is_none() {
                    return Err(codec_error::DeserializeError(
                        "Missing Host header".to_string(),
                    ));
                };

                Ok(HttpRequestPreamble {
                    version: version,
                    verb: verb,
                    path: path,
                    host: peerhost.unwrap(),
                    content_type: content_type,
                    content_length: content_length,
                    keep_alive: keep_alive,
                    headers: headers,
                })
            }
        }
    }
}

impl HttpResponsePreamble {
    pub fn new(
        status_code: u16,
        reason: String,
        content_length_opt: Option<u32>,
        content_type: HttpContentType,
        keep_alive: bool,
        request_id: u32,
    ) -> HttpResponsePreamble {
        HttpResponsePreamble {
            status_code: status_code,
            reason: reason,
            keep_alive: keep_alive,
            content_length: content_length_opt,
            content_type: content_type,
            request_id: request_id,
            headers: HashMap::new(),
        }
    }

    pub fn ok_JSON_from_md<W: Write>(
        fd: &mut W,
        md: &HttpResponseMetadata,
    ) -> Result<(), codec_error> {
        HttpResponsePreamble::new_serialized(
            fd,
            200,
            "OK",
            md.content_length.clone(),
            &HttpContentType::JSON,
            md.request_id,
            |ref mut fd| keep_alive_headers(fd, md),
        )
    }

    pub fn new_serialized<W: Write, F>(
        fd: &mut W,
        status_code: u16,
        reason: &str,
        content_length: Option<u32>,
        content_type: &HttpContentType,
        request_id: u32,
        mut write_headers: F,
    ) -> Result<(), codec_error>
    where
        F: FnMut(&mut W) -> Result<(), codec_error>,
    {
        fd.write_all("HTTP/1.1 ".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(format!("{} {}\r\n", status_code, reason).as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("Server: stacks/2.0\r\nDate: ".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(rfc7231_now().as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("\r\nAccess-Control-Allow-Origin: *".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("\r\nAccess-Control-Allow-Headers: origin, content-type".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("\r\nAccess-Control-Allow-Methods: POST, GET, OPTIONS".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("\r\nContent-Type: ".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(content_type.as_str().as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all("\r\n".as_bytes())
            .map_err(codec_error::WriteError)?;

        match content_length {
            Some(len) => {
                fd.write_all("Content-Length: ".as_bytes())
                    .map_err(codec_error::WriteError)?;
                fd.write_all(format!("{}", len).as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
            None => {
                fd.write_all("Transfer-Encoding: chunked".as_bytes())
                    .map_err(codec_error::WriteError)?;
            }
        }

        fd.write_all("\r\nX-Request-Id: ".as_bytes())
            .map_err(codec_error::WriteError)?;
        fd.write_all(format!("{}\r\n", request_id).as_bytes())
            .map_err(codec_error::WriteError)?;

        write_headers(fd)?;

        fd.write_all("\r\n".as_bytes())
            .map_err(codec_error::WriteError)?;
        Ok(())
    }

    pub fn new_error(
        status_code: u16,
        request_id: u32,
        error_message: Option<String>,
    ) -> HttpResponsePreamble {
        HttpResponsePreamble {
            status_code: status_code,
            keep_alive: true,
            reason: HttpResponseType::error_reason(status_code).to_string(),
            content_length: Some(error_message.unwrap_or("".to_string()).len() as u32),
            content_type: HttpContentType::Text,
            request_id: request_id,
            headers: HashMap::new(),
        }
    }

    #[cfg(test)]
    pub fn from_headers(
        status_code: u16,
        reason: String,
        keep_alive: bool,
        content_length: Option<u32>,
        content_type: HttpContentType,
        request_id: u32,
        mut keys: Vec<String>,
        values: Vec<String>,
    ) -> HttpResponsePreamble {
        assert_eq!(keys.len(), values.len());
        let mut res = HttpResponsePreamble::new(
            status_code,
            reason,
            content_length,
            content_type,
            keep_alive,
            request_id,
        );

        for (k, v) in keys.drain(..).zip(values) {
            res.add_header(k, v);
        }
        res.set_request_id(request_id);
        res
    }

    pub fn add_header(&mut self, key: String, value: String) -> () {
        let hdr = key.to_lowercase();
        if HttpReservedHeader::is_reserved(&hdr) {
            match HttpReservedHeader::try_from_str(&hdr, &value) {
                Some(h) => match h {
                    HttpReservedHeader::XRequestID(rid) => {
                        self.request_id = rid;
                        return;
                    }
                    HttpReservedHeader::ContentLength(cl) => {
                        self.content_length = Some(cl);
                        return;
                    }
                    HttpReservedHeader::ContentType(ct) => {
                        self.content_type = ct;
                        return;
                    }
                    _ => {} // can just fall through and insert
                },
                None => {
                    return;
                }
            }
        }

        self.headers.insert(hdr, value);
    }

    pub fn set_request_id(&mut self, request_id: u32) -> () {
        self.request_id = request_id;
    }

    pub fn add_CORS_headers(&mut self) -> () {
        self.headers
            .insert("Access-Control-Allow-Origin".to_string(), "*".to_string());
    }

    // do we have Transfer-Encoding: chunked?
    pub fn is_chunked(&self) -> bool {
        self.content_length.is_none()
    }
}

/// Get an RFC 7231 date that represents the current time
fn rfc7231_now() -> String {
    let now = time::PrimitiveDateTime::from(SystemTime::now());
    now.format("%a, %b %-d %-Y %-H:%M:%S GMT")
}

impl StacksMessageCodec for HttpResponsePreamble {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        HttpResponsePreamble::new_serialized(
            fd,
            self.status_code,
            &self.reason,
            self.content_length,
            &self.content_type,
            self.request_id,
            |ref mut fd| write_headers(fd, &self.headers),
        )
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<HttpResponsePreamble, codec_error> {
        // realistically, there won't be more than HTTP_PREAMBLE_MAX_NUM_HEADERS headers
        let mut headers = [httparse::EMPTY_HEADER; HTTP_PREAMBLE_MAX_NUM_HEADERS];
        let mut resp = httparse::Response::new(&mut headers);

        let buf_read = read_to_crlf2(fd)?;

        // consume response
        match resp.parse(&buf_read).map_err(|e| {
            codec_error::DeserializeError(format!("Failed to parse HTTP response: {:?}", &e))
        })? {
            httparse::Status::Partial => {
                // try again
                return Err(codec_error::UnderflowError(
                    "Not enough bytes to form a HTTP response preamble".to_string(),
                ));
            }
            httparse::Status::Complete(_) => {
                // consumed all headers.  body_offset points to the start of the response body
                let _ = resp
                    .version
                    .ok_or(codec_error::DeserializeError("No HTTP version".to_string()))?;
                let status_code = resp.code.ok_or(codec_error::DeserializeError(
                    "No HTTP status code".to_string(),
                ))?;
                let reason = resp
                    .reason
                    .ok_or(codec_error::DeserializeError(
                        "No HTTP status reason".to_string(),
                    ))?
                    .to_string();

                let mut headers: HashMap<String, String> = HashMap::new();
                let mut all_headers: HashSet<String> = HashSet::new();

                let mut content_type = None;
                let mut content_length = None;
                let mut request_id = None;
                let mut chunked_encoding = false;
                let mut keep_alive = true;

                for i in 0..resp.headers.len() {
                    let value =
                        String::from_utf8(resp.headers[i].value.to_vec()).map_err(|_e| {
                            codec_error::DeserializeError(
                                "Invalid HTTP header value: not utf-8".to_string(),
                            )
                        })?;
                    if !value.is_ascii() {
                        return Err(codec_error::DeserializeError(format!(
                            "Invalid HTTP request: header value is not ASCII-US"
                        )));
                    }
                    if value.len() > HTTP_PREAMBLE_MAX_ENCODED_SIZE as usize {
                        return Err(codec_error::DeserializeError(format!(
                            "Invalid HTTP request: header value is too big"
                        )));
                    }

                    let key = resp.headers[i].name.to_string().to_lowercase();
                    if headers.contains_key(&key) || all_headers.contains(&key) {
                        return Err(codec_error::DeserializeError(format!(
                            "Invalid HTTP request: duplicate header \"{}\"",
                            key
                        )));
                    }
                    all_headers.insert(key.clone());

                    if key == "content-type" {
                        let ctype = value.to_lowercase().parse::<HttpContentType>()?;
                        content_type = Some(ctype);
                    } else if key == "content-length" {
                        let len = value.parse::<u32>().map_err(|_e| {
                            codec_error::DeserializeError(
                                "Invalid Content-Length header value".to_string(),
                            )
                        })?;
                        content_length = Some(len);
                    } else if key == "x-request-id" {
                        match value.parse::<u32>() {
                            Ok(i) => {
                                request_id = Some(i);
                            }
                            Err(_) => {}
                        }
                    } else if key == "connection" {
                        // parse
                        if value.to_lowercase() == "close" {
                            keep_alive = false;
                        } else if value.to_lowercase() == "keep-alive" {
                            keep_alive = true;
                        } else {
                            return Err(codec_error::DeserializeError(
                                "Inavlid HTTP request: invalid Connection: header".to_string(),
                            ));
                        }
                    } else if key == "transfer-encoding" {
                        if value.to_lowercase() == "chunked" {
                            chunked_encoding = true;
                        } else {
                            return Err(codec_error::DeserializeError(format!(
                                "Unsupported transfer-encoding '{}'",
                                value
                            )));
                        }
                    } else {
                        headers.insert(key, value);
                    }
                }

                if content_length.is_some() && chunked_encoding {
                    return Err(codec_error::DeserializeError(
                        "Invalid HTTP response: incompatible transfer-encoding and content-length"
                            .to_string(),
                    ));
                }

                if content_type.is_none() || (content_length.is_none() && !chunked_encoding) {
                    return Err(codec_error::DeserializeError(
                        "Invalid HTTP response: missing Content-Type, Content-Length".to_string(),
                    ));
                }

                Ok(HttpResponsePreamble {
                    status_code: status_code,
                    reason: reason,
                    keep_alive: keep_alive,
                    content_type: content_type.unwrap(),
                    content_length: content_length,
                    request_id: request_id.unwrap_or(HTTP_REQUEST_ID_RESERVED),
                    headers: headers,
                })
            }
        }
    }
}

impl HttpRequestType {
    fn try_parse<R: Read, F>(
        protocol: &mut StacksHttp,
        verb: &str,
        regex: &Regex,
        preamble: &HttpRequestPreamble,
        path: &str,
        query: Option<&str>,
        fd: &mut R,
        parser: F,
    ) -> Result<Option<HttpRequestType>, net_error>
    where
        F: Fn(
            &mut StacksHttp,
            &HttpRequestPreamble,
            &Captures,
            Option<&str>,
            &mut R,
        ) -> Result<HttpRequestType, net_error>,
    {
        if preamble.verb == verb {
            if let Some(ref captures) = regex.captures(path) {
                let payload = parser(protocol, preamble, captures, query, fd)?;
                return Ok(Some(payload));
            }
        }

        Ok(None)
    }

    pub fn parse<R: Read>(
        protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        // TODO: make this static somehow
        let REQUEST_METHODS: &[(
            &str,
            &Regex,
            &dyn Fn(
                &mut StacksHttp,
                &HttpRequestPreamble,
                &Captures,
                Option<&str>,
                &mut R,
            ) -> Result<HttpRequestType, net_error>,
        )] = &[
            ("GET", &PATH_GETINFO, &HttpRequestType::parse_getinfo),
            ("GET", &PATH_GETPOXINFO, &HttpRequestType::parse_getpoxinfo),
            (
                "GET",
                &PATH_GETNEIGHBORS,
                &HttpRequestType::parse_getneighbors,
            ),
            ("GET", &PATH_GETBLOCK, &HttpRequestType::parse_getblock),
            (
                "GET",
                &PATH_GETMICROBLOCKS_INDEXED,
                &HttpRequestType::parse_getmicroblocks_indexed,
            ),
            (
                "GET",
                &PATH_GETMICROBLOCKS_CONFIRMED,
                &HttpRequestType::parse_getmicroblocks_confirmed,
            ),
            (
                "GET",
                &PATH_GETMICROBLOCKS_UNCONFIRMED,
                &HttpRequestType::parse_getmicroblocks_unconfirmed,
            ),
            (
                "GET",
                &PATH_GETTRANSACTION_UNCONFIRMED,
                &HttpRequestType::parse_gettransaction_unconfirmed,
            ),
            (
                "POST",
                &PATH_POSTTRANSACTION,
                &HttpRequestType::parse_posttransaction,
            ),
            ("POST", &PATH_POSTBLOCK, &HttpRequestType::parse_postblock),
            (
                "POST",
                &PATH_POSTMICROBLOCK,
                &HttpRequestType::parse_postmicroblock,
            ),
            (
                "GET",
                &PATH_GET_ACCOUNT,
                &HttpRequestType::parse_get_account,
            ),
            (
                "POST",
                &PATH_GET_MAP_ENTRY,
                &HttpRequestType::parse_get_map_entry,
            ),
            (
                "GET",
                &PATH_GET_TRANSFER_COST,
                &HttpRequestType::parse_get_transfer_cost,
            ),
            (
                "GET",
                &PATH_GET_CONTRACT_SRC,
                &HttpRequestType::parse_get_contract_source,
            ),
            (
                "GET",
                &PATH_GET_IS_TRAIT_IMPLEMENTED,
                &HttpRequestType::parse_get_is_trait_implemented,
            ),
            (
                "GET",
                &PATH_GET_CONTRACT_ABI,
                &HttpRequestType::parse_get_contract_abi,
            ),
            (
                "POST",
                &PATH_POST_CALL_READ_ONLY,
                &HttpRequestType::parse_call_read_only,
            ),
            (
                "OPTIONS",
                &PATH_OPTIONS_WILDCARD,
                &HttpRequestType::parse_options_preflight,
            ),
            (
                "GET",
                &PATH_GET_ATTACHMENT,
                &HttpRequestType::parse_get_attachment,
            ),
            (
                "GET",
                &PATH_GET_ATTACHMENTS_INV,
                &HttpRequestType::parse_get_attachments_inv,
            ),
        ];

        // use url::Url to parse path and query string
        //   Url will refuse to parse just a path, so create a dummy URL
        let local_url = format!("http://local{}", &preamble.path);
        let url = Url::parse(&local_url).map_err(|_e| {
            net_error::DeserializeError("Http request path could not be parsed".to_string())
        })?;

        let decoded_path = percent_decode_str(url.path()).decode_utf8().map_err(|_e| {
            net_error::DeserializeError(
                "Http request path could not be parsed as UTF-8".to_string(),
            )
        })?;

        for (verb, regex, parser) in REQUEST_METHODS.iter() {
            match HttpRequestType::try_parse(
                protocol,
                verb,
                regex,
                preamble,
                &decoded_path,
                url.query(),
                fd,
                parser,
            )? {
                Some(request) => {
                    let query = if let Some(q) = url.query() {
                        format!("?{}", q)
                    } else {
                        "".to_string()
                    };
                    info!("Handle HTTPRequest"; "verb" => %verb, "peer_addr" => %protocol.peer_addr, "path" => %decoded_path, "query" => %query);
                    return Ok(request);
                }
                None => {
                    continue;
                }
            }
        }

        let _path = preamble.path.clone();
        test_debug!("Failed to parse '{}'", &_path);
        Err(net_error::ClientError(ClientError::NotFound(
            preamble.path.clone(),
        )))
    }

    fn parse_getinfo<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _regex: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetInfo".to_string(),
            ));
        }
        Ok(HttpRequestType::GetInfo(
            HttpRequestMetadata::from_preamble(preamble),
        ))
    }

    fn parse_getpoxinfo<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _regex: &Captures,
        query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetPoxInfo".to_string(),
            ));
        }

        let tip = HttpRequestType::get_chain_tip_query(query);

        Ok(HttpRequestType::GetPoxInfo(
            HttpRequestMetadata::from_preamble(preamble),
            tip,
        ))
    }

    fn parse_getneighbors<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _regex: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetNeighbors".to_string(),
            ));
        }

        Ok(HttpRequestType::GetNeighbors(
            HttpRequestMetadata::from_preamble(preamble),
        ))
    }

    fn parse_get_transfer_cost<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _regex: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetTransferCost".to_string(),
            ));
        }

        Ok(HttpRequestType::GetTransferCost(
            HttpRequestMetadata::from_preamble(preamble),
        ))
    }

    /// check whether the given option query string
    ///   sets proof=0 (setting proof to false).
    /// Defaults to _true_
    fn get_proof_query(query: Option<&str>) -> bool {
        let no_proof = if let Some(query_string) = query {
            form_urlencoded::parse(query_string.as_bytes())
                .find(|(key, _v)| key == "proof")
                .map(|(_k, value)| value == "0")
                .unwrap_or(false)
        } else {
            false
        };

        !no_proof
    }

    /// get the chain tip optional query argument (`tip`)
    /// Take the first value we can parse.
    fn get_chain_tip_query(query: Option<&str>) -> Option<StacksBlockId> {
        match query {
            Some(query_string) => {
                for (key, value) in form_urlencoded::parse(query_string.as_bytes()) {
                    if key != "tip" {
                        continue;
                    }

                    if let Ok(tip) = StacksBlockId::from_hex(&value) {
                        return Some(tip);
                    }
                }
                return None;
            }
            None => {
                return None;
            }
        }
    }

    fn parse_get_account<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetAccount".to_string(),
            ));
        }

        let principal = PrincipalData::parse(&captures["principal"]).map_err(|_e| {
            net_error::DeserializeError("Failed to parse account principal".into())
        })?;

        let with_proof = HttpRequestType::get_proof_query(query);
        let tip = HttpRequestType::get_chain_tip_query(query);

        Ok(HttpRequestType::GetAccount(
            HttpRequestMetadata::from_preamble(preamble),
            principal,
            tip,
            with_proof,
        ))
    }

    fn parse_get_map_entry<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        query: Option<&str>,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        let content_len = preamble.get_content_length();
        if !(content_len > 0 && content_len < (BOUND_VALUE_SERIALIZATION_HEX)) {
            return Err(net_error::DeserializeError(format!(
                "Invalid Http request: invalid body length for GetMapEntry ({})",
                content_len
            )));
        }

        if preamble.content_type != Some(HttpContentType::JSON) {
            return Err(net_error::DeserializeError(
                "Invalid content-type: expected application/json".into(),
            ));
        }

        let contract_addr = StacksAddress::from_string(&captures["address"]).ok_or_else(|| {
            net_error::DeserializeError("Failed to parse contract address".into())
        })?;
        let contract_name = ContractName::try_from(captures["contract"].to_string())
            .map_err(|_e| net_error::DeserializeError("Failed to parse contract name".into()))?;
        let map_name = ClarityName::try_from(captures["map"].to_string())
            .map_err(|_e| net_error::DeserializeError("Failed to parse contract name".into()))?;

        let value_hex: String = serde_json::from_reader(fd)
            .map_err(|_e| net_error::DeserializeError("Failed to parse JSON body".into()))?;

        let value = Value::try_deserialize_hex_untyped(&value_hex)
            .map_err(|_e| net_error::DeserializeError("Failed to deserialize key value".into()))?;

        let with_proof = HttpRequestType::get_proof_query(query);
        let tip = HttpRequestType::get_chain_tip_query(query);

        Ok(HttpRequestType::GetMapEntry(
            HttpRequestMetadata::from_preamble(preamble),
            contract_addr,
            contract_name,
            map_name,
            value,
            tip,
            with_proof,
        ))
    }

    fn parse_call_read_only<R: Read>(
        protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        query: Option<&str>,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        let content_len = preamble.get_content_length();
        if !(content_len > 0 && content_len < protocol.maximum_call_argument_size) {
            return Err(net_error::DeserializeError(format!(
                "Invalid Http request: invalid body length for CallReadOnly ({})",
                content_len
            )));
        }

        if preamble.content_type != Some(HttpContentType::JSON) {
            return Err(net_error::DeserializeError(
                "Invalid content-type: expected application/json".to_string(),
            ));
        }

        let contract_addr = StacksAddress::from_string(&captures["address"]).ok_or_else(|| {
            net_error::DeserializeError("Failed to parse contract address".into())
        })?;
        let contract_name = ContractName::try_from(captures["contract"].to_string())
            .map_err(|_e| net_error::DeserializeError("Failed to parse contract name".into()))?;
        let func_name = ClarityName::try_from(captures["function"].to_string())
            .map_err(|_e| net_error::DeserializeError("Failed to parse contract name".into()))?;

        let body: CallReadOnlyRequestBody = serde_json::from_reader(fd)
            .map_err(|_e| net_error::DeserializeError("Failed to parse JSON body".into()))?;

        let sender = PrincipalData::parse(&body.sender)
            .map_err(|_e| net_error::DeserializeError("Failed to parse sender principal".into()))?;

        let arguments = body
            .arguments
            .into_iter()
            .map(|hex| Value::try_deserialize_hex_untyped(&hex).ok())
            .collect::<Option<Vec<Value>>>()
            .ok_or_else(|| {
                net_error::DeserializeError("Failed to deserialize argument value".into())
            })?;

        let tip = HttpRequestType::get_chain_tip_query(query);

        Ok(HttpRequestType::CallReadOnlyFunction(
            HttpRequestMetadata::from_preamble(preamble),
            contract_addr,
            contract_name,
            sender,
            func_name,
            arguments,
            tip,
        ))
    }

    fn parse_get_contract_arguments(
        preamble: &HttpRequestPreamble,
        captures: &Captures,
    ) -> Result<(HttpRequestMetadata, StacksAddress, ContractName), net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body".to_string(),
            ));
        }

        let contract_addr = StacksAddress::from_string(&captures["address"]).ok_or_else(|| {
            net_error::DeserializeError("Failed to parse contract address".into())
        })?;
        let contract_name = ContractName::try_from(captures["contract"].to_string())
            .map_err(|_e| net_error::DeserializeError("Failed to parse contract name".into()))?;

        Ok((
            HttpRequestMetadata::from_preamble(preamble),
            contract_addr,
            contract_name,
        ))
    }

    fn parse_get_contract_abi<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        let tip = HttpRequestType::get_chain_tip_query(query);
        HttpRequestType::parse_get_contract_arguments(preamble, captures).map(
            |(preamble, addr, name)| HttpRequestType::GetContractABI(preamble, addr, name, tip),
        )
    }

    fn parse_get_contract_source<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        let with_proof = HttpRequestType::get_proof_query(query);
        let tip = HttpRequestType::get_chain_tip_query(query);
        HttpRequestType::parse_get_contract_arguments(preamble, captures).map(
            |(preamble, addr, name)| {
                HttpRequestType::GetContractSrc(preamble, addr, name, tip, with_proof)
            },
        )
    }

    fn parse_get_is_trait_implemented<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        let tip = HttpRequestType::get_chain_tip_query(query);
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body".to_string(),
            ));
        }

        let contract_addr = StacksAddress::from_string(&captures["address"]).ok_or_else(|| {
            net_error::DeserializeError("Failed to parse contract address".into())
        })?;
        let contract_name = ContractName::try_from(captures["contract"].to_string())
            .map_err(|_e| net_error::DeserializeError("Failed to parse contract name".into()))?;
        let trait_name = ClarityName::try_from(captures["traitName"].to_string())
            .map_err(|_e| net_error::DeserializeError("Failed to parse trait name".into()))?;
        let trait_contract_addr = StacksAddress::from_string(&captures["traitContractAddr"])
            .ok_or_else(|| net_error::DeserializeError("Failed to parse contract address".into()))?
            .into();
        let trait_contract_name = ContractName::try_from(captures["traitContractName"].to_string())
            .map_err(|_e| {
                net_error::DeserializeError("Failed to parse trait contract name".into())
            })?;
        let trait_id = TraitIdentifier::new(trait_contract_addr, trait_contract_name, trait_name);

        Ok(HttpRequestType::GetIsTraitImplemented(
            HttpRequestMetadata::from_preamble(preamble),
            contract_addr,
            contract_name,
            trait_id,
            tip,
        ))
    }

    fn parse_getblock<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetBlock".to_string(),
            ));
        }

        let block_hash_str = captures
            .get(1)
            .ok_or(net_error::DeserializeError(
                "Failed to match path to block hash group".to_string(),
            ))?
            .as_str();

        let block_hash = StacksBlockId::from_hex(block_hash_str)
            .map_err(|_e| net_error::DeserializeError("Failed to parse block hash".to_string()))?;

        Ok(HttpRequestType::GetBlock(
            HttpRequestMetadata::from_preamble(preamble),
            block_hash,
        ))
    }

    fn parse_getmicroblocks_indexed<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetMicroblocksIndexed"
                    .to_string(),
            ));
        }

        let block_hash_str = captures
            .get(1)
            .ok_or(net_error::DeserializeError(
                "Failed to match path to microblock hash group".to_string(),
            ))?
            .as_str();

        let block_hash = StacksBlockId::from_hex(block_hash_str).map_err(|_e| {
            net_error::DeserializeError("Failed to parse microblock hash".to_string())
        })?;

        Ok(HttpRequestType::GetMicroblocksIndexed(
            HttpRequestMetadata::from_preamble(preamble),
            block_hash,
        ))
    }

    fn parse_getmicroblocks_confirmed<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetMicrolocks".to_string(),
            ));
        }

        let block_hash_str = captures
            .get(1)
            .ok_or(net_error::DeserializeError(
                "Failed to match path to microblock hash group".to_string(),
            ))?
            .as_str();

        let block_hash = StacksBlockId::from_hex(block_hash_str).map_err(|_e| {
            net_error::DeserializeError("Failed to parse microblock hash".to_string())
        })?;

        Ok(HttpRequestType::GetMicroblocksConfirmed(
            HttpRequestMetadata::from_preamble(preamble),
            block_hash,
        ))
    }

    fn parse_getmicroblocks_unconfirmed<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetMicrolocksUnconfirmed"
                    .to_string(),
            ));
        }

        let block_hash_str = captures
            .get(1)
            .ok_or(net_error::DeserializeError(
                "Failed to match path to microblock hash group".to_string(),
            ))?
            .as_str();

        let min_seq_str = captures
            .get(2)
            .ok_or(net_error::DeserializeError(
                "Failed to match path to microblock minimum sequence group".to_string(),
            ))?
            .as_str();

        let block_hash = StacksBlockId::from_hex(block_hash_str).map_err(|_e| {
            net_error::DeserializeError("Failed to parse microblock hash".to_string())
        })?;

        let min_seq = min_seq_str.parse::<u16>().map_err(|_e| {
            net_error::DeserializeError("Failed to parse microblock minimum sequence".to_string())
        })?;

        Ok(HttpRequestType::GetMicroblocksUnconfirmed(
            HttpRequestMetadata::from_preamble(preamble),
            block_hash,
            min_seq,
        ))
    }

    fn parse_gettransaction_unconfirmed<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        regex: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body for GetMicrolocksUnconfirmed"
                    .to_string(),
            ));
        }

        let txid_hex = regex
            .get(1)
            .ok_or(net_error::DeserializeError(
                "Failed to match path to txid group".to_string(),
            ))?
            .as_str();

        if txid_hex.len() != 64 {
            return Err(net_error::DeserializeError(
                "Invalid txid: expected 64 bytes".to_string(),
            ));
        }

        let txid = Txid::from_hex(&txid_hex)
            .map_err(|_e| net_error::DeserializeError("Failed to decode txid hex".to_string()))?;

        Ok(HttpRequestType::GetTransactionUnconfirmed(
            HttpRequestMetadata::from_preamble(preamble),
            txid,
        ))
    }

    fn parse_posttransaction<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _regex: &Captures,
        _query: Option<&str>,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() == 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected non-zero-length body for PostTransaction"
                    .to_string(),
            ));
        }

        if preamble.get_content_length() > MAX_PAYLOAD_LEN {
            return Err(net_error::DeserializeError(
                "Invalid Http request: PostTransaction body is too big".to_string(),
            ));
        }

        let mut bound_fd = BoundReader::from_reader(fd, preamble.get_content_length() as u64);

        match preamble.content_type {
            None => {
                return Err(net_error::DeserializeError(
                    "Missing Content-Type for transaction".to_string(),
                ));
            }
            Some(HttpContentType::Bytes) => {
                HttpRequestType::parse_posttransaction_octets(preamble, &mut bound_fd)
            }
            Some(HttpContentType::JSON) => {
                HttpRequestType::parse_posttransaction_json(preamble, &mut bound_fd)
            }
            _ => {
                return Err(net_error::DeserializeError(
                    "Wrong Content-Type for transaction; expected application/json".to_string(),
                ));
            }
        }
    }

    fn parse_posttransaction_octets<R: Read>(
        preamble: &HttpRequestPreamble,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        let tx = StacksTransaction::consensus_deserialize(fd).map_err(|e| {
            if let codec_error::DeserializeError(msg) = e {
                net_error::ClientError(ClientError::Message(format!(
                    "Failed to deserialize posted transaction: {}",
                    msg
                )))
            } else {
                e.into()
            }
        })?;
        Ok(HttpRequestType::PostTransaction(
            HttpRequestMetadata::from_preamble(preamble),
            tx,
            None,
        ))
    }

    fn parse_posttransaction_json<R: Read>(
        preamble: &HttpRequestPreamble,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        let body: PostTransactionRequestBody = serde_json::from_reader(fd)
            .map_err(|_e| net_error::DeserializeError("Failed to parse body".into()))?;

        let tx = {
            let tx_bytes = hex_bytes(&body.tx)
                .map_err(|_e| net_error::DeserializeError("Failed to parse tx".into()))?;
            StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).map_err(|e| {
                if let codec_error::DeserializeError(msg) = e {
                    net_error::ClientError(ClientError::Message(format!(
                        "Failed to deserialize posted transaction: {}",
                        msg
                    )))
                } else {
                    e.into()
                }
            })
        }?;

        let attachment = match body.attachment {
            None => None,
            Some(attachment_content) => {
                let content = hex_bytes(&attachment_content).map_err(|_e| {
                    net_error::DeserializeError("Failed to parse attachment".into())
                })?;
                Some(Attachment::new(content))
            }
        };

        Ok(HttpRequestType::PostTransaction(
            HttpRequestMetadata::from_preamble(preamble),
            tx,
            attachment,
        ))
    }

    fn parse_postblock<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        regex: &Captures,
        _query: Option<&str>,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() == 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected non-zero-length body for PostBlock".to_string(),
            ));
        }

        if preamble.get_content_length() > MAX_PAYLOAD_LEN {
            return Err(net_error::DeserializeError(
                "Invalid Http request: PostBlock body is too big".to_string(),
            ));
        }

        // content-type must be given, and must be application/octet-stream
        match preamble.content_type {
            None => {
                return Err(net_error::DeserializeError(
                    "Missing Content-Type for Stacks block".to_string(),
                ));
            }
            Some(ref c) => {
                if *c != HttpContentType::Bytes {
                    return Err(net_error::DeserializeError(
                        "Wrong Content-Type for Stacks block; expected application/octet-stream"
                            .to_string(),
                    ));
                }
            }
        };

        let consensus_hash_str = regex
            .get(1)
            .ok_or(net_error::DeserializeError(
                "Failed to match consensus hash in path group".to_string(),
            ))?
            .as_str();

        let consensus_hash: ConsensusHash =
            ConsensusHash::from_hex(consensus_hash_str).map_err(|_| {
                net_error::DeserializeError("Failed to parse consensus hash".to_string())
            })?;

        let mut bound_fd = BoundReader::from_reader(fd, preamble.get_content_length() as u64);
        let stacks_block = StacksBlock::consensus_deserialize(&mut bound_fd)?;

        Ok(HttpRequestType::PostBlock(
            HttpRequestMetadata::from_preamble(preamble),
            consensus_hash,
            stacks_block,
        ))
    }

    fn parse_postmicroblock<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _regex: &Captures,
        query: Option<&str>,
        fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() == 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected non-zero-length body for PostMicroblock"
                    .to_string(),
            ));
        }

        if preamble.get_content_length() > MAX_PAYLOAD_LEN {
            return Err(net_error::DeserializeError(
                "Invalid Http request: PostMicroblock body is too big".to_string(),
            ));
        }

        // content-type must be given, and must be application/octet-stream
        match preamble.content_type {
            None => {
                return Err(net_error::DeserializeError(
                    "Missing Content-Type for microblock".to_string(),
                ));
            }
            Some(ref c) => {
                if *c != HttpContentType::Bytes {
                    return Err(net_error::DeserializeError(
                        "Wrong Content-Type for microblock; expected application/octet-stream"
                            .to_string(),
                    ));
                }
            }
        };

        let mut bound_fd = BoundReader::from_reader(fd, preamble.get_content_length() as u64);

        let mb = StacksMicroblock::consensus_deserialize(&mut bound_fd)?;
        let tip = HttpRequestType::get_chain_tip_query(query);

        Ok(HttpRequestType::PostMicroblock(
            HttpRequestMetadata::from_preamble(preamble),
            mb,
            tip,
        ))
    }

    fn parse_get_attachment<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        captures: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body".to_string(),
            ));
        }
        let hex_content_hash = captures
            .get(1)
            .ok_or(net_error::DeserializeError(
                "Failed to match path to attachment hash group".to_string(),
            ))?
            .as_str();

        let content_hash = Hash160::from_hex(&hex_content_hash).map_err(|_| {
            net_error::DeserializeError("Failed to construct hash160 from inputs".to_string())
        })?;

        Ok(HttpRequestType::GetAttachment(
            HttpRequestMetadata::from_preamble(preamble),
            content_hash,
        ))
    }

    fn parse_get_attachments_inv<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _captures: &Captures,
        query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        if preamble.get_content_length() != 0 {
            return Err(net_error::DeserializeError(
                "Invalid Http request: expected 0-length body".to_string(),
            ));
        }

        let (index_block_hash, pages_indexes) = match query {
            None => {
                return Err(net_error::DeserializeError(
                    "Invalid Http request: expecting index_block_hash and pages_indexes"
                        .to_string(),
                ));
            }
            Some(query) => {
                let mut index_block_hash = None;
                let mut pages_indexes = HashSet::new();

                for (key, value) in form_urlencoded::parse(query.as_bytes()) {
                    if key == "index_block_hash" {
                        index_block_hash = match StacksBlockId::from_hex(&value) {
                            Ok(index_block_hash) => Some(index_block_hash),
                            _ => None,
                        };
                    } else if key == "pages_indexes" {
                        if let Ok(pages_indexes_value) = value.parse::<String>() {
                            for entry in pages_indexes_value.split(",") {
                                if let Ok(page_index) = entry.parse::<u32>() {
                                    pages_indexes.insert(page_index);
                                }
                            }
                        }
                    }
                }

                let index_block_hash = match index_block_hash {
                    None => {
                        return Err(net_error::DeserializeError(
                            "Invalid Http request: expecting index_block_hash".to_string(),
                        ));
                    }
                    Some(index_block_hash) => index_block_hash,
                };

                if pages_indexes.is_empty() {
                    return Err(net_error::DeserializeError(
                        "Invalid Http request: expecting pages_indexes".to_string(),
                    ));
                }

                (index_block_hash, pages_indexes)
            }
        };

        Ok(HttpRequestType::GetAttachmentsInv(
            HttpRequestMetadata::from_preamble(preamble),
            index_block_hash,
            pages_indexes,
        ))
    }

    fn parse_options_preflight<R: Read>(
        _protocol: &mut StacksHttp,
        preamble: &HttpRequestPreamble,
        _regex: &Captures,
        _query: Option<&str>,
        _fd: &mut R,
    ) -> Result<HttpRequestType, net_error> {
        Ok(HttpRequestType::OptionsPreflight(
            HttpRequestMetadata::from_preamble(preamble),
            preamble.path.to_string(),
        ))
    }

    pub fn metadata(&self) -> &HttpRequestMetadata {
        match *self {
            HttpRequestType::GetInfo(ref md) => md,
            HttpRequestType::GetPoxInfo(ref md, _) => md,
            HttpRequestType::GetNeighbors(ref md) => md,
            HttpRequestType::GetBlock(ref md, _) => md,
            HttpRequestType::GetMicroblocksIndexed(ref md, _) => md,
            HttpRequestType::GetMicroblocksConfirmed(ref md, _) => md,
            HttpRequestType::GetMicroblocksUnconfirmed(ref md, _, _) => md,
            HttpRequestType::GetTransactionUnconfirmed(ref md, _) => md,
            HttpRequestType::PostTransaction(ref md, _, _) => md,
            HttpRequestType::PostBlock(ref md, ..) => md,
            HttpRequestType::PostMicroblock(ref md, ..) => md,
            HttpRequestType::GetAccount(ref md, ..) => md,
            HttpRequestType::GetMapEntry(ref md, ..) => md,
            HttpRequestType::GetTransferCost(ref md) => md,
            HttpRequestType::GetContractABI(ref md, ..) => md,
            HttpRequestType::GetContractSrc(ref md, ..) => md,
            HttpRequestType::GetIsTraitImplemented(ref md, ..) => md,
            HttpRequestType::CallReadOnlyFunction(ref md, ..) => md,
            HttpRequestType::OptionsPreflight(ref md, ..) => md,
            HttpRequestType::GetAttachmentsInv(ref md, ..) => md,
            HttpRequestType::GetAttachment(ref md, ..) => md,
            HttpRequestType::ClientError(ref md, ..) => md,
        }
    }

    pub fn metadata_mut(&mut self) -> &mut HttpRequestMetadata {
        match *self {
            HttpRequestType::GetInfo(ref mut md) => md,
            HttpRequestType::GetPoxInfo(ref mut md, _) => md,
            HttpRequestType::GetNeighbors(ref mut md) => md,
            HttpRequestType::GetBlock(ref mut md, _) => md,
            HttpRequestType::GetMicroblocksIndexed(ref mut md, _) => md,
            HttpRequestType::GetMicroblocksConfirmed(ref mut md, _) => md,
            HttpRequestType::GetMicroblocksUnconfirmed(ref mut md, _, _) => md,
            HttpRequestType::GetTransactionUnconfirmed(ref mut md, _) => md,
            HttpRequestType::PostTransaction(ref mut md, _, _) => md,
            HttpRequestType::PostBlock(ref mut md, ..) => md,
            HttpRequestType::PostMicroblock(ref mut md, ..) => md,
            HttpRequestType::GetAccount(ref mut md, ..) => md,
            HttpRequestType::GetMapEntry(ref mut md, ..) => md,
            HttpRequestType::GetTransferCost(ref mut md) => md,
            HttpRequestType::GetContractABI(ref mut md, ..) => md,
            HttpRequestType::GetContractSrc(ref mut md, ..) => md,
            HttpRequestType::GetIsTraitImplemented(ref mut md, ..) => md,
            HttpRequestType::CallReadOnlyFunction(ref mut md, ..) => md,
            HttpRequestType::OptionsPreflight(ref mut md, ..) => md,
            HttpRequestType::GetAttachmentsInv(ref mut md, ..) => md,
            HttpRequestType::GetAttachment(ref mut md, ..) => md,
            HttpRequestType::ClientError(ref mut md, ..) => md,
        }
    }

    fn make_query_string(tip_opt: Option<&StacksBlockId>, with_proof: bool) -> String {
        if let Some(tip) = tip_opt {
            format!("?tip={}{}", tip, if with_proof { "" } else { "&proof=0" })
        } else if !with_proof {
            format!("?proof=0")
        } else {
            "".to_string()
        }
    }

    pub fn request_path(&self) -> String {
        match self {
            HttpRequestType::GetInfo(_md) => "/v2/info".to_string(),
            HttpRequestType::GetPoxInfo(_md, tip_opt) => format!(
                "/v2/pox{}",
                HttpRequestType::make_query_string(tip_opt.as_ref(), true)
            ),
            HttpRequestType::GetNeighbors(_md) => "/v2/neighbors".to_string(),
            HttpRequestType::GetBlock(_md, block_hash) => {
                format!("/v2/blocks/{}", block_hash.to_hex())
            }
            HttpRequestType::GetMicroblocksIndexed(_md, block_hash) => {
                format!("/v2/microblocks/{}", block_hash.to_hex())
            }
            HttpRequestType::GetMicroblocksConfirmed(_md, block_hash) => {
                format!("/v2/microblocks/confirmed/{}", block_hash.to_hex())
            }
            HttpRequestType::GetMicroblocksUnconfirmed(_md, block_hash, min_seq) => format!(
                "/v2/microblocks/unconfirmed/{}/{}",
                block_hash.to_hex(),
                min_seq
            ),
            HttpRequestType::GetTransactionUnconfirmed(_md, txid) => {
                format!("/v2/transactions/unconfirmed/{}", txid)
            }
            HttpRequestType::PostTransaction(_md, ..) => "/v2/transactions".to_string(),
            HttpRequestType::PostBlock(_md, ch, ..) => format!("/v2/blocks/upload/{}", &ch),
            HttpRequestType::PostMicroblock(_md, _, tip_opt) => format!(
                "/v2/microblocks{}",
                HttpRequestType::make_query_string(tip_opt.as_ref(), true)
            ),
            HttpRequestType::GetAccount(_md, principal, tip_opt, with_proof) => format!(
                "/v2/accounts/{}{}",
                &principal.to_string(),
                HttpRequestType::make_query_string(tip_opt.as_ref(), *with_proof)
            ),
            HttpRequestType::GetMapEntry(
                _md,
                contract_addr,
                contract_name,
                map_name,
                _key,
                tip_opt,
                with_proof,
            ) => format!(
                "/v2/map_entry/{}/{}/{}{}",
                &contract_addr.to_string(),
                contract_name.as_str(),
                map_name.as_str(),
                HttpRequestType::make_query_string(tip_opt.as_ref(), *with_proof)
            ),
            HttpRequestType::GetTransferCost(_md) => "/v2/fees/transfer".into(),
            HttpRequestType::GetContractABI(_, contract_addr, contract_name, tip_opt) => format!(
                "/v2/contracts/interface/{}/{}{}",
                contract_addr,
                contract_name.as_str(),
                HttpRequestType::make_query_string(tip_opt.as_ref(), true)
            ),
            HttpRequestType::GetContractSrc(
                _,
                contract_addr,
                contract_name,
                tip_opt,
                with_proof,
            ) => format!(
                "/v2/contracts/source/{}/{}{}",
                contract_addr,
                contract_name.as_str(),
                HttpRequestType::make_query_string(tip_opt.as_ref(), *with_proof)
            ),
            HttpRequestType::GetIsTraitImplemented(
                _,
                contract_addr,
                contract_name,
                trait_id,
                tip_opt,
            ) => format!(
                "/v2/traits/{}/{}/{}/{}/{}{}",
                contract_addr,
                contract_name.as_str(),
                trait_id.name.to_string(),
                StacksAddress::from(trait_id.clone().contract_identifier.issuer),
                trait_id.contract_identifier.name.as_str(),
                HttpRequestType::make_query_string(tip_opt.as_ref(), true)
            ),
            HttpRequestType::CallReadOnlyFunction(
                _,
                contract_addr,
                contract_name,
                _,
                func_name,
                _,
                tip_opt,
            ) => format!(
                "/v2/contracts/call-read/{}/{}/{}{}",
                contract_addr,
                contract_name.as_str(),
                func_name.as_str(),
                HttpRequestType::make_query_string(tip_opt.as_ref(), true)
            ),
            HttpRequestType::OptionsPreflight(_md, path) => path.to_string(),
            HttpRequestType::GetAttachmentsInv(_md, index_block_hash, pages_indexes) => {
                let pages_query = match pages_indexes.len() {
                    0 => format!(""),
                    _n => {
                        let mut indexes = pages_indexes
                            .iter()
                            .map(|i| format!("{}", i))
                            .collect::<Vec<String>>();
                        indexes.sort();
                        format!("&pages_indexes={}", indexes.join(","))
                    }
                };
                let index_block_hash = format!("index_block_hash={}", index_block_hash);
                format!("/v2/attachments/inv?{}{}", index_block_hash, pages_query,)
            }
            HttpRequestType::GetAttachment(_, content_hash) => {
                format!("/v2/attachments/{}", to_hex(&content_hash.0[..]))
            }
            HttpRequestType::ClientError(_md, e) => match e {
                ClientError::NotFound(path) => path.to_string(),
                _ => "error path unknown".into(),
            },
        }
    }

    pub fn get_path(&self) -> &str {
        match self {
            HttpRequestType::GetInfo(..) => "/v2/info",
            HttpRequestType::GetPoxInfo(..) => "/v2/pox",
            HttpRequestType::GetNeighbors(..) => "/v2/neighbors",
            HttpRequestType::GetBlock(..) => "/v2/blocks/:hash",
            HttpRequestType::GetMicroblocksIndexed(..) => "/v2/microblocks/:hash",
            HttpRequestType::GetMicroblocksConfirmed(..) => "/v2/microblocks/confirmed/:hash",
            HttpRequestType::GetMicroblocksUnconfirmed(..) => {
                "/v2/microblocks/unconfirmed/:hash/:seq"
            }
            HttpRequestType::GetTransactionUnconfirmed(..) => "/v2/transactions/unconfirmed/:txid",
            HttpRequestType::PostTransaction(..) => "/v2/transactions",
            HttpRequestType::PostBlock(..) => "/v2/blocks/upload/:block",
            HttpRequestType::PostMicroblock(..) => "/v2/microblocks",
            HttpRequestType::GetAccount(..) => "/v2/accounts/:principal",
            HttpRequestType::GetMapEntry(..) => "/v2/map_entry/:principal/:contract_name/:map_name",
            HttpRequestType::GetTransferCost(..) => "/v2/fees/transfer",
            HttpRequestType::GetContractABI(..) => {
                "/v2/contracts/interface/:principal/:contract_name"
            }
            HttpRequestType::GetContractSrc(..) => "/v2/contracts/source/:principal/:contract_name",
            HttpRequestType::CallReadOnlyFunction(..) => {
                "/v2/contracts/call-read/:principal/:contract_name/:func_name"
            }
            HttpRequestType::GetAttachmentsInv(..) => "/v2/attachments/inv",
            HttpRequestType::GetAttachment(..) => "/v2/attachments/:hash",
            HttpRequestType::GetIsTraitImplemented(..) => "/v2/traits/:principal/:contract_name",
            HttpRequestType::OptionsPreflight(..) | HttpRequestType::ClientError(..) => "/",
        }
    }

    pub fn send<W: Write>(&self, _protocol: &mut StacksHttp, fd: &mut W) -> Result<(), net_error> {
        match self {
            HttpRequestType::PostTransaction(md, tx, attachment) => {
                let mut tx_bytes = vec![];
                write_next(&mut tx_bytes, tx)?;
                let tx_hex = to_hex(&tx_bytes[..]);

                let (content_type, request_body_bytes) = match attachment {
                    None => {
                        // Transaction does not include an attachment: HttpContentType::Bytes (more compressed)
                        (Some(&HttpContentType::Bytes), tx_bytes)
                    }
                    Some(attachment) => {
                        // Transaction is including an attachment: HttpContentType::JSON
                        let request_body = PostTransactionRequestBody {
                            tx: tx_hex,
                            attachment: Some(to_hex(&attachment.content[..])),
                        };

                        let mut request_body_bytes = vec![];
                        serde_json::to_writer(&mut request_body_bytes, &request_body).map_err(
                            |e| {
                                net_error::SerializeError(format!(
                                    "Failed to serialize read-only call to JSON: {:?}",
                                    &e
                                ))
                            },
                        )?;
                        (Some(&HttpContentType::JSON), request_body_bytes)
                    }
                };

                HttpRequestPreamble::new_serialized(
                    fd,
                    &md.version,
                    "POST",
                    &self.request_path(),
                    &md.peer,
                    md.keep_alive,
                    Some(request_body_bytes.len() as u32),
                    content_type,
                    empty_headers,
                )?;
                fd.write_all(&request_body_bytes)
                    .map_err(net_error::WriteError)?;
            }
            HttpRequestType::PostBlock(md, _ch, block) => {
                let mut block_bytes = vec![];
                write_next(&mut block_bytes, block)?;

                HttpRequestPreamble::new_serialized(
                    fd,
                    &md.version,
                    "POST",
                    &self.request_path(),
                    &md.peer,
                    md.keep_alive,
                    Some(block_bytes.len() as u32),
                    Some(&HttpContentType::Bytes),
                    empty_headers,
                )?;
                fd.write_all(&block_bytes).map_err(net_error::WriteError)?;
            }
            HttpRequestType::PostMicroblock(md, mb, ..) => {
                let mut mb_bytes = vec![];
                write_next(&mut mb_bytes, mb)?;

                HttpRequestPreamble::new_serialized(
                    fd,
                    &md.version,
                    "POST",
                    &self.request_path(),
                    &md.peer,
                    md.keep_alive,
                    Some(mb_bytes.len() as u32),
                    Some(&HttpContentType::Bytes),
                    empty_headers,
                )?;
                fd.write_all(&mb_bytes).map_err(net_error::WriteError)?;
            }
            HttpRequestType::GetMapEntry(
                md,
                _contract_addr,
                _contract_name,
                _map_name,
                key,
                ..,
            ) => {
                let mut request_bytes = vec![];
                key.serialize_write(&mut request_bytes)
                    .map_err(net_error::WriteError)?;
                let request_json = format!("\"{}\"", to_hex(&request_bytes));

                HttpRequestPreamble::new_serialized(
                    fd,
                    &md.version,
                    "POST",
                    &self.request_path(),
                    &md.peer,
                    md.keep_alive,
                    Some(request_json.as_bytes().len() as u32),
                    Some(&HttpContentType::JSON),
                    empty_headers,
                )?;
                fd.write_all(&request_json.as_bytes())
                    .map_err(net_error::WriteError)?;
            }
            HttpRequestType::CallReadOnlyFunction(
                md,
                _contract_addr,
                _contract_name,
                sender,
                _func_name,
                func_args,
                ..,
            ) => {
                let mut args = vec![];
                for arg in func_args.iter() {
                    let mut arg_bytes = vec![];
                    arg.serialize_write(&mut arg_bytes)
                        .map_err(net_error::WriteError)?;
                    args.push(to_hex(&arg_bytes));
                }

                let request_body = CallReadOnlyRequestBody {
                    sender: sender.to_string(),
                    arguments: args,
                };

                let mut request_body_bytes = vec![];
                serde_json::to_writer(&mut request_body_bytes, &request_body).map_err(|e| {
                    net_error::SerializeError(format!(
                        "Failed to serialize read-only call to JSON: {:?}",
                        &e
                    ))
                })?;

                HttpRequestPreamble::new_serialized(
                    fd,
                    &md.version,
                    "POST",
                    &self.request_path(),
                    &md.peer,
                    md.keep_alive,
                    Some(request_body_bytes.len() as u32),
                    Some(&HttpContentType::JSON),
                    empty_headers,
                )?;
                fd.write_all(&request_body_bytes)
                    .map_err(net_error::WriteError)?;
            }
            other_type => {
                let md = other_type.metadata();
                let request_path = other_type.request_path();
                HttpRequestPreamble::new_serialized(
                    fd,
                    &md.version,
                    "GET",
                    &request_path,
                    &md.peer,
                    md.keep_alive,
                    None,
                    None,
                    empty_headers,
                )?;
            }
        }
        Ok(())
    }
}

impl HttpResponseType {
    fn try_parse<R: Read, F>(
        protocol: &mut StacksHttp,
        regex: &Regex,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        request_path: &String,
        fd: &mut R,
        len_hint: Option<usize>,
        parser: F,
    ) -> Result<Option<HttpResponseType>, net_error>
    where
        F: Fn(
            &mut StacksHttp,
            HttpVersion,
            &HttpResponsePreamble,
            &mut R,
            Option<usize>,
        ) -> Result<HttpResponseType, net_error>,
    {
        if regex.is_match(request_path) {
            let payload = parser(protocol, request_version, preamble, fd, len_hint)?;
            Ok(Some(payload))
        } else {
            Ok(None)
        }
    }

    fn parse_error<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
    ) -> Result<HttpResponseType, net_error> {
        if preamble.status_code < 400 || preamble.status_code > 599 {
            return Err(net_error::DeserializeError(
                "Inavlid response: not an error".to_string(),
            ));
        }

        if preamble.content_type != HttpContentType::Text {
            return Err(net_error::DeserializeError(
                "Invalid error response: expected text/plain".to_string(),
            ));
        }

        let mut error_text = String::new();
        fd.read_to_string(&mut error_text)
            .map_err(net_error::ReadError)?;

        let md = HttpResponseMetadata::from_preamble(request_version, preamble);
        let resp = match preamble.status_code {
            400 => HttpResponseType::BadRequest(md, error_text),
            401 => HttpResponseType::Unauthorized(md, error_text),
            402 => HttpResponseType::PaymentRequired(md, error_text),
            403 => HttpResponseType::Forbidden(md, error_text),
            404 => HttpResponseType::NotFound(md, error_text),
            500 => HttpResponseType::ServerError(md, error_text),
            503 => HttpResponseType::ServiceUnavailable(md, error_text),
            _ => HttpResponseType::Error(md, preamble.status_code, error_text),
        };
        Ok(resp)
    }

    fn parse_bytestream<R: Read, T: StacksMessageCodec>(
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
        max_len: u64,
    ) -> Result<T, net_error> {
        // content-type has to be Bytes
        if preamble.content_type != HttpContentType::Bytes {
            return Err(net_error::DeserializeError(
                "Invalid content-type: expected application/octet-stream".to_string(),
            ));
        }

        let item: T = if preamble.is_chunked() && len_hint.is_none() {
            let mut chunked_fd = HttpChunkedTransferReader::from_reader(fd, max_len);
            read_next(&mut chunked_fd)?
        } else {
            let content_length_opt = match (preamble.content_length, len_hint) {
                (Some(l), _) => Some(l as u32),
                (None, Some(l)) => Some(l as u32),
                (None, None) => None,
            };
            if let Some(content_length) = content_length_opt {
                if (content_length as u64) > max_len {
                    return Err(net_error::DeserializeError(
                        "Invalid Content-Length header: too long".to_string(),
                    ));
                }

                let mut bound_fd = BoundReader::from_reader(fd, content_length as u64);
                read_next(&mut bound_fd)?
            } else {
                // unsupported headers
                trace!("preamble: {:?}", preamble);
                return Err(net_error::DeserializeError(
                    "Invalid headers: need either Transfer-Encoding or Content-Length".to_string(),
                ));
            }
        };

        Ok(item)
    }

    fn parse_json<R: Read, T: serde::de::DeserializeOwned>(
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
        max_len: u64,
    ) -> Result<T, net_error> {
        // content-type has to be JSON
        if preamble.content_type != HttpContentType::JSON {
            return Err(net_error::DeserializeError(
                "Invalid content-type: expected application/json".to_string(),
            ));
        }

        let item_result: Result<T, serde_json::Error> = if preamble.is_chunked()
            && len_hint.is_none()
        {
            let chunked_fd = HttpChunkedTransferReader::from_reader(fd, max_len);
            serde_json::from_reader(chunked_fd)
        } else {
            let content_length_opt = match (preamble.content_length, len_hint) {
                (Some(l), _) => Some(l as u32),
                (None, Some(l)) => Some(l as u32),
                (None, None) => None,
            };
            if let Some(content_length) = content_length_opt {
                if (content_length as u64) > max_len {
                    return Err(net_error::DeserializeError(
                        "Invalid Content-Length header: too long".to_string(),
                    ));
                }
                let bound_fd = BoundReader::from_reader(fd, content_length as u64);
                serde_json::from_reader(bound_fd)
            } else {
                // unsupported headers
                trace!("preamble: {:?}", preamble);
                return Err(net_error::DeserializeError(
                    "Invalid headers: need either Transfer-Encoding or Content-Length".to_string(),
                ));
            }
        };

        item_result.map_err(|e| {
            if e.is_eof() {
                net_error::UnderflowError(format!("Not enough bytes to parse JSON"))
            } else {
                net_error::DeserializeError(format!("Failed to parse JSON: {:?}", &e))
            }
        })
    }

    fn parse_text<R: Read>(
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
        max_len: u64,
    ) -> Result<Vec<u8>, net_error> {
        // content-type has to be text/plain
        if preamble.content_type != HttpContentType::Text {
            return Err(net_error::DeserializeError(
                "Invalid content-type: expected text/plain".to_string(),
            ));
        }
        let buf = if preamble.is_chunked() && len_hint.is_none() {
            let mut chunked_fd = HttpChunkedTransferReader::from_reader(fd, max_len);
            let mut buf = vec![];
            chunked_fd
                .read_to_end(&mut buf)
                .map_err(net_error::ReadError)?;
            buf
        } else {
            let content_length_opt = match (preamble.content_length, len_hint) {
                (Some(l), _) => Some(l as u32),
                (None, Some(l)) => Some(l as u32),
                (None, None) => None,
            };
            if let Some(len) = content_length_opt {
                let mut buf = vec![0u8; len as usize];
                fd.read_exact(&mut buf).map_err(net_error::ReadError)?;
                buf
            } else {
                // unsupported headers
                trace!("preamble: {:?}", preamble);
                return Err(net_error::DeserializeError(
                    "Invalid headers: need either Transfer-Encoding or Content-Length".to_string(),
                ));
            }
        };

        Ok(buf)
    }

    // len_hint is given by the StacksHttp protocol implementation
    pub fn parse<R: Read>(
        protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        request_path: String,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        if preamble.status_code >= 400 {
            return HttpResponseType::parse_error(protocol, request_version, preamble, fd);
        }

        // TODO: make this static somehow
        let RESPONSE_METHODS: &[(
            &Regex,
            &dyn Fn(
                &mut StacksHttp,
                HttpVersion,
                &HttpResponsePreamble,
                &mut R,
                Option<usize>,
            ) -> Result<HttpResponseType, net_error>,
        )] = &[
            (&PATH_GETINFO, &HttpResponseType::parse_peerinfo),
            (&PATH_GETPOXINFO, &HttpResponseType::parse_poxinfo),
            (&PATH_GETNEIGHBORS, &HttpResponseType::parse_neighbors),
            (&PATH_GETBLOCK, &HttpResponseType::parse_block),
            (&PATH_GET_MAP_ENTRY, &HttpResponseType::parse_get_map_entry),
            (
                &PATH_GETMICROBLOCKS_INDEXED,
                &HttpResponseType::parse_microblocks,
            ),
            (
                &PATH_GETMICROBLOCKS_CONFIRMED,
                &HttpResponseType::parse_microblocks,
            ),
            (
                &PATH_GETMICROBLOCKS_UNCONFIRMED,
                &HttpResponseType::parse_microblocks_unconfirmed,
            ),
            (
                &PATH_GETTRANSACTION_UNCONFIRMED,
                &HttpResponseType::parse_transaction_unconfirmed,
            ),
            (&PATH_POSTTRANSACTION, &HttpResponseType::parse_txid),
            (
                &PATH_POSTBLOCK,
                &HttpResponseType::parse_stacks_block_accepted,
            ),
            (
                &PATH_POSTMICROBLOCK,
                &HttpResponseType::parse_microblock_hash,
            ),
            (&PATH_GET_ACCOUNT, &HttpResponseType::parse_get_account),
            (
                &PATH_GET_CONTRACT_SRC,
                &HttpResponseType::parse_get_contract_src,
            ),
            (
                &PATH_GET_IS_TRAIT_IMPLEMENTED,
                &HttpResponseType::parse_get_is_trait_implemented,
            ),
            (
                &PATH_GET_CONTRACT_ABI,
                &HttpResponseType::parse_get_contract_abi,
            ),
            (
                &PATH_POST_CALL_READ_ONLY,
                &HttpResponseType::parse_call_read_only,
            ),
            (
                &PATH_GET_ATTACHMENT,
                &HttpResponseType::parse_get_attachment,
            ),
            (
                &PATH_GET_ATTACHMENTS_INV,
                &HttpResponseType::parse_get_attachments_inv,
            ),
        ];

        // use url::Url to parse path and query string
        //   Url will refuse to parse just a path, so create a dummy URL
        let local_url = format!("http://local{}", &request_path);
        let url = Url::parse(&local_url).map_err(|_e| {
            net_error::DeserializeError("Http request path could not be parsed".to_string())
        })?;

        let decoded_path = percent_decode_str(url.path()).decode_utf8().map_err(|_e| {
            net_error::DeserializeError(
                "Http response path could not be parsed as UTF-8".to_string(),
            )
        })?;

        for (regex, parser) in RESPONSE_METHODS.iter() {
            match HttpResponseType::try_parse(
                protocol,
                regex,
                request_version,
                preamble,
                &decoded_path.to_string(),
                fd,
                len_hint,
                parser,
            ) {
                Ok(Some(request)) => {
                    return Ok(request);
                }
                Ok(None) => {
                    continue;
                }
                Err(e) => {
                    test_debug!("Failed to parse {}: {:?}", &request_path, &e);
                    return Err(e);
                }
            }
        }

        test_debug!(
            "Failed to match request path '{}' to a handler",
            &request_path
        );
        return Err(net_error::DeserializeError(
            "Http response could not be parsed".to_string(),
        ));
    }

    fn parse_peerinfo<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let peer_info =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::PeerInfo(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            peer_info,
        ))
    }

    fn parse_poxinfo<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let pox_info =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::PoxInfo(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            pox_info,
        ))
    }

    fn parse_neighbors<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let neighbors_data =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::Neighbors(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            neighbors_data,
        ))
    }

    fn parse_block<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let block: StacksBlock =
            HttpResponseType::parse_bytestream(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::Block(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            block,
        ))
    }

    fn parse_microblocks<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let microblocks: Vec<StacksMicroblock> =
            HttpResponseType::parse_bytestream(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::Microblocks(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            microblocks,
        ))
    }

    fn parse_get_account<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let account_entry =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::GetAccount(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            account_entry,
        ))
    }

    fn parse_get_map_entry<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let map_entry =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::GetMapEntry(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            map_entry,
        ))
    }

    fn parse_get_contract_src<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let src_data =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::GetContractSrc(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            src_data,
        ))
    }

    fn parse_get_is_trait_implemented<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let src_data =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::GetIsTraitImplemented(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            src_data,
        ))
    }

    fn parse_get_contract_abi<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let abi = HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::GetContractABI(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            abi,
        ))
    }

    fn parse_call_read_only<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let call_data =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;
        Ok(HttpResponseType::CallReadOnlyFunction(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            call_data,
        ))
    }

    fn parse_microblocks_unconfirmed<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        // NOTE: there will be no length prefix on this, but we won't ever get more than
        // MAX_MICROBLOCKS_UNCONFIRMED microblocks
        let mut microblocks = vec![];
        let max_len = len_hint.unwrap_or(MAX_MESSAGE_LEN as usize) as u64;
        let mut bound_reader = BoundReader::from_reader(fd, max_len);
        loop {
            let mblock: StacksMicroblock = match read_next(&mut bound_reader) {
                Ok(mblock) => Ok(mblock),
                Err(e) => match e {
                    codec_error::ReadError(ref ioe) => match ioe.kind() {
                        io::ErrorKind::UnexpectedEof => {
                            // end of stream -- this is fine
                            break;
                        }
                        _ => Err(e),
                    },
                    _ => Err(e),
                },
            }?;

            microblocks.push(mblock);
            if microblocks.len() == MAX_MICROBLOCKS_UNCONFIRMED {
                break;
            }
        }
        Ok(HttpResponseType::Microblocks(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            microblocks,
        ))
    }

    fn parse_transaction_unconfirmed<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let unconfirmed_status: UnconfirmedTransactionResponse =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;

        // tx payload must decode to a transaction
        let tx_bytes = hex_bytes(&unconfirmed_status.tx).map_err(|_| {
            net_error::DeserializeError("Unconfirmed transaction is not hex-encoded".to_string())
        })?;
        let _ = StacksTransaction::consensus_deserialize(&mut &tx_bytes[..]).map_err(|_| {
            net_error::DeserializeError(
                "Unconfirmed transaction is not a well-formed Stacks transaction".to_string(),
            )
        })?;

        Ok(HttpResponseType::UnconfirmedTransaction(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            unconfirmed_status,
        ))
    }

    fn parse_txid<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let txid_hex: String = HttpResponseType::parse_json(preamble, fd, len_hint, 66)?;
        if txid_hex.len() != 64 {
            return Err(net_error::DeserializeError(
                "Invalid txid: expected 64 bytes".to_string(),
            ));
        }

        let txid = Txid::from_hex(&txid_hex)
            .map_err(|_e| net_error::DeserializeError("Failed to decode txid hex".to_string()))?;
        Ok(HttpResponseType::TransactionID(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            txid,
        ))
    }

    fn parse_get_attachment<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let res: GetAttachmentResponse =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;

        Ok(HttpResponseType::GetAttachment(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            res,
        ))
    }

    fn parse_get_attachments_inv<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let res: GetAttachmentsInvResponse =
            HttpResponseType::parse_json(preamble, fd, len_hint, MAX_MESSAGE_LEN as u64)?;

        Ok(HttpResponseType::GetAttachmentsInv(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            res,
        ))
    }

    fn parse_stacks_block_accepted<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let stacks_block_accepted: StacksBlockAcceptedData =
            HttpResponseType::parse_json(preamble, fd, len_hint, 128)?;
        Ok(HttpResponseType::StacksBlockAccepted(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            stacks_block_accepted.stacks_block_id,
            stacks_block_accepted.accepted,
        ))
    }

    fn parse_microblock_hash<R: Read>(
        _protocol: &mut StacksHttp,
        request_version: HttpVersion,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
        len_hint: Option<usize>,
    ) -> Result<HttpResponseType, net_error> {
        let mblock_hex: String = HttpResponseType::parse_json(preamble, fd, len_hint, 66)?;
        if mblock_hex.len() != 64 {
            return Err(net_error::DeserializeError(
                "Invalid microblock hash: expected 64 bytes".to_string(),
            ));
        }

        let mblock_hash = BlockHeaderHash::from_hex(&mblock_hex).map_err(|_e| {
            net_error::DeserializeError("Failed to decode microblock hash hex".to_string())
        })?;
        Ok(HttpResponseType::MicroblockHash(
            HttpResponseMetadata::from_preamble(request_version, preamble),
            mblock_hash,
        ))
    }

    fn error_reason(code: u16) -> &'static str {
        match code {
            400 => "Bad Request",
            401 => "Unauthorized",
            402 => "Payment Required",
            403 => "Forbidden",
            404 => "Not Found",
            500 => "Internal Server Error",
            503 => "Service Temporarily Unavailable",
            _ => "Error",
        }
    }

    fn error_response<W: Write>(
        &self,
        fd: &mut W,
        code: u16,
        message: &str,
    ) -> Result<(), net_error> {
        let md = self.metadata();
        HttpResponsePreamble::new_serialized(
            fd,
            code,
            HttpResponseType::error_reason(code),
            Some(message.len() as u32),
            &HttpContentType::Text,
            md.request_id,
            |ref mut fd| keep_alive_headers(fd, md),
        )?;
        fd.write_all(message.as_bytes())
            .map_err(net_error::WriteError)?;
        Ok(())
    }

    pub fn metadata(&self) -> &HttpResponseMetadata {
        match *self {
            HttpResponseType::PeerInfo(ref md, _) => md,
            HttpResponseType::PoxInfo(ref md, _) => md,
            HttpResponseType::Neighbors(ref md, _) => md,
            HttpResponseType::Block(ref md, _) => md,
            HttpResponseType::BlockStream(ref md) => md,
            HttpResponseType::Microblocks(ref md, _) => md,
            HttpResponseType::MicroblockStream(ref md) => md,
            HttpResponseType::TransactionID(ref md, _) => md,
            HttpResponseType::StacksBlockAccepted(ref md, ..) => md,
            HttpResponseType::MicroblockHash(ref md, _) => md,
            HttpResponseType::TokenTransferCost(ref md, _) => md,
            HttpResponseType::GetMapEntry(ref md, _) => md,
            HttpResponseType::GetAccount(ref md, _) => md,
            HttpResponseType::GetContractABI(ref md, _) => md,
            HttpResponseType::GetContractSrc(ref md, _) => md,
            HttpResponseType::GetIsTraitImplemented(ref md, _) => md,
            HttpResponseType::CallReadOnlyFunction(ref md, _) => md,
            HttpResponseType::UnconfirmedTransaction(ref md, _) => md,
            HttpResponseType::GetAttachment(ref md, _) => md,
            HttpResponseType::GetAttachmentsInv(ref md, _) => md,
            HttpResponseType::OptionsPreflight(ref md) => md,
            // errors
            HttpResponseType::BadRequestJSON(ref md, _) => md,
            HttpResponseType::BadRequest(ref md, _) => md,
            HttpResponseType::Unauthorized(ref md, _) => md,
            HttpResponseType::PaymentRequired(ref md, _) => md,
            HttpResponseType::Forbidden(ref md, _) => md,
            HttpResponseType::NotFound(ref md, _) => md,
            HttpResponseType::ServerError(ref md, _) => md,
            HttpResponseType::ServiceUnavailable(ref md, _) => md,
            HttpResponseType::Error(ref md, _, _) => md,
        }
    }

    fn send_bytestream<W: Write, T: StacksMessageCodec>(
        protocol: &mut StacksHttp,
        md: &HttpResponseMetadata,
        fd: &mut W,
        message: &T,
    ) -> Result<(), codec_error> {
        if md.content_length.is_some() {
            // have explicit content-length, so we can send as-is
            write_next(fd, message)
        } else {
            // no content-length, so send as chunk-encoded
            let mut write_state = HttpChunkedTransferWriterState::new(protocol.chunk_size as usize);
            let mut encoder = HttpChunkedTransferWriter::from_writer_state(fd, &mut write_state);
            write_next(&mut encoder, message)?;
            encoder.flush().map_err(codec_error::WriteError)?;
            Ok(())
        }
    }

    fn send_text<W: Write>(
        protocol: &mut StacksHttp,
        md: &HttpResponseMetadata,
        fd: &mut W,
        text: &[u8],
    ) -> Result<(), net_error> {
        if md.content_length.is_some() {
            // have explicit content-length, so we can send as-is
            fd.write_all(text).map_err(net_error::WriteError)
        } else {
            // no content-length, so send as chunk-encoded
            let mut write_state = HttpChunkedTransferWriterState::new(protocol.chunk_size as usize);
            let mut encoder = HttpChunkedTransferWriter::from_writer_state(fd, &mut write_state);
            encoder.write_all(text).map_err(net_error::WriteError)?;
            encoder.flush().map_err(net_error::WriteError)?;
            Ok(())
        }
    }

    fn send_json<W: Write, T: serde::ser::Serialize>(
        protocol: &mut StacksHttp,
        md: &HttpResponseMetadata,
        fd: &mut W,
        message: &T,
    ) -> Result<(), net_error> {
        if md.content_length.is_some() {
            // have explicit content-length, so we can send as-is
            serde_json::to_writer(fd, message)
                .map_err(|e| net_error::SerializeError(format!("Failed to send as JSON: {:?}", &e)))
        } else {
            // no content-length, so send as chunk-encoded
            let mut write_state = HttpChunkedTransferWriterState::new(protocol.chunk_size as usize);
            let mut encoder = HttpChunkedTransferWriter::from_writer_state(fd, &mut write_state);
            serde_json::to_writer(&mut encoder, message).map_err(|e| {
                net_error::SerializeError(format!("Failed to send as chunk-encoded JSON: {:?}", &e))
            })?;
            encoder.flush().map_err(net_error::WriteError)?;
            Ok(())
        }
    }

    pub fn send<W: Write>(&self, protocol: &mut StacksHttp, fd: &mut W) -> Result<(), net_error> {
        match *self {
            HttpResponseType::GetAccount(ref md, ref account_data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, account_data)?;
            }
            HttpResponseType::GetContractABI(ref md, ref data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, data)?;
            }
            HttpResponseType::GetContractSrc(ref md, ref data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, data)?;
            }
            HttpResponseType::GetIsTraitImplemented(ref md, ref data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, data)?;
            }
            HttpResponseType::TokenTransferCost(ref md, ref cost) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, cost)?;
            }
            HttpResponseType::CallReadOnlyFunction(ref md, ref data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, data)?;
            }
            HttpResponseType::GetMapEntry(ref md, ref map_data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, map_data)?;
            }
            HttpResponseType::PeerInfo(ref md, ref peer_info) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, peer_info)?;
            }
            HttpResponseType::PoxInfo(ref md, ref pox_info) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, pox_info)?;
            }
            HttpResponseType::Neighbors(ref md, ref neighbor_data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, neighbor_data)?;
            }
            HttpResponseType::GetAttachment(ref md, ref zonefile_data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, zonefile_data)?;
            }
            HttpResponseType::GetAttachmentsInv(ref md, ref zonefile_data) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, zonefile_data)?;
            }
            HttpResponseType::Block(ref md, ref block) => {
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    md.content_length.clone(),
                    &HttpContentType::Bytes,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
                HttpResponseType::send_bytestream(protocol, md, fd, block)?;
            }
            HttpResponseType::BlockStream(ref md) => {
                // only send the preamble.  The caller will need to figure out how to send along
                // the block data itself.
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    None,
                    &HttpContentType::Bytes,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
            }
            HttpResponseType::Microblocks(ref md, ref microblocks) => {
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    md.content_length.clone(),
                    &HttpContentType::Bytes,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
                HttpResponseType::send_bytestream(protocol, md, fd, microblocks)?;
            }
            HttpResponseType::MicroblockStream(ref md) => {
                // only send the preamble.  The caller will need to figure out how to send along
                // the microblock data itself.
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    None,
                    &HttpContentType::Bytes,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
            }
            HttpResponseType::TransactionID(ref md, ref txid) => {
                let txid_bytes = txid.to_hex();
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    md.content_length.clone(),
                    &HttpContentType::JSON,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
                HttpResponseType::send_json(protocol, md, fd, &txid_bytes)?;
            }
            HttpResponseType::StacksBlockAccepted(ref md, ref stacks_block_id, ref accepted) => {
                let accepted_data = StacksBlockAcceptedData {
                    stacks_block_id: stacks_block_id.clone(),
                    accepted: *accepted,
                };
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    md.content_length.clone(),
                    &HttpContentType::JSON,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
                HttpResponseType::send_json(protocol, md, fd, &accepted_data)?;
            }
            HttpResponseType::MicroblockHash(ref md, ref mblock_hash) => {
                let mblock_bytes = mblock_hash.to_hex();
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    md.content_length.clone(),
                    &HttpContentType::JSON,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
                HttpResponseType::send_json(protocol, md, fd, &mblock_bytes)?;
            }
            HttpResponseType::UnconfirmedTransaction(ref md, ref unconfirmed_status) => {
                HttpResponsePreamble::ok_JSON_from_md(fd, md)?;
                HttpResponseType::send_json(protocol, md, fd, unconfirmed_status)?;
            }
            HttpResponseType::OptionsPreflight(ref md) => {
                HttpResponsePreamble::new_serialized(
                    fd,
                    200,
                    "OK",
                    None,
                    &HttpContentType::Text,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
                HttpResponseType::send_text(protocol, md, fd, "".as_bytes())?;
            }
            HttpResponseType::BadRequestJSON(ref md, ref data) => {
                HttpResponsePreamble::new_serialized(
                    fd,
                    400,
                    HttpResponseType::error_reason(400),
                    md.content_length.clone(),
                    &HttpContentType::JSON,
                    md.request_id,
                    |ref mut fd| keep_alive_headers(fd, md),
                )?;
                HttpResponseType::send_json(protocol, md, fd, data)?;
            }
            HttpResponseType::BadRequest(_, ref msg) => self.error_response(fd, 400, msg)?,
            HttpResponseType::Unauthorized(_, ref msg) => self.error_response(fd, 401, msg)?,
            HttpResponseType::PaymentRequired(_, ref msg) => self.error_response(fd, 402, msg)?,
            HttpResponseType::Forbidden(_, ref msg) => self.error_response(fd, 403, msg)?,
            HttpResponseType::NotFound(_, ref msg) => self.error_response(fd, 404, msg)?,
            HttpResponseType::ServerError(_, ref msg) => self.error_response(fd, 500, msg)?,
            HttpResponseType::ServiceUnavailable(_, ref msg) => {
                self.error_response(fd, 503, msg)?
            }
            HttpResponseType::Error(_, ref error_code, ref msg) => {
                self.error_response(fd, *error_code, msg)?
            }
        };
        Ok(())
    }
}

impl StacksMessageCodec for StacksHttpPreamble {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        match *self {
            StacksHttpPreamble::Request(ref req) => req.consensus_serialize(fd),
            StacksHttpPreamble::Response(ref res) => res.consensus_serialize(fd),
        }
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<StacksHttpPreamble, codec_error> {
        let mut retry_fd = RetryReader::new(fd);

        // the byte stream can decode to a http request or a http response, but not both.
        match HttpRequestPreamble::consensus_deserialize(&mut retry_fd) {
            Ok(request) => Ok(StacksHttpPreamble::Request(request)),
            Err(e_request) => {
                // maybe a http response?
                retry_fd.set_position(0);
                match HttpResponsePreamble::consensus_deserialize(&mut retry_fd) {
                    Ok(response) => Ok(StacksHttpPreamble::Response(response)),
                    Err(e) => {
                        // underflow?
                        match (e_request, e) {
                            (codec_error::ReadError(ref ioe1), codec_error::ReadError(ref ioe2)) => {
                                if ioe1.kind() == io::ErrorKind::UnexpectedEof && ioe2.kind() == io::ErrorKind::UnexpectedEof {
                                    // out of bytes
                                    Err(codec_error::UnderflowError("Not enough bytes to form a HTTP request or response".to_string()))
                                }
                                else {
                                    Err(codec_error::DeserializeError(format!("Neither a HTTP request ({:?}) or HTTP response ({:?})", ioe1, ioe2)))
                                }
                            },
                            (e_req, e_res) => Err(codec_error::DeserializeError(format!("Failed to decode HTTP request or HTTP response (request error: {:?}; response error: {:?})", &e_req, &e_res)))
                        }
                    }
                }
            }
        }
    }
}

impl MessageSequence for StacksHttpMessage {
    fn request_id(&self) -> u32 {
        // there is at most one in-flight HTTP request, as far as a Connection<P> is concerned
        HTTP_REQUEST_ID_RESERVED
    }

    fn get_message_name(&self) -> &'static str {
        match *self {
            StacksHttpMessage::Request(ref req) => match req {
                HttpRequestType::GetInfo(_) => "HTTP(GetInfo)",
                HttpRequestType::GetPoxInfo(_, _) => "HTTP(GetPoxInfo)",
                HttpRequestType::GetNeighbors(_) => "HTTP(GetNeighbors)",
                HttpRequestType::GetBlock(_, _) => "HTTP(GetBlock)",
                HttpRequestType::GetMicroblocksIndexed(_, _) => "HTTP(GetMicroblocksIndexed)",
                HttpRequestType::GetMicroblocksConfirmed(_, _) => "HTTP(GetMicroblocksConfirmed)",
                HttpRequestType::GetMicroblocksUnconfirmed(_, _, _) => {
                    "HTTP(GetMicroblocksUnconfirmed)"
                }
                HttpRequestType::GetTransactionUnconfirmed(_, _) => {
                    "HTTP(GetTransactionUnconfirmed)"
                }
                HttpRequestType::PostTransaction(_, _, _) => "HTTP(PostTransaction)",
                HttpRequestType::PostBlock(..) => "HTTP(PostBlock)",
                HttpRequestType::PostMicroblock(..) => "HTTP(PostMicroblock)",
                HttpRequestType::GetAccount(..) => "HTTP(GetAccount)",
                HttpRequestType::GetMapEntry(..) => "HTTP(GetMapEntry)",
                HttpRequestType::GetTransferCost(_) => "HTTP(GetTransferCost)",
                HttpRequestType::GetContractABI(..) => "HTTP(GetContractABI)",
                HttpRequestType::GetContractSrc(..) => "HTTP(GetContractSrc)",
                HttpRequestType::GetIsTraitImplemented(..) => "HTTP(GetIsTraitImplemented)",
                HttpRequestType::CallReadOnlyFunction(..) => "HTTP(CallReadOnlyFunction)",
                HttpRequestType::GetAttachment(..) => "HTTP(GetAttachment)",
                HttpRequestType::GetAttachmentsInv(..) => "HTTP(GetAttachmentsInv)",
                HttpRequestType::OptionsPreflight(..) => "HTTP(OptionsPreflight)",
                HttpRequestType::ClientError(..) => "HTTP(ClientError)",
            },
            StacksHttpMessage::Response(ref res) => match res {
                HttpResponseType::TokenTransferCost(_, _) => "HTTP(TokenTransferCost)",
                HttpResponseType::GetMapEntry(_, _) => "HTTP(GetMapEntry)",
                HttpResponseType::GetAccount(_, _) => "HTTP(GetAccount)",
                HttpResponseType::GetContractABI(..) => "HTTP(GetContractABI)",
                HttpResponseType::GetContractSrc(..) => "HTTP(GetContractSrc)",
                HttpResponseType::GetIsTraitImplemented(..) => "HTTP(GetIsTraitImplemented)",
                HttpResponseType::CallReadOnlyFunction(..) => "HTTP(CallReadOnlyFunction)",
                HttpResponseType::GetAttachment(_, _) => "HTTP(GetAttachment)",
                HttpResponseType::GetAttachmentsInv(_, _) => "HTTP(GetAttachmentsInv)",
                HttpResponseType::PeerInfo(_, _) => "HTTP(PeerInfo)",
                HttpResponseType::PoxInfo(_, _) => "HTTP(PeerInfo)",
                HttpResponseType::Neighbors(_, _) => "HTTP(Neighbors)",
                HttpResponseType::Block(_, _) => "HTTP(Block)",
                HttpResponseType::BlockStream(_) => "HTTP(BlockStream)",
                HttpResponseType::Microblocks(_, _) => "HTTP(Microblocks)",
                HttpResponseType::MicroblockStream(_) => "HTTP(MicroblockStream)",
                HttpResponseType::TransactionID(_, _) => "HTTP(Transaction)",
                HttpResponseType::StacksBlockAccepted(..) => "HTTP(StacksBlockAccepted)",
                HttpResponseType::MicroblockHash(_, _) => "HTTP(MicroblockHash)",
                HttpResponseType::UnconfirmedTransaction(_, _) => "HTTP(UnconfirmedTransaction)",
                HttpResponseType::OptionsPreflight(_) => "HTTP(OptionsPreflight)",
                HttpResponseType::BadRequestJSON(..) | HttpResponseType::BadRequest(..) => {
                    "HTTP(400)"
                }
                HttpResponseType::Unauthorized(_, _) => "HTTP(401)",
                HttpResponseType::PaymentRequired(_, _) => "HTTP(402)",
                HttpResponseType::Forbidden(_, _) => "HTTP(403)",
                HttpResponseType::NotFound(_, _) => "HTTP(404)",
                HttpResponseType::ServerError(_, _) => "HTTP(500)",
                HttpResponseType::ServiceUnavailable(_, _) => "HTTP(503)",
                HttpResponseType::Error(_, _, _) => "HTTP(other)",
            },
        }
    }
}

/// A partially-decoded, streamed HTTP message (response) being received.
/// Internally used by StacksHttp to keep track of chunk-decoding state.
#[derive(Debug, Clone, PartialEq)]
struct HttpRecvStream {
    state: HttpChunkedTransferReaderState,
    data: Vec<u8>,
    total_consumed: usize, // number of *encoded* bytes consumed
}

impl HttpRecvStream {
    pub fn new(max_size: u64) -> HttpRecvStream {
        HttpRecvStream {
            state: HttpChunkedTransferReaderState::new(max_size),
            data: vec![],
            total_consumed: 0,
        }
    }

    /// Feed data into our chunked transfer reader state.  If we finish reading a stream, return
    /// the decoded bytes (as Some(Vec<u8>) and the total number of encoded bytes consumed).
    /// Always returns the number of bytes consumed.
    pub fn consume_data<R: Read>(
        &mut self,
        fd: &mut R,
    ) -> Result<(Option<(Vec<u8>, usize)>, usize), net_error> {
        let mut consumed = 0;
        let mut blocked = false;
        while !blocked {
            let mut decoded_buf = vec![0u8; 8192];
            let (read_pass, consumed_pass) = match self.state.do_read(fd, &mut decoded_buf) {
                Ok((0, num_consumed)) => {
                    trace!(
                        "consume_data blocked on 0 decoded bytes ({} consumed)",
                        num_consumed
                    );
                    blocked = true;
                    (0, num_consumed)
                }
                Ok((num_read, num_consumed)) => (num_read, num_consumed),
                Err(e) => match e.kind() {
                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => {
                        trace!("consume_data blocked on read error");
                        blocked = true;
                        (0, 0)
                    }
                    _ => {
                        return Err(net_error::ReadError(e));
                    }
                },
            };

            consumed += consumed_pass;
            if read_pass > 0 {
                self.data.extend_from_slice(&decoded_buf[0..read_pass]);
            }
        }

        self.total_consumed += consumed;

        // did we get a message?
        if self.state.is_eof() {
            // reset
            let message_data = mem::replace(&mut self.data, vec![]);
            let total_consumed = self.total_consumed;

            self.state = HttpChunkedTransferReaderState::new(self.state.max_size);
            self.total_consumed = 0;

            Ok((Some((message_data, total_consumed)), consumed))
        } else {
            Ok((None, consumed))
        }
    }
}

/// Information about an in-flight request
#[derive(Debug, Clone, PartialEq)]
struct HttpReplyData {
    request_id: u32,
    stream: HttpRecvStream,
}

/// Stacks HTTP implementation, for bufferring up data.
/// One of these exists per Connection<P: Protocol>.
/// There can be at most one HTTP request in-flight (i.e. we don't do pipelining)
#[derive(Debug, Clone, PartialEq)]
pub struct StacksHttp {
    /// Address of peer
    peer_addr: SocketAddr,
    /// Version of client
    request_version: Option<HttpVersion>,
    /// Path we requested
    request_path: Option<String>,
    /// Incoming reply
    reply: Option<HttpReplyData>,
    /// Size of HTTP chunks to write
    chunk_size: usize,
    /// Maximum size of call arguments
    pub maximum_call_argument_size: u32,
}

impl StacksHttp {
    pub fn new(peer_addr: SocketAddr) -> StacksHttp {
        StacksHttp {
            peer_addr,
            reply: None,
            request_version: None,
            request_path: None,
            chunk_size: 8192,
            maximum_call_argument_size: 20 * BOUND_VALUE_SERIALIZATION_HEX,
        }
    }

    pub fn set_chunk_size(&mut self, size: usize) -> () {
        self.chunk_size = size;
    }

    pub fn num_pending(&self) -> usize {
        if self.reply.is_some() {
            1
        } else {
            0
        }
    }

    pub fn has_pending_reply(&self) -> bool {
        self.reply.is_some()
    }

    pub fn set_pending(&mut self, preamble: &HttpResponsePreamble) -> bool {
        if self.reply.is_some() {
            // already pending
            return false;
        }
        self.reply = Some(HttpReplyData {
            request_id: preamble.request_id,
            stream: HttpRecvStream::new(MAX_MESSAGE_LEN as u64),
        });
        true
    }

    pub fn begin_request(&mut self, client_version: HttpVersion, request_path: String) -> () {
        self.request_version = Some(client_version);
        self.request_path = Some(request_path);
    }

    pub fn reset(&mut self) -> () {
        self.request_version = None;
        self.request_path = None;
        self.reply = None;
    }

    /// Used for processing chunk-encoded streams.
    /// Given the preamble and a Read, stream the bytes into a chunk-decoder.  Return the decoded
    /// bytes if we decode an entire stream.  Always return the number of bytes consumed.
    /// Returns Ok((Some(request path, decoded bytes we got, total number of encoded bytes), number of bytes gotten in this call))
    pub fn consume_data<R: Read>(
        &mut self,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
    ) -> Result<(Option<(HttpVersion, String, Vec<u8>, usize)>, usize), net_error> {
        assert!(preamble.is_chunked());
        assert!(self.reply.is_some());
        assert!(self.request_path.is_some());
        assert!(self.request_version.is_some());

        let mut finished = false;
        let res = match self.reply {
            Some(ref mut reply) => {
                assert_eq!(reply.request_id, preamble.request_id);
                match reply.stream.consume_data(fd) {
                    Ok(res) => {
                        match res {
                            (None, sz) => Ok((None, sz)),
                            (Some((byte_vec, bytes_total)), sz) => {
                                // done receiving
                                finished = true;
                                Ok((
                                    Some((
                                        self.request_version.clone().unwrap(),
                                        self.request_path.clone().unwrap(),
                                        byte_vec,
                                        bytes_total,
                                    )),
                                    sz,
                                ))
                            }
                        }
                    }
                    Err(e) => {
                        // broken stream
                        finished = true;
                        Err(e)
                    }
                }
            }
            None => {
                unreachable!();
            }
        };

        if finished {
            // if we fetch the whole message, or encounter an error, then we're done -- we can free
            // up this stream.
            self.reset();
        }
        res
    }

    /// Given a HTTP request, serialize it out
    #[cfg(test)]
    pub fn serialize_request(req: &HttpRequestType) -> Result<Vec<u8>, net_error> {
        let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());
        let mut ret = vec![];
        req.send(&mut http, &mut ret)?;
        Ok(ret)
    }

    /// Given a fully-formed single HTTP response, parse it (used by clients).
    #[cfg(test)]
    pub fn parse_response(
        request_path: &str,
        response_buf: &[u8],
    ) -> Result<StacksHttpMessage, net_error> {
        let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());
        http.reset();
        http.begin_request(HttpVersion::Http11, request_path.to_string());

        let (preamble, message_offset) = http.read_preamble(response_buf)?;
        let is_chunked = match preamble {
            StacksHttpPreamble::Response(ref resp) => resp.is_chunked(),
            _ => {
                return Err(net_error::DeserializeError(
                    "Invalid HTTP message: did not get a Response preamble".to_string(),
                ));
            }
        };

        let mut message_bytes = &response_buf[message_offset..];

        if is_chunked {
            match http.stream_payload(&preamble, &mut message_bytes) {
                Ok((Some((message, _)), _)) => Ok(message),
                Ok((None, _)) => Err(net_error::UnderflowError(
                    "Not enough bytes to form a streamed HTTP response".to_string(),
                )),
                Err(e) => Err(e),
            }
        } else {
            let (message, _) = http.read_payload(&preamble, &mut message_bytes)?;
            Ok(message)
        }
    }
}

impl ProtocolFamily for StacksHttp {
    type Preamble = StacksHttpPreamble;
    type Message = StacksHttpMessage;

    /// how big can a preamble get?
    fn preamble_size_hint(&mut self) -> usize {
        HTTP_PREAMBLE_MAX_ENCODED_SIZE as usize
    }

    /// how big is this message?  Might not know if we're dealing with chunked encoding.
    fn payload_len(&mut self, preamble: &StacksHttpPreamble) -> Option<usize> {
        match *preamble {
            StacksHttpPreamble::Request(ref http_request_preamble) => {
                Some(http_request_preamble.get_content_length() as usize)
            }
            StacksHttpPreamble::Response(ref http_response_preamble) => {
                match http_response_preamble.content_length {
                    Some(len) => Some(len as usize),
                    None => None,
                }
            }
        }
    }

    /// StacksHttpMessage deals with HttpRequestPreambles and HttpResponsePreambles
    fn read_preamble(&mut self, buf: &[u8]) -> Result<(StacksHttpPreamble, usize), net_error> {
        let mut cursor = io::Cursor::new(buf);

        let preamble = {
            let mut rd = BoundReader::from_reader(&mut cursor, 4096);
            let preamble: StacksHttpPreamble = read_next(&mut rd)?;
            preamble
        };

        let preamble_len = cursor.position() as usize;

        // if we already have a pending message, then this preamble cannot be processed (indicates an un-compliant client)
        match preamble {
            StacksHttpPreamble::Response(ref http_response_preamble) => {
                // request path must have been set
                if self.request_path.is_none() {
                    return Err(net_error::DeserializeError(
                        "Possible bug: did not set the request path".to_string(),
                    ));
                }

                if http_response_preamble.is_chunked() {
                    // will stream this.  Make sure we're not doing so already (no collisions
                    // allowed on in-flight request IDs!)
                    if self.has_pending_reply() {
                        test_debug!("Have pending reply already");
                        return Err(net_error::InProgress);
                    }

                    // mark as pending -- we can stream this
                    if !self.set_pending(http_response_preamble) {
                        test_debug!("Have pending reply already");
                        return Err(net_error::InProgress);
                    }
                }
            }
            _ => {}
        }

        Ok((preamble, preamble_len))
    }

    /// Stream a payload of unknown length.  Only gets called if payload_len() returns None.
    /// Returns the message if we get enough data to form one.
    /// Always returns the number of bytes consumed.
    fn stream_payload<R: Read>(
        &mut self,
        preamble: &StacksHttpPreamble,
        fd: &mut R,
    ) -> Result<(Option<(StacksHttpMessage, usize)>, usize), net_error> {
        assert!(self.payload_len(preamble).is_none());
        match preamble {
            StacksHttpPreamble::Request(_) => {
                // HTTP requests can't be chunk-encoded, so this should never be reached
                unreachable!()
            }
            StacksHttpPreamble::Response(ref http_response_preamble) => {
                assert!(http_response_preamble.is_chunked());
                assert!(self.request_path.is_some());

                // message of unknown length.  Buffer up and maybe we can parse it.
                let (message_bytes_opt, num_read) =
                    self.consume_data(http_response_preamble, fd).map_err(|e| {
                        self.reset();
                        e
                    })?;

                match message_bytes_opt {
                    Some((request_version, request_path, message_bytes, total_bytes_consumed)) => {
                        // can parse!
                        test_debug!(
                            "read http response payload of {} bytes (just buffered {}) for {}",
                            message_bytes.len(),
                            num_read,
                            &request_path
                        );

                        // we now know the content-length, so pass it into the parser.
                        let len_hint = message_bytes.len();
                        let parse_res = HttpResponseType::parse(
                            self,
                            request_version,
                            http_response_preamble,
                            request_path,
                            &mut &message_bytes[..],
                            Some(len_hint),
                        );

                        // done parsing
                        self.reset();
                        match parse_res {
                            Ok(data_response) => Ok((
                                Some((
                                    StacksHttpMessage::Response(data_response),
                                    total_bytes_consumed,
                                )),
                                num_read,
                            )),
                            Err(e) => {
                                info!("Failed to parse HTTP response: {:?}", &e);
                                Err(e)
                            }
                        }
                    }
                    None => {
                        // need more data
                        trace!(
                            "did not read http response payload, but buffered {}",
                            num_read
                        );
                        Ok((None, num_read))
                    }
                }
            }
        }
    }

    /// Parse a payload of known length.
    /// Only gets called if payload_len() returns Some(...)
    fn read_payload(
        &mut self,
        preamble: &StacksHttpPreamble,
        buf: &[u8],
    ) -> Result<(StacksHttpMessage, usize), net_error> {
        match preamble {
            StacksHttpPreamble::Request(ref http_request_preamble) => {
                // all requests have a known length
                let len = http_request_preamble.get_content_length() as usize;
                assert!(len <= buf.len(), "{} > {}", len, buf.len());

                trace!("read http request payload of {} bytes", len);

                let mut cursor = io::Cursor::new(buf);
                match HttpRequestType::parse(self, http_request_preamble, &mut cursor) {
                    Ok(data_request) => Ok((
                        StacksHttpMessage::Request(data_request),
                        cursor.position() as usize,
                    )),
                    Err(e) => {
                        info!("Failed to parse HTTP request: {:?}", &e);
                        if let net_error::ClientError(client_err) = e {
                            let req = HttpRequestType::ClientError(
                                HttpRequestMetadata::from_preamble(http_request_preamble),
                                client_err,
                            );
                            // consume any remaining HTTP request content by returning bytes read = len
                            Ok((StacksHttpMessage::Request(req), len))
                        } else {
                            Err(e)
                        }
                    }
                }
            }
            StacksHttpPreamble::Response(ref http_response_preamble) => {
                assert!(!http_response_preamble.is_chunked());
                assert!(self.request_path.is_some());
                assert!(self.request_version.is_some());

                let request_path = self.request_path.take().unwrap();
                let request_version = self.request_version.take().unwrap();

                // message of known length
                test_debug!(
                    "read http response payload of {} bytes for {}",
                    buf.len(),
                    &request_path
                );

                let mut cursor = io::Cursor::new(buf);
                match HttpResponseType::parse(
                    self,
                    request_version,
                    http_response_preamble,
                    request_path,
                    &mut cursor,
                    None,
                ) {
                    Ok(data_response) => Ok((
                        StacksHttpMessage::Response(data_response),
                        cursor.position() as usize,
                    )),
                    Err(e) => Err(e),
                }
            }
        }
    }

    fn verify_payload_bytes(
        &mut self,
        _key: &StacksPublicKey,
        _preamble: &StacksHttpPreamble,
        _bytes: &[u8],
    ) -> Result<(), net_error> {
        // not defined for HTTP messages, but maybe we could add a signature header at some point
        // in the future if needed.
        Ok(())
    }

    fn write_message<W: Write>(
        &mut self,
        fd: &mut W,
        message: &StacksHttpMessage,
    ) -> Result<(), net_error> {
        match *message {
            StacksHttpMessage::Request(ref req) => {
                if self.request_path.is_some() {
                    test_debug!("Have pending request already");
                    return Err(net_error::InProgress);
                }
                req.send(self, fd)?;

                self.reset();
                self.begin_request(req.metadata().version, req.request_path());
                Ok(())
            }
            StacksHttpMessage::Response(ref resp) => resp.send(self, fd),
        }
    }
}

#[cfg(test)]
mod test {
    use std::error::Error;

    use rand;
    use rand::RngCore;

    use burnchains::Txid;
    use chainstate::stacks::db::blocks::test::make_sample_microblock_stream;
    use chainstate::stacks::test::make_codec_test_block;
    use chainstate::stacks::StacksBlock;
    use chainstate::stacks::StacksMicroblock;
    use chainstate::stacks::StacksPrivateKey;
    use chainstate::stacks::StacksTransaction;
    use chainstate::stacks::TokenTransferMemo;
    use chainstate::stacks::TransactionAuth;
    use chainstate::stacks::TransactionPayload;
    use chainstate::stacks::TransactionPostConditionMode;
    use chainstate::stacks::TransactionVersion;
    use net::codec::test::check_codec_and_corruption;
    use net::test::*;
    use net::RPCNeighbor;
    use net::RPCNeighborsInfo;
    use util::hash::to_hex;
    use util::hash::Hash160;
    use util::hash::MerkleTree;
    use util::hash::Sha512Trunc256Sum;

    use crate::types::chainstate::StacksAddress;
    use crate::types::chainstate::StacksBlockHeader;

    use super::*;

    /// Simulate reading variable-length segments
    struct SegmentReader {
        segments: Vec<Vec<u8>>,
        i: usize, // which segment
        j: usize, // which offset in segment
    }

    impl SegmentReader {
        pub fn new(segments: Vec<Vec<u8>>) -> SegmentReader {
            SegmentReader {
                segments: segments,
                i: 0,
                j: 0,
            }
        }
    }

    impl Read for SegmentReader {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            if self.i >= self.segments.len() {
                return Ok(0);
            }
            let mut written = 0;
            while written < buf.len() {
                let to_copy = if self.segments[self.i][self.j..].len() < buf[written..].len() {
                    self.segments[self.i][self.j..].len()
                } else {
                    buf[written..].len()
                };

                buf[written..(written + to_copy)]
                    .copy_from_slice(&self.segments[self.i][self.j..(self.j + to_copy)]);

                self.j += to_copy;
                written += to_copy;

                if self.j >= self.segments[self.i].len() {
                    self.i += 1;
                    self.j = 0;
                }
            }
            Ok(written)
        }
    }

    fn vec_u8(mut v: Vec<&str>) -> Vec<Vec<u8>> {
        let mut ret = vec![];
        for s_vec in v.drain(..) {
            let v_u8 = s_vec.as_bytes().to_vec();
            ret.push(v_u8);
        }
        ret
    }

    #[test]
    fn test_segment_reader() {
        let mut tests = vec![
            (vec_u8(vec!["a", "b"]), "ab"),
            (vec_u8(vec!["aa", "bbb", "cccc"]), "aabbbcccc"),
            (vec_u8(vec!["aaaa", "bbb", "cc", "d", ""]), "aaaabbbccd"),
            (vec_u8(vec!["", "a", "", "b", ""]), "ab"),
            (vec_u8(vec![""]), ""),
        ];
        for (input_vec, expected) in tests.drain(..) {
            let num_segments = input_vec.len();
            let mut segment_io = SegmentReader::new(input_vec);
            let mut output = vec![0u8; expected.len()];
            let mut offset = 0;
            for i in 0..num_segments {
                let nw = segment_io.read(&mut output[offset..]).unwrap();
                offset += nw;
            }
            assert_eq!(output, expected.as_bytes().to_vec());
        }
    }

    #[test]
    fn test_http_chunked_encode() {
        let tests = vec![
            // (chunk size, byte string, expected encoding)
            (10, "aaaaaaaaaabbbbbbbbbbccccccccccdddddddddd", "a\r\naaaaaaaaaa\r\na\r\nbbbbbbbbbb\r\na\r\ncccccccccc\r\na\r\ndddddddddd\r\n0\r\n\r\n"),
            (10, "aaaaaaaaaabbbbbbbbbbccccccccccdddddddddde", "a\r\naaaaaaaaaa\r\na\r\nbbbbbbbbbb\r\na\r\ncccccccccc\r\na\r\ndddddddddd\r\n1\r\ne\r\n0\r\n\r\n"),
            (10, "aaaaaaaaaabbbbbbbbbbccccccccccddddddddddeeeee", "a\r\naaaaaaaaaa\r\na\r\nbbbbbbbbbb\r\na\r\ncccccccccc\r\na\r\ndddddddddd\r\n5\r\neeeee\r\n0\r\n\r\n"),
            (1, "abcd", "1\r\na\r\n1\r\nb\r\n1\r\nc\r\n1\r\nd\r\n0\r\n\r\n"),
            (3, "abcd", "3\r\nabc\r\n1\r\nd\r\n0\r\n\r\n"),
            (10, "", "0\r\n\r\n")
        ];
        for (chunk_size, input_bytes, encoding) in tests.iter() {
            let mut bytes = vec![];
            {
                let mut write_state = HttpChunkedTransferWriterState::new(*chunk_size as usize);
                let mut encoder =
                    HttpChunkedTransferWriter::from_writer_state(&mut bytes, &mut write_state);
                encoder.write_all(input_bytes.as_bytes()).unwrap();
                encoder.flush().unwrap();
            }

            assert_eq!(bytes, encoding.as_bytes().to_vec());
        }
    }

    #[test]
    fn test_http_chunked_encode_multi() {
        let tests = vec![
            // chunk size, sequence of writes, expected encoding
            (10, vec!["aaaaaaaaaa", "bbbbb", "bbbbb", "ccc", "ccc", "ccc", "c", "dd", "ddddd", "ddd"], "a\r\naaaaaaaaaa\r\na\r\nbbbbbbbbbb\r\na\r\ncccccccccc\r\na\r\ndddddddddd\r\n0\r\n\r\n"),
            (10, vec!["a", "a", "a", "a", "a", "a", "a", "a", "a", "a"], "a\r\naaaaaaaaaa\r\n0\r\n\r\n"),
            (10, vec!["a", "", "a", "", "a", "", "a", "", "a", "", "a", "", "a", "", "a", "", "a", "", "a", ""], "a\r\naaaaaaaaaa\r\n0\r\n\r\n"),
        ];

        for (chunk_size, input_vec, encoding) in tests.iter() {
            let mut bytes = vec![];
            {
                let mut write_state = HttpChunkedTransferWriterState::new(*chunk_size as usize);
                let mut encoder =
                    HttpChunkedTransferWriter::from_writer_state(&mut bytes, &mut write_state);
                for input in input_vec.iter() {
                    encoder.write_all(input.as_bytes()).unwrap();
                }
                encoder.flush().unwrap();
            }

            assert_eq!(bytes, encoding.as_bytes().to_vec());
        }
    }

    #[test]
    fn test_http_chunked_decode() {
        let tests = vec![
            ("a\r\naaaaaaaaaa\r\na\r\nbbbbbbbbbb\r\na\r\ncccccccccc\r\na\r\ndddddddddd\r\n0\r\n\r\n", "aaaaaaaaaabbbbbbbbbbccccccccccdddddddddd"),
            ("A\r\naaaaaaaaaa\r\nA\r\nbbbbbbbbbb\r\nA\r\ncccccccccc\r\nA\r\ndddddddddd\r\n0\r\n\r\n", "aaaaaaaaaabbbbbbbbbbccccccccccdddddddddd"),
            ("1\r\na\r\n2\r\nbb\r\n3\r\nccc\r\n4\r\ndddd\r\n0\r\n\r\n", "abbcccdddd"),
            ("1\r\na\r\n0\r\n\r\n", "a"),
            ("1\r\na\r\n0\r\n\r\n1\r\nb\r\n0\r\n\r\n", "a"),     // stop reading after the first 0-length chunk encountered
            ("1; a; b\r\na\r\n0; c\r\n\r\n", "a"),                          // ignore short extensions
            ("1  ; a ; b \r\na\r\n0     ; extension003\r\n\r\n", "a"),      // ignore short extensions
            ("1 \t; a\t;\tb ;\r\na\r\n0\t\t;c\r\n\r\n", "a"),               // ignore short extensions
        ];
        for (encoded, expected) in tests.iter() {
            let mut cursor = io::Cursor::new(encoded.as_bytes());
            let mut decoder = HttpChunkedTransferReader::from_reader(&mut cursor, 50);
            let mut output = vec![0u8; expected.len()];
            decoder.read_exact(&mut output).unwrap();

            assert_eq!(output, expected.as_bytes().to_vec());
        }
    }

    #[test]
    fn test_http_chunked_decode_multi() {
        let tests = vec![
            (vec_u8(vec!["1\r\na", "\r\n", "0\r\n\r\n"]), "a"),
            (vec_u8(vec!["1\r\na\r", "\n0\r\n\r\n"]), "a"),
            (vec_u8(vec!["1\r\na\r\n", "0\r\n\r", "\n"]), "a"),
            (vec_u8(vec!["1\r\na\r\n0\r\n", "\r\n"]), "a"),
            (vec_u8(vec!["1\r\na\r\n0\r", "\n\r\n"]), "a"),
            (vec_u8(vec!["1\r\na\r\n0\r", "\n", "\r\n"]), "a"),
            (vec_u8(vec!["1\r\na\r\n0\r", "\n\r", "\n"]), "a"),
            (vec_u8(vec!["1\r\na\r\n0\r", "\n", "\r", "\n"]), "a"),
            (
                vec_u8(vec![
                    "1", "\r", "\n", "a", "\r", "\n", "0", "\r", "\n", "\r", "\n",
                ]),
                "a",
            ),
            (
                vec_u8(vec![
                    "a\r",
                    "\n",
                    "aaaa",
                    "aaaaa",
                    "a",
                    "\r\n",
                    "a\r\n",
                    "bbbbbbbbbb\r",
                    "\na\r\nccc",
                    "ccccccc",
                    "\r",
                    "\na\r",
                    "\ndddddd",
                    "dddd",
                    "\r\n0\r",
                    "\n",
                    "\r",
                    "\n",
                ]),
                "aaaaaaaaaabbbbbbbbbbccccccccccdddddddddd",
            ),
            (
                vec_u8(vec![
                    "a\r\naaaaaaaaaa",
                    "\r",
                    "\n",
                    "a\r\nbbbbbbbbbb\r",
                    "\n",
                    "a\r\ncccccccccc\r",
                    "\na\r\nddddd",
                    "ddddd\r",
                    "\n0\r",
                    "\n\r",
                    "\n",
                ]),
                "aaaaaaaaaabbbbbbbbbbccccccccccdddddddddd",
            ),
            (
                vec_u8(vec![
                    "1",
                    "\r",
                    "\n",
                    "",
                    "a",
                    "\r",
                    "\n",
                    "2",
                    "\r\n",
                    "bb",
                    "\r\n",
                    "3\r\n",
                    "ccc\r",
                    "\n4\r\n",
                    "dddd\r\n",
                    "0\r\n\r\n",
                ]),
                "abbcccdddd",
            ),
        ];
        for (encoded_vec, expected) in tests.iter() {
            test_debug!("expect {:?}", &expected);

            let mut output = vec![];
            let mut cursor = SegmentReader::new((*encoded_vec).clone());
            let mut decoder = HttpChunkedTransferReader::from_reader(&mut cursor, 50);

            for encoded in encoded_vec.iter() {
                let mut tmp = vec![0u8; encoded.len()];
                let nr = decoder.read(&mut tmp).unwrap();

                output.extend_from_slice(&tmp[0..nr]);
            }

            assert_eq!(output, expected.as_bytes().to_vec());
        }
    }

    #[test]
    fn test_http_chunked_decode_err() {
        let tests = vec![
            (
                "1; reallyreallyreallyreallylongextension;\r\na\r\n0\r\n\r\n",
                1,
                "too long",
            ),
            ("ffffffff\r\n", 1, "too big"),
            ("nope\r\n", 1, "could not parse"),
            ("1\na\r\n0\r\n\r\n", 1, "could not parse"),
            ("a\r\naaaaaaaaaa", 11, "failed to fill whole buffer"),
            ("1\r\nab\r\n0\r\n\r\n", 2, "Invalid chunk trailer"),
            (
                "15\r\naaaaaaaaaabbbbbbbbbbb\r\n0\r\n\r\n",
                21,
                "HTTP body exceeds maximum expected length",
            ),
            (
                "7\r\naaaaaaa\r\n8\r\nbbbbbbbb\r\n6\r\ncccccc\r\n0\r\n\r\n",
                21,
                "HTTP body exceeds maximum expected length",
            ),
        ];
        for (encoded, expected_len, expected) in tests.iter() {
            test_debug!("expect '{}'", expected);
            let mut cursor = io::Cursor::new(encoded.as_bytes());
            let mut decoder = HttpChunkedTransferReader::from_reader(&mut cursor, 20);
            let mut output = vec![0u8; *expected_len as usize];

            let err = decoder.read_exact(&mut output).unwrap_err();
            let errstr = format!("{:?}", &err);

            assert!(
                errstr.find(expected).is_some(),
                "Expected '{}' in '{:?}'",
                expected,
                errstr
            );
        }
    }

    #[test]
    fn test_http_chunked_encode_decode_roundtrip() {
        let mut rng = rand::thread_rng();
        for i in 0..100 {
            let mut data = vec![0u8; 256];
            rng.fill_bytes(&mut data);

            let mut encoded_data = vec![];
            {
                let mut write_state = HttpChunkedTransferWriterState::new(i + 1);
                let mut encoder = HttpChunkedTransferWriter::from_writer_state(
                    &mut encoded_data,
                    &mut write_state,
                );
                encoder.write_all(&data).unwrap();
                encoder.flush().unwrap();
            }

            let mut decoded_data = vec![0u8; 256];
            {
                let mut cursor = io::Cursor::new(&encoded_data);
                let mut decoder = HttpChunkedTransferReader::from_reader(&mut cursor, 256);
                decoder.read_exact(&mut decoded_data).unwrap();
            }

            assert_eq!(data, decoded_data);
        }
    }

    #[test]
    fn test_parse_reserved_header() {
        let tests = vec![
            (
                "Content-Length",
                "123",
                Some(HttpReservedHeader::ContentLength(123)),
            ),
            (
                "Content-Type",
                "text/plain",
                Some(HttpReservedHeader::ContentType(HttpContentType::Text)),
            ),
            (
                "Content-Type",
                "application/octet-stream",
                Some(HttpReservedHeader::ContentType(HttpContentType::Bytes)),
            ),
            (
                "Content-Type",
                "application/json",
                Some(HttpReservedHeader::ContentType(HttpContentType::JSON)),
            ),
            (
                "X-Request-Id",
                "123",
                Some(HttpReservedHeader::XRequestID(123)),
            ),
            (
                "Host",
                "foo:123",
                Some(HttpReservedHeader::Host(PeerHost::DNS(
                    "foo".to_string(),
                    123,
                ))),
            ),
            (
                "Host",
                "1.2.3.4:123",
                Some(HttpReservedHeader::Host(PeerHost::IP(
                    PeerAddress([
                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
                        0x01, 0x02, 0x03, 0x04,
                    ]),
                    123,
                ))),
            ),
            // errors
            ("Content-Length", "-1", None),
            ("Content-Length", "asdf", None),
            ("Content-Length", "4294967296", None),
            ("Content-Type", "blargh", None),
            ("X-Request-Id", "-1", None),
            ("X-Request-Id", "asdf", None),
            ("X-Request-Id", "4294967296", None),
            ("Unrecognized", "header", None),
        ];

        for (key, value, expected_result) in tests {
            let result = HttpReservedHeader::try_from_str(key, value);
            assert_eq!(result, expected_result);
        }
    }

    #[test]
    fn test_parse_http_request_preamble_ok() {
        let tests = vec![
            ("GET /foo HTTP/1.1\r\nHost: localhost:6270\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "GET".to_string(), "/foo".to_string(), "localhost".to_string(), 6270, true, vec![], vec![])),
            ("POST asdf HTTP/1.1\r\nHost: core.blockstack.org\r\nFoo: Bar\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "POST".to_string(), "asdf".to_string(), "core.blockstack.org".to_string(), 80, true, vec!["foo".to_string()], vec!["Bar".to_string()])),
            ("POST asdf HTTP/1.1\r\nHost: core.blockstack.org\r\nFoo: Bar\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "POST".to_string(), "asdf".to_string(), "core.blockstack.org".to_string(), 80, true, vec!["foo".to_string()], vec!["Bar".to_string()])),
            ("GET /foo HTTP/1.1\r\nConnection: close\r\nHost: localhost:6270\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "GET".to_string(), "/foo".to_string(), "localhost".to_string(), 6270, false, vec![], vec![])),
            ("POST asdf HTTP/1.1\r\nHost: core.blockstack.org\r\nConnection: close\r\nFoo: Bar\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "POST".to_string(), "asdf".to_string(), "core.blockstack.org".to_string(), 80, false, vec!["foo".to_string()], vec!["Bar".to_string()])),
            ("POST asdf HTTP/1.1\r\nHost: core.blockstack.org\r\nFoo: Bar\r\nConnection: close\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "POST".to_string(), "asdf".to_string(), "core.blockstack.org".to_string(), 80, false, vec!["foo".to_string()], vec!["Bar".to_string()])) 
        ];

        for (data, request) in tests.iter() {
            let req = HttpRequestPreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(req.is_ok(), "{:?}", &req);
            assert_eq!(req.unwrap(), *request);

            let sreq = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(sreq.is_ok(), "{:?}", &sreq);
            assert_eq!(
                sreq.unwrap(),
                StacksHttpPreamble::Request((*request).clone())
            );
        }
    }

    #[test]
    fn test_parse_http_request_options() {
        let data = "OPTIONS /foo HTTP/1.1\r\nHost: localhost:6270\r\n\r\n";
        let req = HttpRequestPreamble::consensus_deserialize(&mut data.as_bytes());
        let preamble = HttpRequestPreamble::from_headers(
            HttpVersion::Http11,
            "OPTIONS".to_string(),
            "/foo".to_string(),
            "localhost".to_string(),
            6270,
            true,
            vec![],
            vec![],
        );
        assert_eq!(req.unwrap(), preamble);
    }

    #[test]
    fn test_parse_http_request_preamble_case_ok() {
        let tests = vec![
            ("GET /foo HTTP/1.1\r\nhOsT: localhost:6270\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "GET".to_string(), "/foo".to_string(), "localhost".to_string(), 6270, true, vec![], vec![])),
            ("GET /foo HTTP/1.1\r\ncOnNeCtIoN: cLoSe\r\nhOsT: localhost:6270\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "GET".to_string(), "/foo".to_string(), "localhost".to_string(), 6270, false, vec![], vec![])),
            ("POST asdf HTTP/1.1\r\nhOsT: core.blockstack.org\r\nCOnNeCtIoN: kEeP-aLiVE\r\nFoo: Bar\r\n\r\n",
             HttpRequestPreamble::from_headers(HttpVersion::Http11, "POST".to_string(), "asdf".to_string(), "core.blockstack.org".to_string(), 80, true, vec!["foo".to_string()], vec!["Bar".to_string()])),
        ];

        for (data, request) in tests.iter() {
            let req = HttpRequestPreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(req.is_ok(), "{:?}", &req);
            assert_eq!(req.unwrap(), *request);

            let sreq = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(sreq.is_ok(), "{:?}", &sreq);
            assert_eq!(
                sreq.unwrap(),
                StacksHttpPreamble::Request((*request).clone())
            );
        }
    }

    #[test]
    fn test_parse_http_request_preamble_err() {
        let tests = vec![
            ("GET /foo HTTP/1.1\r\n", "failed to fill whole buffer"),
            ("GET /foo HTTP/1.1\r\n\r\n", "Missing Host header"),
            (
                "GET /foo HTTP/1.1\r\nFoo: Bar\r\n\r\n",
                "Missing Host header",
            ),
            ("GET /foo HTTP/\r\n\r\n", "Failed to parse HTTP request"),
            ("GET /foo HTTP/1.1\r\nHost:", "failed to fill whole buffer"),
            (
                "GET /foo HTTP/1.1\r\nHost: foo:80\r\nHost: bar:80\r\n\r\n",
                "duplicate header",
            ),
            (
                "GET /foo HTTP/1.1\r\nHost: localhost:6270\r\nfoo: \u{2764}\r\n\r\n",
                "header value is not ASCII-US",
            ),
            (
                "Get /foo HTTP/1.1\r\nHost: localhost:666666\r\n\r\n",
                "Missing Host header",
            ),
            (
                "GET /foo HTTP/1.1\r\nHost: localhost:8080\r\nConnection: foo\r\n\r\n",
                "invalid Connection: header",
            ),
        ];

        for (data, errstr) in tests.iter() {
            let res = HttpRequestPreamble::consensus_deserialize(&mut data.as_bytes());
            test_debug!("Expect '{}'", errstr);
            assert!(res.is_err(), "{:?}", &res);
            assert!(
                res.as_ref().unwrap_err().to_string().find(errstr).is_some(),
                "{:?}",
                &res
            );
        }
    }

    #[test]
    fn test_parse_stacks_http_preamble_request_err() {
        let tests = vec![
            (
                "GET /foo HTTP/1.1\r\n",
                "Not enough bytes to form a HTTP request or response",
            ),
            (
                "GET /foo HTTP/1.1\r\n\r\n",
                "Failed to decode HTTP request or HTTP response",
            ),
            (
                "GET /foo HTTP/1.1\r\nFoo: Bar\r\n\r\n",
                "Failed to decode HTTP request or HTTP response",
            ),
            (
                "GET /foo HTTP/\r\n\r\n",
                "Failed to decode HTTP request or HTTP response",
            ),
            (
                "GET /foo HTTP/1.1\r\nHost:",
                "Not enough bytes to form a HTTP request or response",
            ),
            (
                "GET /foo HTTP/1.1\r\nHost: foo:80\r\nHost: bar:80\r\n\r\n",
                "Failed to decode HTTP request or HTTP response",
            ),
            (
                "GET /foo HTTP/1.1\r\nHost: localhost:6270\r\nfoo: \u{2764}\r\n\r\n",
                "Failed to decode HTTP request or HTTP response",
            ),
            (
                "Get /foo HTTP/1.1\r\nHost: localhost:666666\r\n\r\n",
                "Failed to decode HTTP request or HTTP response",
            ),
            (
                "GET /foo HTTP/1.1\r\nHost: localhost:8080\r\nConnection: foo\r\n\r\n",
                "Failed to decode HTTP request or HTTP response",
            ),
        ];

        for (data, errstr) in tests.iter() {
            let sres = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
            test_debug!("Expect '{}'", errstr);
            assert!(sres.is_err(), "{:?}", &sres);
            assert!(
                sres.as_ref()
                    .unwrap_err()
                    .to_string()
                    .find(errstr)
                    .is_some(),
                "{:?}",
                &sres
            );
        }
    }

    #[test]
    fn test_http_request_preamble_headers() {
        let mut req = HttpRequestPreamble::new(
            HttpVersion::Http11,
            "GET".to_string(),
            "/foo".to_string(),
            "localhost".to_string(),
            6270,
            true,
        );
        let req_11 = HttpRequestPreamble::new(
            HttpVersion::Http11,
            "GET".to_string(),
            "/foo".to_string(),
            "localhost".to_string(),
            6270,
            false,
        );
        let req_10 = HttpRequestPreamble::new(
            HttpVersion::Http10,
            "GET".to_string(),
            "/foo".to_string(),
            "localhost".to_string(),
            6270,
            false,
        );

        req.add_header("foo".to_string(), "bar".to_string());

        assert_eq!(req.content_type, None);
        req.set_content_type(HttpContentType::JSON);
        assert_eq!(req.content_type, Some(HttpContentType::JSON));

        req.add_header(
            "content-type".to_string(),
            "application/octet-stream".to_string(),
        );
        assert_eq!(req.content_type, Some(HttpContentType::Bytes));

        let mut bytes = vec![];
        req.consensus_serialize(&mut bytes).unwrap();
        let txt = String::from_utf8(bytes).unwrap();

        test_debug!("headers:\n{}", txt);

        assert!(txt.find("HTTP/1.1").is_some(), "HTTP version is missing");
        assert!(
            txt.find("User-Agent: stacks/2.0\r\n").is_some(),
            "User-Agnet header is missing"
        );
        assert!(
            txt.find("Host: localhost:6270\r\n").is_some(),
            "Host header is missing"
        );
        assert!(txt.find("foo: bar\r\n").is_some(), "foo header is missing");
        assert!(
            txt.find("Content-Type: application/octet-stream\r\n")
                .is_some(),
            "content-type is missing"
        );
        assert!(txt.find("Connection: ").is_none()); // not sent if keep_alive is true (for HTTP/1.1)

        let mut bytes_10 = vec![];
        req_10.consensus_serialize(&mut bytes_10).unwrap();
        let txt_10 = String::from_utf8(bytes_10).unwrap();

        assert!(txt_10.find("HTTP/1.0").is_some(), "HTTP version is missing");

        let mut bytes_11 = vec![];
        req_11.consensus_serialize(&mut bytes_11).unwrap();
        let txt_11 = String::from_utf8(bytes_11).unwrap();

        assert!(txt_11.find("HTTP/1.1").is_some(), "HTTP version is wrong");
        assert!(
            txt_11.find("Connection: close").is_some(),
            "Explicit Connection: close is missing"
        );
    }

    #[test]
    fn test_parse_http_response_preamble_ok() {
        let tests = vec![
            ("HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: 123\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "OK".to_string(), true, Some(123), HttpContentType::Bytes, 0, vec![], vec![])),
            ("HTTP/1.1 400 Bad Request\r\nContent-Type: application/json\r\nContent-Length: 456\r\nFoo: Bar\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(400, "Bad Request".to_string(), true, Some(456), HttpContentType::JSON, 0, vec!["foo".to_string()], vec!["Bar".to_string()])),
            ("HTTP/1.1 400 Bad Request\r\nContent-Type: application/json\r\nContent-Length: 456\r\nX-Request-Id: 123\r\nFoo: Bar\r\n\r\n",
             HttpResponsePreamble::from_headers(400, "Bad Request".to_string(), true, Some(456), HttpContentType::JSON, 123, vec!["foo".to_string()], vec!["Bar".to_string()])),
            ("HTTP/1.1 200 Ok\r\nContent-Type: application/octet-stream\r\nTransfer-encoding: chunked\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "Ok".to_string(), true, None, HttpContentType::Bytes, 0, vec![], vec![])),
            ("HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: 123\r\nConnection: close\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "OK".to_string(), false, Some(123), HttpContentType::Bytes, 0, vec![], vec![])),
            ("HTTP/1.1 400 Bad Request\r\nContent-Type: application/json\r\nContent-Length: 456\r\nConnection: close\r\nFoo: Bar\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(400, "Bad Request".to_string(), false, Some(456), HttpContentType::JSON, 0, vec!["foo".to_string()], vec!["Bar".to_string()])),
            ("HTTP/1.1 400 Bad Request\r\nContent-Type: application/json\r\nConnection: close\r\nContent-Length: 456\r\nX-Request-Id: 123\r\nFoo: Bar\r\n\r\n",
             HttpResponsePreamble::from_headers(400, "Bad Request".to_string(), false, Some(456), HttpContentType::JSON, 123, vec!["foo".to_string()], vec!["Bar".to_string()])),
            ("HTTP/1.1 200 Ok\r\nConnection: close\r\nContent-Type: application/octet-stream\r\nTransfer-encoding: chunked\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "Ok".to_string(), false, None, HttpContentType::Bytes, 0, vec![], vec![])),
        ];

        for (data, response) in tests.iter() {
            test_debug!("Try parsing:\n{}\n", data);
            let res = HttpResponsePreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(res.is_ok(), "{:?}", &res);
            assert_eq!(res.unwrap(), *response);

            let sres = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(sres.is_ok(), "{:?}", &sres);
            assert_eq!(
                sres.unwrap(),
                StacksHttpPreamble::Response((*response).clone())
            );
        }
    }

    #[test]
    fn test_parse_http_response_case_ok() {
        let tests = vec![
            ("HTTP/1.1 200 OK\r\ncOnTeNt-TyPe: aPpLiCaTiOn/oCtEt-StReAm\r\ncOnTeNt-LeNgTh: 123\r\nx-ReQuEsT-iD: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "OK".to_string(), true, Some(123), HttpContentType::Bytes, 0, vec![], vec![])),
            ("HTTP/1.1 200 Ok\r\ncOnTeNt-tYpE: aPpLiCaTiOn/OcTeT-sTrEaM\r\ntRaNsFeR-eNcOdInG: cHuNkEd\r\nX-rEqUeSt-Id: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "Ok".to_string(), true, None, HttpContentType::Bytes, 0, vec![], vec![])),
            ("HTTP/1.1 200 Ok\r\ncOnNeCtIoN: cLoSe\r\nContent-Type: application/octet-stream\r\nTransfer-encoding: chunked\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "Ok".to_string(), false, None, HttpContentType::Bytes, 0, vec![], vec![])),
            ("HTTP/1.1 200 Ok\r\ncOnNeCtIoN: kEeP-AlIvE\r\nContent-Type: application/octet-stream\r\nTransfer-encoding: chunked\r\nX-Request-ID: 0\r\n\r\n",
             HttpResponsePreamble::from_headers(200, "Ok".to_string(), true, None, HttpContentType::Bytes, 0, vec![], vec![])),
        ];

        for (data, response) in tests.iter() {
            test_debug!("Try parsing:\n{}\n", data);
            let res = HttpResponsePreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(res.is_ok(), "{:?}", &res);
            assert_eq!(res.unwrap(), *response);

            let sres = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
            assert!(sres.is_ok(), "{:?}", &sres);
            assert_eq!(
                sres.unwrap(),
                StacksHttpPreamble::Response((*response).clone())
            );
        }
    }

    #[test]
    fn test_http_response_preamble_headers() {
        let mut res = HttpResponsePreamble::new(
            200,
            "OK".to_string(),
            Some(123),
            HttpContentType::JSON,
            true,
            123,
        );
        assert_eq!(res.request_id, 123);

        res.set_request_id(456);
        assert_eq!(res.request_id, 456);

        res.add_header("foo".to_string(), "bar".to_string());
        res.add_CORS_headers();

        let mut bytes = vec![];
        res.consensus_serialize(&mut bytes).unwrap();
        let txt = String::from_utf8(bytes).unwrap();
        assert!(
            txt.find("Server: stacks/2.0\r\n").is_some(),
            "Server header is missing"
        );
        assert!(
            txt.find("Content-Length: 123\r\n").is_some(),
            "Content-Length is missing"
        );
        assert!(
            txt.find("Content-Type: application/json\r\n").is_some(),
            "Content-Type is missing"
        );
        assert!(txt.find("Date: ").is_some(), "Date header is missing");
        assert!(txt.find("foo: bar\r\n").is_some(), "foo header is missing");
        assert!(
            txt.find("X-Request-Id: 456\r\n").is_some(),
            "X-Request-Id is missing"
        );
        assert!(
            txt.find("Access-Control-Allow-Origin: *\r\n").is_some(),
            "CORS header is missing"
        );
        assert!(
            txt.find("Access-Control-Allow-Headers: origin, content-type\r\n")
                .is_some(),
            "CORS header is missing"
        );
        assert!(
            txt.find("Access-Control-Allow-Methods: POST, GET, OPTIONS\r\n")
                .is_some(),
            "CORS header is missing"
        );
        assert!(txt.find("Connection: ").is_none()); // not sent if keep_alive is true
    }

    #[test]
    fn test_parse_http_response_preamble_err() {
        let tests = vec![
            ("HTTP/1.1 200",
            "failed to fill whole buffer"),
            ("HTTP/1.1 200 OK\r\nfoo: \u{2764}\r\n\r\n",
            "header value is not ASCII-US"),
            ("HTTP/1.1 200 OK\r\nfoo: bar\r\nfoo: bar\r\n\r\n",
             "duplicate header"),
            ("HTTP/1.1 200 OK\r\nContent-Type: image/png\r\n\r\n",
             "Unsupported HTTP content type"),
            ("HTTP/1.1 200 OK\r\nContent-Length: foo\r\n\r\n",
             "Invalid Content-Length"),
            ("HTTP/1.1 200 OK\r\nContent-Length: 123\r\n\r\n",
             "missing Content-Type, Content-Length"),
            ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\n",
             "missing Content-Type, Content-Length"),
            ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 123\r\nTransfer-Encoding: chunked\r\n\r\n",
             "incompatible transfer-encoding and content-length"),
            ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 123\r\nConnection: foo\r\n\r\n",
             "invalid Connection: header"),
        ];

        for (data, errstr) in tests.iter() {
            let res = HttpResponsePreamble::consensus_deserialize(&mut data.as_bytes());
            test_debug!("Expect '{}', got: {:?}", errstr, &res);
            assert!(res.is_err(), "{:?}", &res);
            assert!(res.unwrap_err().to_string().find(errstr).is_some());
        }
    }

    #[test]
    fn test_parse_stacks_http_preamble_response_err() {
        let tests = vec![
            ("HTTP/1.1 200",
            "Not enough bytes to form a HTTP request or response"),
            ("HTTP/1.1 200 OK\r\nfoo: \u{2764}\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
            ("HTTP/1.1 200 OK\r\nfoo: bar\r\nfoo: bar\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
            ("HTTP/1.1 200 OK\r\nContent-Type: image/png\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
            ("HTTP/1.1 200 OK\r\nContent-Length: foo\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
            ("HTTP/1.1 200 OK\r\nContent-Length: 123\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
            ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
            ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 123\r\nTransfer-Encoding: chunked\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
            ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 123\r\nConnection: foo\r\n\r\n",
             "Failed to decode HTTP request or HTTP response"),
        ];

        for (data, errstr) in tests.iter() {
            let sres = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
            test_debug!("Expect '{}', got: {:?}", errstr, &sres);
            assert!(sres.is_err(), "{:?}", &sres);
            assert!(
                sres.as_ref()
                    .unwrap_err()
                    .to_string()
                    .find(errstr)
                    .is_some(),
                "{:?}",
                &sres
            );
        }
    }

    fn make_test_transaction() -> StacksTransaction {
        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
        let addr = auth.origin().address_testnet();
        let recv_addr = StacksAddress {
            version: 1,
            bytes: Hash160([0xff; 20]),
        };

        let mut tx_stx_transfer = StacksTransaction::new(
            TransactionVersion::Testnet,
            auth.clone(),
            TransactionPayload::TokenTransfer(
                recv_addr.clone().into(),
                123,
                TokenTransferMemo([0u8; 34]),
            ),
        );
        tx_stx_transfer.chain_id = 0x80000000;
        tx_stx_transfer.post_condition_mode = TransactionPostConditionMode::Allow;
        tx_stx_transfer.set_tx_fee(0);
        tx_stx_transfer
    }

    #[test]
    fn test_http_parse_host_header_value() {
        let hosts = vec![
            "1.2.3.4",
            "1.2.3.4:5678",
            "[1:203:405:607:809:a0b:c0d:e0f]",
            "[1:203:405:607:809:a0b:c0d:e0f]:12345",
            "www.foo.com",
            "www.foo.com:12345",
            // invalid IP addresses will be parsed to DNS names
            "1.2.3.4.5",
            "[1:203:405:607:809:a0b:c0d:e0f:1011]",
            // these won't parse at all, since the port is invalid
            "1.2.3.4:1234567",
            "1.2.3.4.5:1234567",
            "[1:203:405:607:809:a0b:c0d:e0f]:1234567",
            "[1:203:405:607:809:a0b:c0d:e0f:1011]:1234567",
            "www.foo.com:1234567",
            ":",
            ":123",
        ];

        let peerhosts = vec![
            Some(PeerHost::IP(
                PeerAddress([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 1, 2, 3, 4]),
                80,
            )),
            Some(PeerHost::IP(
                PeerAddress([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 1, 2, 3, 4]),
                5678,
            )),
            Some(PeerHost::IP(
                PeerAddress([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
                80,
            )),
            Some(PeerHost::IP(
                PeerAddress([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
                12345,
            )),
            Some(PeerHost::DNS("www.foo.com".to_string(), 80)),
            Some(PeerHost::DNS("www.foo.com".to_string(), 12345)),
            Some(PeerHost::DNS("1.2.3.4.5".to_string(), 80)),
            Some(PeerHost::DNS(
                "[1:203:405:607:809:a0b:c0d:e0f:1011]".to_string(),
                80,
            )),
            None,
            None,
            None,
            None,
            None,
            None,
            None,
        ];

        for (host, expected_host) in hosts.iter().zip(peerhosts.iter()) {
            let peerhost = match host.parse::<PeerHost>() {
                Ok(ph) => Some(ph),
                Err(_) => None,
            };

            match (peerhost, expected_host) {
                (Some(ref ph), Some(ref expected_ph)) => assert_eq!(*ph, *expected_ph),
                (None, None) => {}
                (Some(ph), None) => {
                    eprintln!(
                        "Parsed {} successfully to {:?}, but expected error",
                        host, ph
                    );
                    assert!(false);
                }
                (None, Some(expected_ph)) => {
                    eprintln!("Failed to parse {} successfully", host);
                    assert!(false);
                }
            }
        }
    }

    #[test]
    fn test_http_request_type_codec() {
        let http_request_metadata_ip = HttpRequestMetadata {
            version: HttpVersion::Http11,
            peer: PeerHost::IP(
                PeerAddress([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
                12345,
            ),
            keep_alive: true,
        };
        let http_request_metadata_dns = HttpRequestMetadata {
            version: HttpVersion::Http11,
            peer: PeerHost::DNS("www.foo.com".to_string(), 80),
            keep_alive: true,
        };

        let tests = vec![
            HttpRequestType::GetNeighbors(http_request_metadata_ip.clone()),
            HttpRequestType::GetBlock(http_request_metadata_dns.clone(), StacksBlockId([2u8; 32])),
            HttpRequestType::GetMicroblocksIndexed(
                http_request_metadata_ip.clone(),
                StacksBlockId([3u8; 32]),
            ),
            HttpRequestType::PostTransaction(
                http_request_metadata_dns.clone(),
                make_test_transaction(),
                None,
            ),
            HttpRequestType::OptionsPreflight(http_request_metadata_ip.clone(), "/".to_string()),
        ];

        let mut tx_body = vec![];
        make_test_transaction()
            .consensus_serialize(&mut tx_body)
            .unwrap();

        let mut post_transaction_preamble = HttpRequestPreamble::new(
            HttpVersion::Http11,
            "POST".to_string(),
            "/v2/transactions".to_string(),
            http_request_metadata_dns.peer.hostname(),
            http_request_metadata_dns.peer.port(),
            http_request_metadata_dns.keep_alive,
        );
        post_transaction_preamble.set_content_type(HttpContentType::Bytes);
        post_transaction_preamble.set_content_length(tx_body.len() as u32);

        // all of these should parse
        let expected_http_preambles = vec![
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/neighbors".to_string(),
                http_request_metadata_ip.peer.hostname(),
                http_request_metadata_ip.peer.port(),
                http_request_metadata_ip.keep_alive,
            ),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                format!("/v2/blocks/{}", StacksBlockId([2u8; 32]).to_hex()),
                http_request_metadata_dns.peer.hostname(),
                http_request_metadata_dns.peer.port(),
                http_request_metadata_dns.keep_alive,
            ),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                format!("/v2/microblocks/{}", StacksBlockId([3u8; 32]).to_hex()),
                http_request_metadata_ip.peer.hostname(),
                http_request_metadata_ip.peer.port(),
                http_request_metadata_ip.keep_alive,
            ),
            post_transaction_preamble,
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "OPTIONS".to_string(),
                format!("/"),
                http_request_metadata_ip.peer.hostname(),
                http_request_metadata_ip.peer.port(),
                http_request_metadata_ip.keep_alive,
            ),
        ];

        let expected_http_bodies = vec![vec![], vec![], vec![], tx_body];

        for (test, (expected_http_preamble, expected_http_body)) in tests.iter().zip(
            expected_http_preambles
                .iter()
                .zip(expected_http_bodies.iter()),
        ) {
            let mut expected_bytes = vec![];
            expected_http_preamble
                .consensus_serialize(&mut expected_bytes)
                .unwrap();

            test_debug!(
                "Expected preamble:\n{}",
                str::from_utf8(&expected_bytes).unwrap()
            );

            if expected_http_preamble.content_type.is_none()
                || expected_http_preamble.content_type != Some(HttpContentType::Bytes)
            {
                test_debug!(
                    "Expected http body:\n{}",
                    str::from_utf8(&expected_http_body).unwrap()
                );
            } else {
                test_debug!("Expected http body (hex):\n{}", to_hex(&expected_http_body));
            }

            expected_bytes.append(&mut expected_http_body.clone());

            let mut bytes = vec![];
            let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());
            http.write_message(&mut bytes, &StacksHttpMessage::Request(test.clone()))
                .unwrap();

            assert_eq!(bytes, expected_bytes);
        }
    }

    #[test]
    fn test_http_request_type_codec_err() {
        let bad_content_lengths = vec![
            "GET /v2/neighbors HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
            "GET /v2/blocks/1111111111111111111111111111111111111111111111111111111111111111 HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
            "GET /v2/microblocks/1111111111111111111111111111111111111111111111111111111111111111 HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
            "POST /v2/transactions HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 0\r\n\r\n",
        ];
        for bad_content_length in bad_content_lengths {
            let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());
            let (preamble, offset) = http.read_preamble(bad_content_length.as_bytes()).unwrap();
            let e = http.read_payload(&preamble, &bad_content_length.as_bytes()[offset..]);

            assert!(e.is_err(), "{:?}", &e);
            assert!(
                e.as_ref()
                    .unwrap_err()
                    .to_string()
                    .find("-length body for")
                    .is_some(),
                "{:?}",
                &e
            );
        }

        let bad_content_types = vec![
            "POST /v2/transactions HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
        ];
        for bad_content_type in bad_content_types {
            let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());
            let (preamble, offset) = http.read_preamble(bad_content_type.as_bytes()).unwrap();
            let e = http.read_payload(&preamble, &bad_content_type.as_bytes()[offset..]);
            assert!(e.is_err());
            assert!(e.unwrap_err().to_string().find("Content-Type").is_some());
        }
    }

    #[test]
    fn test_http_response_type_codec() {
        let test_neighbors_info = RPCNeighborsInfo {
            sample: vec![
                RPCNeighbor {
                    network_id: 1,
                    peer_version: 2,
                    addrbytes: PeerAddress([
                        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
                        0x0c, 0x0d, 0x0e, 0x0f,
                    ]),
                    port: 12345,
                    public_key_hash: Hash160::from_bytes(
                        &hex_bytes("1111111111111111111111111111111111111111").unwrap(),
                    )
                    .unwrap(),
                    authenticated: true,
                },
                RPCNeighbor {
                    network_id: 3,
                    peer_version: 4,
                    addrbytes: PeerAddress([
                        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
                        0x01, 0x02, 0x03, 0x04,
                    ]),
                    port: 23456,
                    public_key_hash: Hash160::from_bytes(
                        &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
                    )
                    .unwrap(),
                    authenticated: false,
                },
            ],
            inbound: vec![],
            outbound: vec![],
        };

        let privk = StacksPrivateKey::from_hex(
            "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
        )
        .unwrap();
        let test_block_info = make_codec_test_block(5);
        let test_microblock_info =
            make_sample_microblock_stream(&privk, &test_block_info.block_hash());

        let mut test_block_info_bytes = vec![];
        test_block_info
            .consensus_serialize(&mut test_block_info_bytes)
            .unwrap();

        let mut test_microblock_info_bytes = vec![];
        test_microblock_info
            .consensus_serialize(&mut test_microblock_info_bytes)
            .unwrap();

        let tests = vec![
            // length is known
            (
                HttpResponseType::Neighbors(
                    HttpResponseMetadata::new(
                        HttpVersion::Http11,
                        123,
                        Some(serde_json::to_string(&test_neighbors_info).unwrap().len() as u32),
                        true,
                    ),
                    test_neighbors_info.clone(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Block(
                    HttpResponseMetadata::new(
                        HttpVersion::Http11,
                        123,
                        Some(test_block_info_bytes.len() as u32),
                        true,
                    ),
                    test_block_info.clone(),
                ),
                format!("/v2/blocks/{}", test_block_info.block_hash().to_hex()),
            ),
            (
                HttpResponseType::Microblocks(
                    HttpResponseMetadata::new(
                        HttpVersion::Http11,
                        123,
                        Some(test_microblock_info_bytes.len() as u32),
                        true,
                    ),
                    test_microblock_info.clone(),
                ),
                format!(
                    "/v2/microblocks/{}",
                    test_microblock_info[0].block_hash().to_hex()
                ),
            ),
            (
                HttpResponseType::TransactionID(
                    HttpResponseMetadata::new(
                        HttpVersion::Http11,
                        123,
                        Some((Txid([0x1; 32]).to_hex().len() + 2) as u32),
                        true,
                    ),
                    Txid([0x1; 32]),
                ),
                "/v2/transactions".to_string(),
            ),
            // length is unknown
            (
                HttpResponseType::Neighbors(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, None, true),
                    test_neighbors_info.clone(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Block(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, None, true),
                    test_block_info.clone(),
                ),
                format!("/v2/blocks/{}", test_block_info.block_hash().to_hex()),
            ),
            (
                HttpResponseType::Microblocks(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, None, true),
                    test_microblock_info.clone(),
                ),
                format!(
                    "/v2/microblocks/{}",
                    test_microblock_info[0].block_hash().to_hex()
                ),
            ),
            (
                HttpResponseType::TransactionID(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, None, true),
                    Txid([0x1; 32]),
                ),
                "/v2/transactions".to_string(),
            ),
            // errors without error messages
            (
                HttpResponseType::BadRequest(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Unauthorized(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::PaymentRequired(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Forbidden(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::NotFound(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::ServerError(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::ServiceUnavailable(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Error(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(0), true),
                    502,
                    "".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            // errors with specific messages
            (
                HttpResponseType::BadRequest(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Unauthorized(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::PaymentRequired(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Forbidden(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::NotFound(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::ServerError(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::ServiceUnavailable(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
            (
                HttpResponseType::Error(
                    HttpResponseMetadata::new(HttpVersion::Http11, 123, Some(3), true),
                    502,
                    "foo".to_string(),
                ),
                "/v2/neighbors".to_string(),
            ),
        ];

        let expected_http_preambles = vec![
            // length is known
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                Some(serde_json::to_string(&test_neighbors_info).unwrap().len() as u32),
                HttpContentType::JSON,
                true,
                123,
            ),
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                Some(test_block_info_bytes.len() as u32),
                HttpContentType::Bytes,
                true,
                123,
            ),
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                Some(test_microblock_info_bytes.len() as u32),
                HttpContentType::Bytes,
                true,
                123,
            ),
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                Some((Txid([0x1; 32]).to_hex().len() + 2) as u32),
                HttpContentType::JSON,
                true,
                123,
            ),
            // length is unknown
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                None,
                HttpContentType::JSON,
                true,
                123,
            ),
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                None,
                HttpContentType::Bytes,
                true,
                123,
            ),
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                None,
                HttpContentType::Bytes,
                true,
                123,
            ),
            HttpResponsePreamble::new(
                200,
                "OK".to_string(),
                None,
                HttpContentType::JSON,
                true,
                123,
            ),
            // errors
            HttpResponsePreamble::new_error(400, 123, None),
            HttpResponsePreamble::new_error(401, 123, None),
            HttpResponsePreamble::new_error(402, 123, None),
            HttpResponsePreamble::new_error(403, 123, None),
            HttpResponsePreamble::new_error(404, 123, None),
            HttpResponsePreamble::new_error(500, 123, None),
            HttpResponsePreamble::new_error(503, 123, None),
            // generic error
            HttpResponsePreamble::new_error(502, 123, None),
            // errors with messages
            HttpResponsePreamble::new_error(400, 123, Some("foo".to_string())),
            HttpResponsePreamble::new_error(401, 123, Some("foo".to_string())),
            HttpResponsePreamble::new_error(402, 123, Some("foo".to_string())),
            HttpResponsePreamble::new_error(403, 123, Some("foo".to_string())),
            HttpResponsePreamble::new_error(404, 123, Some("foo".to_string())),
            HttpResponsePreamble::new_error(500, 123, Some("foo".to_string())),
            HttpResponsePreamble::new_error(503, 123, Some("foo".to_string())),
            HttpResponsePreamble::new_error(502, 123, Some("foo".to_string())),
        ];

        let expected_http_bodies = vec![
            // with content-length
            serde_json::to_string(&test_neighbors_info)
                .unwrap()
                .as_bytes()
                .to_vec(),
            test_block_info_bytes.clone(),
            test_microblock_info_bytes.clone(),
            Txid([0x1; 32]).to_hex().as_bytes().to_vec(),
            // with transfer-encoding: chunked
            serde_json::to_string(&test_neighbors_info)
                .unwrap()
                .as_bytes()
                .to_vec(),
            test_block_info_bytes,
            test_microblock_info_bytes,
            Txid([0x1; 32]).to_hex().as_bytes().to_vec(),
            // errors
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            // errors with messages
            "foo".as_bytes().to_vec(),
            "foo".as_bytes().to_vec(),
            "foo".as_bytes().to_vec(),
            "foo".as_bytes().to_vec(),
            "foo".as_bytes().to_vec(),
            "foo".as_bytes().to_vec(),
            "foo".as_bytes().to_vec(),
            "foo".as_bytes().to_vec(),
        ];

        for ((test, request_path), (expected_http_preamble, _expected_http_body)) in
            tests.iter().zip(
                expected_http_preambles
                    .iter()
                    .zip(expected_http_bodies.iter()),
            )
        {
            let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());
            let mut bytes = vec![];
            test_debug!("write body:\n{:?}\n", test);

            http.begin_request(HttpVersion::Http11, request_path.to_string());
            http.write_message(&mut bytes, &StacksHttpMessage::Response((*test).clone()))
                .unwrap();

            let (mut preamble, offset) = match http.read_preamble(&bytes) {
                Ok((p, o)) => (p, o),
                Err(e) => {
                    test_debug!("first 4096 bytes:\n{:?}\n", &bytes[0..].to_vec());
                    test_debug!("error: {:?}", &e);
                    assert!(false);
                    unreachable!();
                }
            };

            test_debug!("read preamble of {} bytes\n{:?}\n", offset, preamble);

            test_debug!("read http body\n{:?}\n", &bytes[offset..].to_vec());

            let (message, _total_len) = if expected_http_preamble.is_chunked() {
                let (msg_opt, len) = http
                    .stream_payload(&preamble, &mut &bytes[offset..])
                    .unwrap();
                (msg_opt.unwrap().0, len)
            } else {
                http.read_payload(&preamble, &bytes[offset..]).unwrap()
            };

            test_debug!("got message\n{:?}\n", &message);

            // check everything in the parsed preamble except for the extra headers
            match preamble {
                StacksHttpPreamble::Response(ref mut req) => {
                    assert_eq!(req.headers.len(), 5);
                    assert!(req.headers.get("access-control-allow-headers").is_some());
                    assert!(req.headers.get("access-control-allow-methods").is_some());
                    assert!(req.headers.get("access-control-allow-origin").is_some());
                    assert!(req.headers.get("server").is_some());
                    assert!(req.headers.get("date").is_some());
                    req.headers.clear();
                }
                StacksHttpPreamble::Request(_) => {
                    panic!("parsed a request");
                }
            }

            assert_eq!(
                preamble,
                StacksHttpPreamble::Response((*expected_http_preamble).clone())
            );
            assert_eq!(message, StacksHttpMessage::Response((*test).clone()));
            assert_eq!(http.num_pending(), 0);
        }
    }

    #[test]
    fn test_http_response_type_codec_err() {
        let request_paths = vec![
            "/v2/blocks/1111111111111111111111111111111111111111111111111111111111111111",
            "/v2/transactions",
            "/v2/neighbors",
            "/v2/neighbors",
            "/v2/neighbors",
        ];
        let bad_request_payloads = vec![
            "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 2\r\n\r\nab",
            "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 4\r\n\r\n\"ab\"",
            "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 1\r\n\r\n{",
            "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 1\r\n\r\na",
            "HTTP/1.1 400 Bad Request\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 2\r\n\r\n{}",
        ];
        let expected_bad_request_payload_errors = vec![
            "Invalid content-type",
            "Invalid txid:",
            "Not enough bytes",
            "Failed to parse",
            "expected text/plain",
        ];
        for (test, (expected_error, request_path)) in bad_request_payloads.iter().zip(
            expected_bad_request_payload_errors
                .iter()
                .zip(request_paths),
        ) {
            test_debug!(
                "Expect failure:\n{}\nExpected error: '{}'",
                test,
                expected_error
            );

            let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());
            http.begin_request(HttpVersion::Http11, request_path.to_string());

            let (preamble, offset) = http.read_preamble(test.as_bytes()).unwrap();
            let e = http.read_payload(&preamble, &test.as_bytes()[offset..]);
            let errstr = format!("{:?}", &e);
            assert!(e.is_err());
            assert!(
                e.unwrap_err().to_string().find(expected_error).is_some(),
                "{}",
                errstr
            );
        }
    }

    #[test]
    fn test_http_headers_too_big() {
        let bad_header_value = std::iter::repeat("A")
            .take(HTTP_PREAMBLE_MAX_ENCODED_SIZE as usize)
            .collect::<String>();
        let bad_request_preamble = format!(
            "GET /v2/neighbors HTTP/1.1\r\nHost: localhost:1234\r\nBad-Header: {}\r\n\r\n",
            &bad_header_value
        );
        let bad_response_preamble = format!("HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-ID: 123\r\nContent-Type: text/plain\r\nContent-Length: 64\r\nBad-Header: {}\r\n\r\n", &bad_header_value);

        let request_err =
            HttpRequestPreamble::consensus_deserialize(&mut bad_request_preamble.as_bytes())
                .unwrap_err();
        let response_err =
            HttpResponsePreamble::consensus_deserialize(&mut bad_response_preamble.as_bytes())
                .unwrap_err();

        let protocol_request_err =
            StacksHttpPreamble::consensus_deserialize(&mut bad_request_preamble.as_bytes())
                .unwrap_err();
        let protocol_response_err =
            StacksHttpPreamble::consensus_deserialize(&mut bad_response_preamble.as_bytes())
                .unwrap_err();

        eprintln!("request_err: {:?}", &request_err);
        eprintln!("response_err: {:?}", &response_err);

        eprintln!("protocol_request_err: {:?}", &protocol_request_err);
        eprintln!("protocol_response_err: {:?}", &protocol_response_err);

        assert!(request_err
            .to_string()
            .find("Not enough bytes to form a HTTP request preamble")
            .is_some());
        assert!(response_err
            .to_string()
            .find("Not enough bytes to form a HTTP response preamble")
            .is_some());
        assert!(protocol_request_err
            .to_string()
            .find("Failed to decode HTTP request or HTTP response")
            .is_some());
        assert!(protocol_response_err
            .to_string()
            .find("Failed to decode HTTP request or HTTP response")
            .is_some());
    }

    #[test]
    fn test_http_headers_too_many() {
        let mut too_many_headers_list = vec![];
        for i in 0..HTTP_PREAMBLE_MAX_NUM_HEADERS {
            too_many_headers_list.push(format!("H{}: {}\r\n", i + 1, i + 1));
        }
        let too_many_headers = too_many_headers_list.join("");
        let bad_request_preamble = format!(
            "GET /v2/neighbors HTTP/1.1\r\nHost: localhost:1234\r\n{}\r\n",
            &too_many_headers
        );
        let bad_response_preamble = format!("HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-ID: 123\r\nContent-Type: text/plain\r\nContent-Length: 64\r\n{}\r\n", &too_many_headers);

        let request_err =
            HttpRequestPreamble::consensus_deserialize(&mut bad_request_preamble.as_bytes())
                .unwrap_err();
        let response_err =
            HttpResponsePreamble::consensus_deserialize(&mut bad_response_preamble.as_bytes())
                .unwrap_err();

        let protocol_request_err =
            StacksHttpPreamble::consensus_deserialize(&mut bad_request_preamble.as_bytes())
                .unwrap_err();
        let protocol_response_err =
            StacksHttpPreamble::consensus_deserialize(&mut bad_response_preamble.as_bytes())
                .unwrap_err();

        eprintln!("request_err: {:?}", &request_err);
        eprintln!("response_err: {:?}", &response_err);

        eprintln!("protocol_request_err: {:?}", &protocol_request_err);
        eprintln!("protocol_response_err: {:?}", &protocol_response_err);

        assert!(request_err
            .to_string()
            .find("Failed to parse HTTP request: TooManyHeaders")
            .is_some());
        assert!(response_err
            .to_string()
            .find("Failed to parse HTTP response: TooManyHeaders")
            .is_some());
        assert!(protocol_request_err
            .to_string()
            .find("Failed to decode HTTP request or HTTP response")
            .is_some());
        assert!(protocol_response_err
            .to_string()
            .find("Failed to decode HTTP request or HTTP response")
            .is_some());
    }

    #[test]
    fn test_http_duplicate_concurrent_streamed_response_fails() {
        // do not permit multiple in-flight chunk-encoded HTTP responses with the same request ID.
        let valid_neighbors_response = "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nTransfer-Encoding: chunked\r\n\r\n28\r\n{\"sample\":[],\"inbound\":[],\"outbound\":[]}\r\n0\r\n\r\n";
        let invalid_neighbors_response = "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nTransfer-Encoding: chunked\r\n\r\n10\r\nxxxxxxxxxxxxxxxx\r\n0\r\n\r\n";
        let invalid_chunked_response = "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nTransfer-Encoding: chunked\r\n\r\n29\r\n{\"sample\":[],\"inbound\":[],\"outbound\":[]}\r\n0\r\n\r\n";

        let mut http = StacksHttp::new("127.0.0.1:20443".parse().unwrap());

        http.begin_request(HttpVersion::Http11, "/v2/neighbors".to_string());
        let (preamble, offset) = http
            .read_preamble(valid_neighbors_response.as_bytes())
            .unwrap();
        assert_eq!(http.num_pending(), 1);

        let res = http.read_preamble(valid_neighbors_response.as_bytes());
        assert!(res.is_err());
        assert!(res.unwrap_err().to_string().find("in progress").is_some());

        // finish reading the body
        let msg = http
            .stream_payload(
                &preamble,
                &mut &valid_neighbors_response.as_bytes()[offset..],
            )
            .unwrap();
        match msg {
            (
                Some((
                    StacksHttpMessage::Response(HttpResponseType::Neighbors(_, neighbors_data)),
                    _,
                )),
                _,
            ) => assert_eq!(
                neighbors_data,
                RPCNeighborsInfo {
                    sample: vec![],
                    inbound: vec![],
                    outbound: vec![]
                }
            ),
            _ => {
                error!("Got {:?}", &msg);
                assert!(false);
            }
        }
        assert_eq!(http.num_pending(), 0);

        // can read the preamble again, but only once
        http.begin_request(HttpVersion::Http11, "/v2/neighbors".to_string());
        let (preamble, offset) = http
            .read_preamble(invalid_neighbors_response.as_bytes())
            .unwrap();
        assert_eq!(http.num_pending(), 1);

        let res = http.read_preamble(valid_neighbors_response.as_bytes());
        assert!(res.is_err());
        assert!(res.unwrap_err().to_string().find("in progress").is_some());

        // reading a corrupt body unlocks the ability to read the preamble again
        let res = http.stream_payload(
            &preamble,
            &mut &invalid_neighbors_response.as_bytes()[offset..],
        );
        assert!(res.unwrap_err().to_string().find("JSON").is_some());
        assert_eq!(http.num_pending(), 0);

        // can read the premable again, but only once
        http.begin_request(HttpVersion::Http11, "/v2/neighbors".to_string());
        let (preamble, offset) = http
            .read_preamble(invalid_chunked_response.as_bytes())
            .unwrap();
        let res = http.read_preamble(valid_neighbors_response.as_bytes());

        assert!(res.is_err());
        assert!(res.unwrap_err().to_string().find("in progress").is_some());

        // reading a corrupt chunk stream unlocks the ability to read the preamble again
        let res = http.stream_payload(
            &preamble,
            &mut &invalid_chunked_response.as_bytes()[offset..],
        );
        assert!(res
            .unwrap_err()
            .to_string()
            .find("Invalid chunk trailer")
            .is_some());
        assert_eq!(http.num_pending(), 0);
    }

    #[test]
    fn test_http_request_version_keep_alive() {
        let requests = vec![
            HttpRequestPreamble::new(
                HttpVersion::Http10,
                "GET".to_string(),
                "/v2/info".to_string(),
                "localhost".to_string(),
                8080,
                true,
            ),
            HttpRequestPreamble::new(
                HttpVersion::Http10,
                "GET".to_string(),
                "/v2/info".to_string(),
                "localhost".to_string(),
                8080,
                false,
            ),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/info".to_string(),
                "localhost".to_string(),
                8080,
                true,
            ),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/info".to_string(),
                "localhost".to_string(),
                8080,
                false,
            ),
        ];

        // (have 'connection' header?, have 'keep-alive' value?)
        let requests_connection_expected =
            vec![(true, true), (false, false), (false, false), (true, false)];

        for (r, (has_connection, is_keep_alive)) in
            requests.iter().zip(requests_connection_expected.iter())
        {
            let mut bytes = vec![];
            r.consensus_serialize(&mut bytes).unwrap();
            let txt = String::from_utf8(bytes).unwrap();

            eprintln!(
                "has_connection: {}, is_keep_alive: {}\n{}",
                *has_connection, *is_keep_alive, &txt
            );
            if *has_connection {
                if *is_keep_alive {
                    assert!(txt.find("Connection: keep-alive\r\n").is_some());
                } else {
                    assert!(txt.find("Connection: close\r\n").is_some());
                }
            } else {
                assert!(txt.find("Connection: ").is_none());
            }
        }
    }

    #[test]
    fn test_http_response_version_keep_alive() {
        // (version, explicit keep-alive?)
        let responses_args = vec![
            (HttpVersion::Http10, true),
            (HttpVersion::Http10, false),
            (HttpVersion::Http11, true),
            (HttpVersion::Http11, false),
        ];

        let mut responses = vec![];
        for res in responses_args.iter() {
            let mut bytes = vec![];
            let md = HttpResponseMetadata::new(res.0.clone(), 123, None, res.1);
            HttpResponsePreamble::new_serialized(
                &mut bytes,
                200,
                "OK",
                None,
                &HttpContentType::JSON,
                123,
                |ref mut fd| keep_alive_headers(fd, &md),
            )
            .unwrap();
            responses.push(String::from_utf8(bytes).unwrap());
        }

        for (response, (version, sent_keep_alive)) in responses.iter().zip(responses_args.iter()) {
            test_debug!(
                "version: {:?}, sent keep-alive: {}, response:\n{}",
                version,
                sent_keep_alive,
                response
            );
            match version {
                HttpVersion::Http10 => {
                    // be explicit about Connection: with http/1.0 clients
                    if *sent_keep_alive {
                        assert!(response.find("Connection: keep-alive\r\n").is_some());
                    } else {
                        assert!(response.find("Connection: close\r\n").is_some());
                    }
                }
                HttpVersion::Http11 => {
                    if *sent_keep_alive {
                        // we don't send connection: keep-alive if the client is 1.1 and it didn't
                        // send its own connection: <option>
                        assert!(response.find("Connection:").is_none());
                    } else {
                        assert!(response.find("Connection: close\r\n").is_some());
                    }
                }
            }
        }
    }

    #[test]
    fn test_http_parse_proof_tip_query() {
        let query_txt = "tip=7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392";
        assert_eq!(
            HttpRequestType::get_chain_tip_query(Some(query_txt)).unwrap(),
            StacksBlockId::from_hex(
                "7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392"
            )
            .unwrap()
        );

        // first parseable tip is taken
        let query_txt_dup = "tip=7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392&tip=03e26bd68a8722f8b3861e2058edcafde094ad059e152754986c3573306698f1";
        assert_eq!(
            HttpRequestType::get_chain_tip_query(Some(query_txt_dup)).unwrap(),
            StacksBlockId::from_hex(
                "7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392"
            )
            .unwrap()
        );

        // first parseable tip is taken
        let query_txt_dup = "tip=bad&tip=7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392&tip=03e26bd68a8722f8b3861e2058edcafde094ad059e152754986c3573306698f1";
        assert_eq!(
            HttpRequestType::get_chain_tip_query(Some(query_txt_dup)).unwrap(),
            StacksBlockId::from_hex(
                "7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392"
            )
            .unwrap()
        );

        // tip can be skipped
        let query_txt_bad = "tip=bad";
        assert_eq!(
            HttpRequestType::get_chain_tip_query(Some(query_txt_bad)),
            None
        );

        // tip can be skipped
        let query_txt_none = "tip=bad";
        assert_eq!(
            HttpRequestType::get_chain_tip_query(Some(query_txt_none)),
            None
        );
    }

    #[test]
    fn test_http_live_headers() {
        // headers pulled from prod
        let live_headers = &[
            "GET /v2/info HTTP/1.1\r\naccept-language: en-US,en;q=0.9\r\naccept-encoding: gzip, deflate, br\r\nsec-fetch-dest: document\r\nsec-fetch-user: ?1\r\nsec-fetch-mode: navigate\r\nsec-fetch-site: none\r\naccept: text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9\r\nuser-agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_3) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/81.0.4044.113 Safari/537.36\r\nupgrade-insecure-requests: 1\r\ncache-control: max-age=0\r\nconnection: close\r\nx-forwarded-port: 443\r\nx-forwarded-host: crashy-stacky.zone117x.com\r\nx-forwarded-proto: https\r\nx-forwarded-for: 213.127.17.55\r\nx-real-ip: 213.127.17.55\r\nhost: stacks-blockchain:20443\r\n\r\n"
        ];

        let bad_live_headers = &[
            "GET /favicon.ico HTTP/1.1\r\nConnection: upgrade\r\nHost: crashy-stacky.zone117x.com\r\nX-Real-IP: 213.127.17.55\r\nX-Forwarded-For: 213.127.17.55\r\nX-Forwarded-Proto: http\r\nX-Forwarded-Host: crashy-stacky.zone117x.com\r\nX-Forwarded-Port: 9001\r\nUser-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_3) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/81.0.4044.113 Safari/537.36\r\nAccept: image/webp,image/apng,image/*,*/*;q=0.8\r\nReferer: http://crashy-stacky.zone117x.com:9001/v2/info\r\nAccept-Encoding: gzip, deflate\r\nAccept-Language: en-US,en;q=0.9\r\n\r\n",
        ];

        for live_header in live_headers {
            let res = HttpRequestPreamble::consensus_deserialize(&mut live_header.as_bytes());
            assert!(res.is_ok(), "headers: {}\nerror: {:?}", live_header, &res);
        }

        for bad_live_header in bad_live_headers {
            let res = HttpRequestPreamble::consensus_deserialize(&mut bad_live_header.as_bytes());
            assert!(
                res.is_err(),
                "headers: {}\nshould not have parsed",
                bad_live_header
            );
        }
    }

    // TODO: test mismatch between request path and reply
}
