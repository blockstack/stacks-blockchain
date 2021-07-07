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

use rand::{thread_rng, Rng};
use std::fs;
use std::net;
use std::net::Shutdown;
use std::ops::Deref;
use std::ops::DerefMut;
use std::path;
use std::path::PathBuf;
use std::time;
use std::time::Duration;

use burnchains::bitcoin::blocks::BitcoinHeaderIPC;
use burnchains::bitcoin::messages::BitcoinMessageHandler;
use burnchains::bitcoin::spv::*;
use burnchains::bitcoin::Error as btc_error;
use burnchains::indexer::BurnchainIndexer;
use burnchains::indexer::*;
use burnchains::Burnchain;

use burnchains::bitcoin::blocks::{BitcoinBlockDownloader, BitcoinBlockParser};
use burnchains::bitcoin::BitcoinNetworkType;

use crate::types::chainstate::BurnchainHeaderHash;
use burnchains::Error as burnchain_error;
use burnchains::MagicBytes;
use burnchains::BLOCKSTACK_MAGIC_MAINNET;

use deps::bitcoin::blockdata::block::LoneBlockHeader;
use deps::bitcoin::network::message::NetworkMessage;
use deps::bitcoin::network::serialize::BitcoinHash;
use deps::bitcoin::network::serialize::Error as btc_serialization_err;
use util::log;

pub const USER_AGENT: &'static str = "Stacks/2.0";

pub const BITCOIN_MAINNET: u32 = 0xD9B4BEF9;
pub const BITCOIN_TESTNET: u32 = 0x0709110B;
pub const BITCOIN_REGTEST: u32 = 0xDAB5BFFA;

pub const BITCOIN_MAINNET_NAME: &'static str = "mainnet";
pub const BITCOIN_TESTNET_NAME: &'static str = "testnet";
pub const BITCOIN_REGTEST_NAME: &'static str = "regtest";

// batch size for searching for a reorg
// kept small since sometimes bitcoin will just send us one header at a time
#[cfg(not(test))]
const REORG_BATCH_SIZE: u64 = 16;
#[cfg(test)]
const REORG_BATCH_SIZE: u64 = 2;

pub fn network_id_to_bytes(network_id: BitcoinNetworkType) -> u32 {
    match network_id {
        BitcoinNetworkType::Mainnet => BITCOIN_MAINNET,
        BitcoinNetworkType::Testnet => BITCOIN_TESTNET,
        BitcoinNetworkType::Regtest => BITCOIN_REGTEST,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BitcoinIndexerConfig {
    // config fields
    pub peer_host: String,
    pub peer_port: u16,
    pub rpc_port: u16,
    pub rpc_ssl: bool,
    pub username: Option<String>,
    pub password: Option<String>,
    pub timeout: u32,
    pub spv_headers_path: String,
    pub first_block: u64,
    pub magic_bytes: MagicBytes,
}

#[derive(Debug)]
pub struct BitcoinIndexerRuntime {
    sock: Option<net::TcpStream>,
    pub services: u64,
    pub user_agent: String,
    pub version_nonce: u64,
    pub network_id: BitcoinNetworkType,
    pub block_height: u64,
    pub last_getdata_send_time: u64,
    pub last_getheaders_send_time: u64,
    pub timeout: u64,
}

pub struct BitcoinIndexer {
    pub config: BitcoinIndexerConfig,
    pub runtime: BitcoinIndexerRuntime,
}

impl BitcoinIndexerConfig {
    pub fn default(first_block: u64) -> BitcoinIndexerConfig {
        BitcoinIndexerConfig {
            peer_host: "bitcoin.blockstack.com".to_string(),
            peer_port: 8333,
            rpc_port: 8332,
            rpc_ssl: false,
            username: Some("blockstack".to_string()),
            password: Some("blockstacksystem".to_string()),
            timeout: 30,
            spv_headers_path: "./headers.sqlite".to_string(),
            first_block,
            magic_bytes: BLOCKSTACK_MAGIC_MAINNET.clone(),
        }
    }

    pub fn default_regtest(spv_headers_path: String) -> BitcoinIndexerConfig {
        BitcoinIndexerConfig {
            peer_host: "127.0.0.1".to_string(),
            peer_port: 18444,
            rpc_port: 18443,
            rpc_ssl: false,
            username: Some("blockstack".to_string()),
            password: Some("blockstacksystem".to_string()),
            timeout: 30,
            spv_headers_path: spv_headers_path,
            first_block: 0,
            magic_bytes: BLOCKSTACK_MAGIC_MAINNET.clone(),
        }
    }
}

impl BitcoinIndexerRuntime {
    pub fn new(network_id: BitcoinNetworkType) -> BitcoinIndexerRuntime {
        let mut rng = thread_rng();
        BitcoinIndexerRuntime {
            sock: None,
            services: 0,
            user_agent: USER_AGENT.to_owned(),
            version_nonce: rng.gen(),
            network_id: network_id,
            block_height: 0,
            last_getdata_send_time: 0,
            last_getheaders_send_time: 0,
            timeout: 300,
        }
    }
}

impl BitcoinIndexer {
    pub fn new(config: BitcoinIndexerConfig, runtime: BitcoinIndexerRuntime) -> BitcoinIndexer {
        BitcoinIndexer {
            config: config,
            runtime: runtime,
        }
    }

    pub fn dup(&self) -> BitcoinIndexer {
        BitcoinIndexer {
            config: self.config.clone(),
            runtime: BitcoinIndexerRuntime::new(self.runtime.network_id),
        }
    }

    /// (re)connect to our configured network peer.
    /// Sets self.runtime.sock to a new socket referring to our configured
    /// Bitcoin peer.  If we fail to connect, this method sets the socket
    /// to None.
    fn reconnect_peer(&mut self) -> Result<(), btc_error> {
        match net::TcpStream::connect((self.config.peer_host.as_str(), self.config.peer_port)) {
            Ok(s) => {
                // Disable Nagle algorithm
                s.set_nodelay(true).map_err(|_e| {
                    test_debug!("Failed to set TCP_NODELAY: {:?}", &_e);
                    btc_error::ConnectionError
                })?;

                // set timeout
                s.set_read_timeout(Some(Duration::from_secs(self.runtime.timeout)))
                    .map_err(|_e| {
                        test_debug!("Failed to set TCP read timeout: {:?}", &_e);
                        btc_error::ConnectionError
                    })?;

                s.set_write_timeout(Some(Duration::from_secs(self.runtime.timeout)))
                    .map_err(|_e| {
                        test_debug!("Failed to set TCP write timeout: {:?}", &_e);
                        btc_error::ConnectionError
                    })?;

                match self.runtime.sock.take() {
                    Some(s) => {
                        let _ = s.shutdown(Shutdown::Both);
                    }
                    None => {}
                }

                self.runtime.sock = Some(s);
                Ok(())
            }
            Err(_e) => {
                let s = self.runtime.sock.take();
                match s {
                    Some(s) => {
                        let _ = s.shutdown(Shutdown::Both);
                    }
                    None => {}
                }
                Err(btc_error::ConnectionError)
            }
        }
    }

    /// Run code with the socket
    pub fn with_socket<F, R>(&mut self, closure: F) -> Result<R, btc_error>
    where
        F: FnOnce(&mut net::TcpStream) -> Result<R, btc_error>,
    {
        let mut sock = self.runtime.sock.take();
        let res = match sock {
            Some(ref mut s) => closure(s),
            None => Err(btc_error::SocketNotConnectedToPeer),
        };
        self.runtime.sock = sock;
        res
    }

    /// Are we connected?
    fn is_connected(&mut self) -> bool {
        self.runtime.sock.is_some()
    }

    /// Carry on a conversation with the bitcoin peer.
    /// Handle version, verack, ping, and pong messages automatically.
    /// Reconnect to the peer automatically if the peer closes the connection.
    /// Pass any other messages to a given message handler.
    pub fn peer_communicate<T: BitcoinMessageHandler>(
        &mut self,
        message_handler: &mut T,
        initial_handshake: bool,
    ) -> Result<(), btc_error> {
        let mut do_handshake = initial_handshake || !self.is_connected();
        let mut keep_going = true;
        let mut initiated = false;

        while keep_going {
            if do_handshake {
                debug!("(Re)establish peer connection");

                initiated = false;
                let handshake_result = self.connect_handshake_backoff();
                match handshake_result {
                    Ok(_block_height) => {
                        // connection established!
                        do_handshake = false;
                    }
                    Err(_) => {
                        // need to try again
                        continue;
                    }
                }
            }

            if !initiated {
                // initiate the conversation
                match message_handler.begin_session(self) {
                    Ok(status) => {
                        if !status {
                            debug!("begin_session() terminates conversation");
                            break;
                        }
                        initiated = true;
                    }
                    Err(btc_error::ConnectionBroken) => {
                        debug!("Re-establish peer connection");
                        do_handshake = true;
                    }
                    Err(e) => {
                        warn!("Unhandled error while initiating conversation: {:?}", e);
                        return Err(e);
                    }
                }
            }

            match self.recv_message() {
                Ok(msg) => {
                    // got a message; go consume it
                    let handled = self.handle_message(msg, Some(message_handler));
                    match handled {
                        Ok(do_continue) => {
                            keep_going = do_continue;
                            if !keep_going {
                                debug!("Message handler indicates to stop");
                            }
                        }
                        Err(btc_error::UnhandledMessage(m)) => {
                            match m {
                                // some Bitcoin nodes send this to tell us to upgrade, so just
                                // consume it
                                NetworkMessage::Alert(..) => {}
                                _ => {
                                    // TODO: handle inv block-push
                                    debug!("Unhandled message {:?}", m);
                                }
                            }
                        }
                        Err(btc_error::ConnectionBroken) => {
                            debug!("Re-establish peer connection");
                            do_handshake = true;
                        }
                        Err(e) => {
                            warn!("Unhandled error {:?}", e);
                            return Err(e);
                        }
                    }
                }
                Err(btc_error::ConnectionBroken) => {
                    do_handshake = true;
                }
                Err(btc_error::SerializationError(
                    btc_serialization_err::UnrecognizedNetworkCommand(s),
                )) => {
                    debug!("Received unrecognized network command while receiving a message: {}, ignoring", s);
                }
                Err(e) => {
                    warn!("Unhandled error while receiving a message: {:?}", e);
                    do_handshake = true;
                }
            }
        }
        Ok(())
    }

    /// Synchronize a range of headers from bitcoin to a specific file.
    /// If last_block is None, then sync as many headers as the remote peer has to offer.
    /// Returns the height of the last block fetched
    pub fn sync_last_headers(
        &mut self,
        start_block: u64,
        last_block: Option<u64>,
    ) -> Result<u64, btc_error> {
        debug!("Sync all headers starting at block {}", start_block);
        let mut spv_client = SpvClient::new(
            &self.config.spv_headers_path,
            start_block,
            last_block,
            self.runtime.network_id,
            true,
            false,
        )?;
        spv_client
            .run(self)
            .and_then(|_r| Ok(spv_client.end_block_height.unwrap()))
    }

    /// Create a SPV client for starting reorg processing
    fn setup_reorg_headers(
        &mut self,
        canonical_spv_client: &SpvClient,
        reorg_headers_path: &str,
        start_block: u64,
    ) -> Result<SpvClient, btc_error> {
        if PathBuf::from(&reorg_headers_path).exists() {
            fs::remove_file(&reorg_headers_path).map_err(|e| {
                error!("Failed to remove {}", reorg_headers_path);
                btc_error::Io(e)
            })?;
        }

        // bootstrap reorg client
        let mut reorg_spv_client = SpvClient::new(
            &reorg_headers_path,
            start_block,
            Some(start_block + REORG_BATCH_SIZE),
            self.runtime.network_id,
            true,
            true,
        )?;
        if start_block > 0 {
            let start_header = canonical_spv_client
                .read_block_header(start_block)?
                .expect(&format!("BUG: missing block header for {}", start_block));
            reorg_spv_client.insert_block_headers_before(start_block - 1, vec![start_header])?;
        }

        Ok(reorg_spv_client)
    }

    /// Search for a bitcoin reorg.  Return the offset into the canonical bitcoin headers where
    /// the reorg starts.  Returns the hight of the highest common ancestor, and its block hash.
    /// Note that under certain testnet settings, the bitcoin chain itself can shrink.
    pub fn find_bitcoin_reorg<F>(
        &mut self,
        canonical_headers_path: &str,
        reorg_headers_path: &str,
        mut load_reorg_headers: F,
    ) -> Result<u64, btc_error>
    where
        F: FnMut(&mut BitcoinIndexer, &mut SpvClient, u64, Option<u64>) -> Result<(), btc_error>,
    {
        let mut new_tip = 0;
        let mut found_common_ancestor = false;

        let orig_spv_client = SpvClient::new(
            canonical_headers_path,
            0,
            None,
            self.runtime.network_id,
            false,
            false,
        )?;

        // what's the last header we have from the canonical history?
        let canonical_end_block = orig_spv_client.get_headers_height().map_err(|e| {
            error!(
                "Failed to get the last block from {}",
                canonical_headers_path
            );
            e
        })?;

        // bootstrap reorg client
        let mut start_block = canonical_end_block.saturating_sub(REORG_BATCH_SIZE);
        let mut reorg_spv_client =
            self.setup_reorg_headers(&orig_spv_client, reorg_headers_path, start_block)?;
        let mut discontiguous_header_error_count = 0;

        while !found_common_ancestor {
            debug!(
                "Search for reorg'ed Bitcoin headers from {} - {}",
                start_block,
                start_block + REORG_BATCH_SIZE
            );

            // get new headers, starting off of start_block.  Feed them into the given
            // reorg_spv_client.
            match load_reorg_headers(
                self,
                &mut reorg_spv_client,
                start_block,
                Some(start_block + REORG_BATCH_SIZE),
            ) {
                Ok(_) => {}
                Err(btc_error::NoncontiguousHeader) | Err(btc_error::InvalidPoW) => {
                    warn!(
                        "Received invalid headers from {} - {} -- possible reorg in progress",
                        start_block,
                        start_block + REORG_BATCH_SIZE
                    );
                    if start_block == 0 {
                        // reorg all the way back to genesis
                        new_tip = 0;
                        break;
                    }

                    // try again
                    discontiguous_header_error_count += 1;
                    start_block = start_block
                        .saturating_sub(REORG_BATCH_SIZE * discontiguous_header_error_count);
                    reorg_spv_client = self.setup_reorg_headers(
                        &orig_spv_client,
                        reorg_headers_path,
                        start_block,
                    )?;
                    continue;
                }
                Err(e) => {
                    error!(
                        "Failed to fetch Bitcoin headers from {} - {}: {:?}",
                        start_block,
                        start_block + REORG_BATCH_SIZE,
                        &e
                    );
                    return Err(e);
                }
            }

            let reorg_headers = reorg_spv_client
                .read_block_headers(start_block, start_block + REORG_BATCH_SIZE)
                .map_err(|e| {
                    error!(
                        "Failed to read reorg Bitcoin headers from {} to {}",
                        start_block,
                        start_block + REORG_BATCH_SIZE
                    );
                    e
                })?;

            if reorg_headers.len() == 0 {
                // chain shrank considerably
                info!(
                    "Missing Bitcoin headers in block range {}-{} -- did the Bitcoin chain shrink?",
                    start_block,
                    start_block + REORG_BATCH_SIZE
                );
                if start_block == 0 {
                    // reorg chain is empty
                    new_tip = 0;
                    break;
                }

                start_block = start_block.saturating_sub(REORG_BATCH_SIZE);
                reorg_spv_client.set_scan_range(start_block, Some(start_block + REORG_BATCH_SIZE));
                continue;
            }

            // got reorg headers.  Find the equivalent headers in our canonical history
            let canonical_headers = orig_spv_client
                .read_block_headers(start_block, start_block + REORG_BATCH_SIZE)
                .map_err(|e| {
                    error!(
                        "Failed to read canonical headers from {} to {}",
                        start_block,
                        start_block + REORG_BATCH_SIZE
                    );
                    e
                })?;

            assert!(
                canonical_headers.len() > 0,
                "BUG: uninitialized canonical SPV headers DB"
            );

            let max_headers_len = if canonical_headers.len() < reorg_headers.len() {
                canonical_headers.len()
            } else {
                reorg_headers.len()
            };
            let max_height = start_block + (max_headers_len as u64);

            // scan for common ancestor, but excluding the block we wrote to bootstrap the
            // reorg_spv_client.
            for i in (start_block + 1..max_height).rev() {
                if canonical_headers[(i - start_block) as usize].header
                    == reorg_headers[(i - start_block) as usize].header
                {
                    // found common ancestor
                    debug!(
                        "Found common Bitcoin block ancestor at height {}: {:?}",
                        i,
                        &canonical_headers[(i - start_block) as usize].header
                    );
                    new_tip = i;
                    found_common_ancestor = true;
                    break;
                } else {
                    debug!(
                        "Diverged headers at {}: {:?} != {:?}",
                        i,
                        &canonical_headers[(i - start_block) as usize].header,
                        &reorg_headers[(i - start_block) as usize].header
                    );
                }
            }
            if found_common_ancestor {
                break;
            }

            debug!(
                "No common ancestor found between Bitcoin headers {}-{}",
                start_block, max_height
            );

            if start_block == 0 {
                break;
            }

            // try again
            start_block = start_block.saturating_sub(REORG_BATCH_SIZE);
            reorg_spv_client =
                self.setup_reorg_headers(&orig_spv_client, reorg_headers_path, start_block)?;
        }

        debug!("Bitcoin headers history is consistent up to {}", new_tip);

        let hdr_reorg = reorg_spv_client.read_block_header(new_tip)?;
        let hdr_canonical = orig_spv_client.read_block_header(new_tip)?;
        assert_eq!(hdr_reorg, hdr_canonical);

        Ok(new_tip)
    }
}

impl Drop for BitcoinIndexer {
    fn drop(&mut self) {
        match self.runtime.sock {
            Some(ref mut s) => {
                let _ = s.shutdown(Shutdown::Both);
            }
            None => {}
        }
    }
}

impl BurnchainIndexer for BitcoinIndexer {
    type P = BitcoinBlockParser;

    /// Connect to the Bitcoin peer network.
    /// Use the peer host and peer port given in the config file,
    /// and loaded in on setup.  Don't call this before init().
    fn connect(&mut self) -> Result<(), burnchain_error> {
        self.reconnect_peer().map_err(burnchain_error::Bitcoin)
    }

    /// Get the location on disk where we keep headers
    fn get_headers_path(&self) -> String {
        self.config.spv_headers_path.clone()
    }

    /// Get the number of headers we have
    fn get_headers_height(&self) -> Result<u64, burnchain_error> {
        let spv_client = SpvClient::new(
            &self.config.spv_headers_path,
            0,
            None,
            self.runtime.network_id,
            false,
            false,
        )
        .map_err(burnchain_error::Bitcoin)?;
        spv_client
            .get_headers_height()
            .map_err(burnchain_error::Bitcoin)
    }

    fn get_highest_header_height(&self) -> Result<u64, burnchain_error> {
        let spv_client = SpvClient::new(
            &self.config.spv_headers_path,
            0,
            None,
            self.runtime.network_id,
            false,
            false,
        )
        .map_err(burnchain_error::Bitcoin)?;
        spv_client
            .get_highest_header_height()
            .map_err(burnchain_error::Bitcoin)
    }

    /// Get the first block height
    fn get_first_block_height(&self) -> u64 {
        self.config.first_block
    }

    /// Get the first block header hash
    fn get_first_block_header_hash(&self) -> Result<BurnchainHeaderHash, burnchain_error> {
        let spv_client = SpvClient::new(
            &self.config.spv_headers_path,
            0,
            None,
            self.runtime.network_id,
            false,
            false,
        )?;
        let first_block_height = self.get_first_block_height();
        let first_header = spv_client
            .read_block_header(first_block_height)?
            .expect("BUG: no first block header hash");

        let first_block_header_hash =
            BurnchainHeaderHash::from_bitcoin_hash(&first_header.header.bitcoin_hash());
        Ok(first_block_header_hash)
    }

    /// Get the first block header timestamp
    fn get_first_block_header_timestamp(&self) -> Result<u64, burnchain_error> {
        let spv_client = SpvClient::new(
            &self.config.spv_headers_path,
            0,
            None,
            self.runtime.network_id,
            false,
            false,
        )?;
        let first_block_height = self.get_first_block_height();
        let first_header = spv_client
            .read_block_header(first_block_height)?
            .expect("BUG: no first block header timestamp");

        let first_block_header_timestamp = first_header.header.time as u64;
        Ok(first_block_header_timestamp)
    }

    /// Read downloaded headers within a range
    fn read_headers(
        &self,
        start_block: u64,
        end_block: u64,
    ) -> Result<Vec<BitcoinHeaderIPC>, burnchain_error> {
        let spv_client = SpvClient::new(
            &self.config.spv_headers_path,
            0,
            None,
            self.runtime.network_id,
            false,
            false,
        )?;

        let headers = spv_client.read_block_headers(start_block, end_block)?;
        let mut ret_headers: Vec<BitcoinHeaderIPC> = vec![];
        for i in 0..headers.len() {
            ret_headers.push({
                BitcoinHeaderIPC {
                    block_header: headers[i].clone(),
                    block_height: (i as u64) + start_block,
                }
            });
        }
        Ok(ret_headers)
    }

    /// Identify underlying reorgs and return the block height of the highest block in common
    /// between the remote node and our block headers.
    fn find_chain_reorg(&mut self) -> Result<u64, burnchain_error> {
        let headers_path = self.config.spv_headers_path.clone();
        let reorg_path = format!("{}.reorg", &self.config.spv_headers_path);
        self.find_bitcoin_reorg(
            &headers_path,
            &reorg_path,
            |ref mut indexer, ref mut spv_client, start_block, end_block_opt| {
                spv_client.set_scan_range(start_block, end_block_opt);
                spv_client.run(indexer)
            },
        )
        .map_err(|e| match e {
            btc_error::TimedOut => burnchain_error::TrySyncAgain,
            x => burnchain_error::Bitcoin(x),
        })
    }

    /// Download and store all headers between two block heights
    /// end_heights, if given, is inclusive.
    /// Returns the height of the last header fetched
    fn sync_headers(
        &mut self,
        start_height: u64,
        end_height: Option<u64>,
    ) -> Result<u64, burnchain_error> {
        if end_height.is_some() && end_height <= Some(start_height) {
            return Ok(end_height.unwrap());
        }

        self.sync_last_headers(start_height, end_height)
            .map_err(|e| match e {
                btc_error::TimedOut => burnchain_error::TrySyncAgain,
                x => burnchain_error::Bitcoin(x),
            })
    }

    /// Drop headers after a given height -- i.e. to accomodate a reorg
    fn drop_headers(&mut self, new_height: u64) -> Result<(), burnchain_error> {
        let mut spv_client = SpvClient::new(
            &self.config.spv_headers_path,
            0,
            None,
            self.runtime.network_id,
            true,
            false,
        )
        .map_err(burnchain_error::Bitcoin)?;
        spv_client
            .drop_headers(new_height)
            .map_err(burnchain_error::Bitcoin)
    }

    fn downloader(&self) -> BitcoinBlockDownloader {
        BitcoinBlockDownloader::new(self.dup())
    }

    fn parser(&self) -> BitcoinBlockParser {
        BitcoinBlockParser::new(self.runtime.network_id, self.config.magic_bytes)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use burnchains::bitcoin::Error as btc_error;
    use burnchains::bitcoin::*;
    use burnchains::Error as burnchain_error;
    use burnchains::*;

    use deps::bitcoin::blockdata::block::{BlockHeader, LoneBlockHeader};
    use deps::bitcoin::network::encodable::VarInt;
    use deps::bitcoin::network::serialize::{deserialize, serialize, BitcoinHash};
    use deps::bitcoin::util::hash::Sha256dHash;

    use std::env;

    #[test]
    fn test_indexer_find_bitcoin_reorg_genesis() {
        let path_1 = "/tmp/test-indexer-find_bitcoin_reorg_genesis.dat";
        let path_2 = "/tmp/test-indexer-find_bitcoin_reorg_genesis.dat.reorg.bak";
        let path_reorg = "/tmp/test-indexer-find_bitcoin_reorg_genesis.dat.reorg";

        if fs::metadata(path_1).is_ok() {
            fs::remove_file(path_1).unwrap();
        }
        if fs::metadata(path_2).is_ok() {
            fs::remove_file(path_2).unwrap();
        }

        // two header sets -- both of which build off of the genesis block
        let headers_1 = vec![
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "20bee96458517fc5082a9720ce6207b5742f2b18e4e0a7e7373342725d80f88c",
                    )
                    .unwrap(),
                    nonce: 2,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
                    )
                    .unwrap(),
                    time: 1587626881,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "39d1a6f1ee7a5903797f92ec89e4c58549013f38114186fc2eb6e5218cb2d0ac",
                    )
                    .unwrap(),
                    nonce: 1,
                    prev_blockhash: Sha256dHash::from_hex(
                        "606d31daaaa5919f3720d8440dd99d31f2a4e4189c65879f19ae43268425e74b",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "a7e04ed25f589938eb5627abb7b5913dd77b8955bcdf72d7f111d0a71e346e47",
                    )
                    .unwrap(),
                    nonce: 4,
                    prev_blockhash: Sha256dHash::from_hex(
                        "2fa2f451ac27f0e5cd3760ba6cdf34ef46adb76a44d96bc0f3bf3e713dd955f0",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
        ];

        let headers_2 = vec![
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "677351ef5cd586c8d0ee7c242e0c5794d0bb4564107e567fd24e508aa66c8b79",
                    )
                    .unwrap(),
                    nonce: 0,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
                    )
                    .unwrap(),
                    time: 1587612061,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "a92e6612c0cde9b029081d90b1dcef97f95508b92dd982223c8fcbe9e953fc79",
                    )
                    .unwrap(),
                    nonce: 0,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f4865e8169da0cb265ab0ea9eef440e6b7cc9bc1d5e74e4627c0f1e83e67e95",
                    )
                    .unwrap(),
                    time: 1587612062,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "5bd6f6f0863582bb6910d772829b7cf36be262b74ac5775ef9d78180c90a9fef",
                    )
                    .unwrap(),
                    nonce: 0,
                    prev_blockhash: Sha256dHash::from_hex(
                        "2dbbe38703af1918ef4091dfea226db8868843a55a4673e3d2d7259083b07063",
                    )
                    .unwrap(),
                    time: 1587612062,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
        ];

        let mut spv_client =
            SpvClient::new(path_1, 0, None, BitcoinNetworkType::Regtest, true, false).unwrap();
        let mut spv_client_reorg =
            SpvClient::new(path_2, 0, None, BitcoinNetworkType::Regtest, true, false).unwrap();

        spv_client
            .insert_block_headers_after(0, headers_1.clone())
            .unwrap();
        spv_client_reorg
            .insert_block_headers_after(0, headers_2.clone())
            .unwrap();

        assert_eq!(spv_client.read_block_headers(0, 10).unwrap().len(), 4);
        assert_eq!(spv_client_reorg.read_block_headers(0, 10).unwrap().len(), 4);

        assert_eq!(spv_client_reorg.read_block_headers(2, 10).unwrap().len(), 2);

        let mut indexer = BitcoinIndexer::new(
            BitcoinIndexerConfig::default_regtest(path_1.to_string()),
            BitcoinIndexerRuntime::new(BitcoinNetworkType::Regtest),
        );
        let common_ancestor_height = indexer
            .find_bitcoin_reorg(
                path_1,
                path_reorg,
                |ref mut indexer, ref mut spv_client, start_block, end_block_opt| {
                    // mock the bitcoind by just copying over the relevant headers from our backup reorg db
                    let end_block = end_block_opt.unwrap_or(10000000);
                    let hdrs = spv_client_reorg
                        .read_block_headers(start_block, end_block)
                        .unwrap();
                    if start_block > 0 {
                        spv_client
                            .insert_block_headers_before(start_block - 1, hdrs)
                            .unwrap();
                    } else if hdrs.len() > 0 {
                        spv_client
                            .insert_block_headers_before(0, hdrs[1..].to_vec())
                            .unwrap();
                    }

                    Ok(())
                },
            )
            .unwrap();

        // lowest common ancestor is the genesis block
        assert_eq!(common_ancestor_height, 0);
    }

    #[test]
    fn test_indexer_find_bitcoin_reorg_midpoint() {
        let path_1 = "/tmp/test-indexer-find_bitcoin_reorg_midpoint.dat";
        let path_2 = "/tmp/test-indexer-find_bitcoin_reorg_midpoint.dat.reorg.bak";
        let path_reorg = "/tmp/test-indexer-find_bitcoin_reorg_midpoint.dat.reorg";

        if fs::metadata(path_1).is_ok() {
            fs::remove_file(path_1).unwrap();
        }
        if fs::metadata(path_2).is_ok() {
            fs::remove_file(path_2).unwrap();
        }

        // two header sets -- both of which build off of the genesis block
        let headers_1 = vec![
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "677351ef5cd586c8d0ee7c242e0c5794d0bb4564107e567fd24e508aa66c8b79",
                    )
                    .unwrap(),
                    nonce: 0,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
                    )
                    .unwrap(),
                    time: 1587612061,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "39d1a6f1ee7a5903797f92ec89e4c58549013f38114186fc2eb6e5218cb2d0ac",
                    )
                    .unwrap(),
                    nonce: 1,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f4865e8169da0cb265ab0ea9eef440e6b7cc9bc1d5e74e4627c0f1e83e67e95",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "a7e04ed25f589938eb5627abb7b5913dd77b8955bcdf72d7f111d0a71e346e47",
                    )
                    .unwrap(),
                    nonce: 4,
                    prev_blockhash: Sha256dHash::from_hex(
                        "7a06268e099dafa4549d9e2511c251497779cf16ab3b5363e5b25d3dd6f552e7",
                    )
                    .unwrap(),
                    time: 1587626882,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
        ];

        let headers_2 = vec![
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "677351ef5cd586c8d0ee7c242e0c5794d0bb4564107e567fd24e508aa66c8b79",
                    )
                    .unwrap(),
                    nonce: 0,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f9188f13cb7b2c71f2a335e3a4fc328bf5beb436012afca590b1a11466e2206",
                    )
                    .unwrap(),
                    time: 1587612061,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "a92e6612c0cde9b029081d90b1dcef97f95508b92dd982223c8fcbe9e953fc79",
                    )
                    .unwrap(),
                    nonce: 0,
                    prev_blockhash: Sha256dHash::from_hex(
                        "0f4865e8169da0cb265ab0ea9eef440e6b7cc9bc1d5e74e4627c0f1e83e67e95",
                    )
                    .unwrap(),
                    time: 1587612062,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
            LoneBlockHeader {
                header: BlockHeader {
                    bits: 545259519,
                    merkle_root: Sha256dHash::from_hex(
                        "5bd6f6f0863582bb6910d772829b7cf36be262b74ac5775ef9d78180c90a9fef",
                    )
                    .unwrap(),
                    nonce: 0,
                    prev_blockhash: Sha256dHash::from_hex(
                        "2dbbe38703af1918ef4091dfea226db8868843a55a4673e3d2d7259083b07063",
                    )
                    .unwrap(),
                    time: 1587612062,
                    version: 0x20000000,
                },
                tx_count: VarInt(0),
            },
        ];

        let mut spv_client =
            SpvClient::new(path_1, 0, None, BitcoinNetworkType::Regtest, true, false).unwrap();
        let mut spv_client_reorg =
            SpvClient::new(path_2, 0, None, BitcoinNetworkType::Regtest, true, false).unwrap();

        spv_client
            .insert_block_headers_after(0, headers_1.clone())
            .unwrap();
        spv_client_reorg
            .insert_block_headers_after(0, headers_2.clone())
            .unwrap();

        assert_eq!(spv_client.read_block_headers(0, 10).unwrap().len(), 4);
        assert_eq!(spv_client_reorg.read_block_headers(0, 10).unwrap().len(), 4);

        assert_eq!(spv_client_reorg.read_block_headers(2, 10).unwrap().len(), 2);

        let mut indexer = BitcoinIndexer::new(
            BitcoinIndexerConfig::default_regtest(path_1.to_string()),
            BitcoinIndexerRuntime::new(BitcoinNetworkType::Regtest),
        );
        let common_ancestor_height = indexer
            .find_bitcoin_reorg(
                path_1,
                path_reorg,
                |ref mut indexer, ref mut spv_client, start_block, end_block_opt| {
                    // mock the bitcoind by just copying over the relevant headers from our backup reorg db
                    let end_block = end_block_opt.unwrap_or(10000000);
                    let hdrs = spv_client_reorg
                        .read_block_headers(start_block, end_block)
                        .unwrap();
                    if start_block > 0 {
                        spv_client
                            .insert_block_headers_before(start_block - 1, hdrs)
                            .unwrap();
                    } else if hdrs.len() > 0 {
                        spv_client
                            .insert_block_headers_before(0, hdrs[1..].to_vec())
                            .unwrap();
                    }

                    Ok(())
                },
            )
            .unwrap();

        // lowest common ancestor is the first block
        assert_eq!(common_ancestor_height, 1);
    }

    #[test]
    fn test_indexer_sync_headers() {
        if !env::var("BLOCKSTACK_SPV_BITCOIN_HOST").is_ok() {
            eprintln!(
                "Skipping test_indexer_sync_headers -- no BLOCKSTACK_SPV_BITCOIN_HOST envar set"
            );
            return;
        }
        if !env::var("BLOCKSTACK_SPV_BITCOIN_PORT").is_ok() {
            eprintln!(
                "Skipping test_indexer_sync_headers -- no BLOCKSTACK_SPV_BITCOIN_PORT envar set"
            );
            return;
        }
        if !env::var("BLOCKSTACK_SPV_BITCOIN_MODE").is_ok() {
            eprintln!(
                "Skipping test_indexer_sync_headers -- no BLOCKSTACK_SPV_BITCOIN_MODE envar set"
            );
            return;
        }

        let host = env::var("BLOCKSTACK_SPV_BITCOIN_HOST").unwrap();
        let port = env::var("BLOCKSTACK_SPV_BITCOIN_PORT")
            .unwrap()
            .parse::<u16>()
            .unwrap();
        let mode = match env::var("BLOCKSTACK_SPV_BITCOIN_MODE").unwrap().as_str() {
            "mainnet" => BitcoinNetworkType::Mainnet,
            "testnet" => BitcoinNetworkType::Testnet,
            "regtest" => BitcoinNetworkType::Regtest,
            _ => {
                panic!("Invalid bitcoin mode -- expected mainnet, testnet, or regtest");
            }
        };

        let indexer_conf = BitcoinIndexerConfig {
            peer_host: host,
            peer_port: port,
            rpc_port: port + 1, // ignored
            rpc_ssl: false,
            username: None,
            password: None,
            timeout: 30,
            spv_headers_path: "/tmp/test_indexer_sync_headers.sqlite".to_string(),
            first_block: 0,
            magic_bytes: MagicBytes([105, 100]),
        };

        if fs::metadata(&indexer_conf.spv_headers_path).is_ok() {
            fs::remove_file(&indexer_conf.spv_headers_path).unwrap();
        }

        let mut indexer = BitcoinIndexer::new(indexer_conf, BitcoinIndexerRuntime::new(mode));
        let last_block = indexer.sync_headers(0, None).unwrap();
        eprintln!("sync'ed to block {}", last_block);
    }
}
