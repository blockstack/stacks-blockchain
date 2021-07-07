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

use std::collections::HashMap;
use std::convert::TryFrom;
use std::default::Default;
use std::error;
use std::fmt;
use std::io;
use std::marker::PhantomData;

use rusqlite::Error as sqlite_error;

use address::AddressHashMode;
use chainstate::burn::distribution::BurnSamplePoint;
use chainstate::burn::operations::leader_block_commit::OUTPUTS_PER_COMMIT;
use chainstate::burn::operations::BlockstackOperationType;
use chainstate::burn::operations::Error as op_error;
use chainstate::burn::operations::LeaderKeyRegisterOp;
use chainstate::burn::ConsensusHash;
use chainstate::stacks::StacksPublicKey;
use core::*;
use net::neighbors::MAX_NEIGHBOR_BLOCK_DELAY;
use util::db::Error as db_error;
use util::hash::Hash160;
use util::secp256k1::MessageSignature;

use crate::types::chainstate::BurnchainHeaderHash;
use crate::types::chainstate::PoxId;
use crate::types::chainstate::StacksAddress;
use crate::types::proof::TrieHash;

use self::bitcoin::indexer::{
    BITCOIN_MAINNET as BITCOIN_NETWORK_ID_MAINNET, BITCOIN_MAINNET_NAME,
    BITCOIN_REGTEST as BITCOIN_NETWORK_ID_REGTEST, BITCOIN_REGTEST_NAME,
    BITCOIN_TESTNET as BITCOIN_NETWORK_ID_TESTNET, BITCOIN_TESTNET_NAME,
};
use self::bitcoin::Error as btc_error;
use self::bitcoin::{
    BitcoinBlock, BitcoinInputType, BitcoinTransaction, BitcoinTxInput, BitcoinTxOutput,
};

/// This module contains drivers and types for all burn chains we support.
pub mod bitcoin;
pub mod burnchain;
pub mod db;
pub mod indexer;

#[derive(Serialize, Deserialize)]
pub struct Txid(pub [u8; 32]);
impl_array_newtype!(Txid, u8, 32);
impl_array_hexstring_fmt!(Txid);
impl_byte_array_newtype!(Txid, u8, 32);
pub const TXID_ENCODED_SIZE: u32 = 32;

pub const MAGIC_BYTES_LENGTH: usize = 2;

#[derive(Debug, Serialize, Deserialize, Default)]
pub struct MagicBytes([u8; MAGIC_BYTES_LENGTH]);
impl_array_newtype!(MagicBytes, u8, MAGIC_BYTES_LENGTH);
impl MagicBytes {
    pub fn default() -> MagicBytes {
        BLOCKSTACK_MAGIC_MAINNET
    }
}

pub const BLOCKSTACK_MAGIC_MAINNET: MagicBytes = MagicBytes([105, 100]); // 'id'

#[derive(Debug, PartialEq, Clone)]
pub struct BurnchainParameters {
    chain_name: String,
    network_name: String,
    network_id: u32,
    stable_confirmations: u32,
    consensus_hash_lifetime: u32,
    pub first_block_height: u64,
    pub first_block_hash: BurnchainHeaderHash,
    pub first_block_timestamp: u32,
    pub initial_reward_start_block: u64,
}

impl BurnchainParameters {
    pub fn from_params(chain: &str, network: &str) -> Option<BurnchainParameters> {
        match (chain, network) {
            ("bitcoin", "mainnet") => Some(BurnchainParameters::bitcoin_mainnet()),
            ("bitcoin", "testnet") => Some(BurnchainParameters::bitcoin_testnet()),
            ("bitcoin", "regtest") => Some(BurnchainParameters::bitcoin_regtest()),
            _ => None,
        }
    }

    pub fn bitcoin_mainnet() -> BurnchainParameters {
        BurnchainParameters {
            chain_name: "bitcoin".to_string(),
            network_name: BITCOIN_MAINNET_NAME.to_string(),
            network_id: BITCOIN_NETWORK_ID_MAINNET,
            stable_confirmations: 7,
            consensus_hash_lifetime: 24,
            first_block_height: BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT,
            first_block_hash: BurnchainHeaderHash::from_hex(BITCOIN_MAINNET_FIRST_BLOCK_HASH)
                .unwrap(),
            first_block_timestamp: BITCOIN_MAINNET_FIRST_BLOCK_TIMESTAMP,
            initial_reward_start_block: BITCOIN_MAINNET_INITIAL_REWARD_START_BLOCK,
        }
    }

    pub fn bitcoin_testnet() -> BurnchainParameters {
        BurnchainParameters {
            chain_name: "bitcoin".to_string(),
            network_name: BITCOIN_TESTNET_NAME.to_string(),
            network_id: BITCOIN_NETWORK_ID_TESTNET,
            stable_confirmations: 7,
            consensus_hash_lifetime: 24,
            first_block_height: BITCOIN_TESTNET_FIRST_BLOCK_HEIGHT,
            first_block_hash: BurnchainHeaderHash::from_hex(BITCOIN_TESTNET_FIRST_BLOCK_HASH)
                .unwrap(),
            first_block_timestamp: BITCOIN_TESTNET_FIRST_BLOCK_TIMESTAMP,
            initial_reward_start_block: BITCOIN_TESTNET_FIRST_BLOCK_HEIGHT - 10_000,
        }
    }

    pub fn bitcoin_regtest() -> BurnchainParameters {
        BurnchainParameters {
            chain_name: "bitcoin".to_string(),
            network_name: BITCOIN_REGTEST_NAME.to_string(),
            network_id: BITCOIN_NETWORK_ID_REGTEST,
            stable_confirmations: 1,
            consensus_hash_lifetime: 24,
            first_block_height: BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT,
            first_block_hash: BurnchainHeaderHash::from_hex(BITCOIN_REGTEST_FIRST_BLOCK_HASH)
                .unwrap(),
            first_block_timestamp: BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP,
            initial_reward_start_block: BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT,
        }
    }

    pub fn is_testnet(network_id: u32) -> bool {
        match network_id {
            BITCOIN_NETWORK_ID_TESTNET | BITCOIN_NETWORK_ID_REGTEST => true,
            _ => false,
        }
    }
}

pub trait PublicKey: Clone + fmt::Debug + serde::Serialize + serde::de::DeserializeOwned {
    fn to_bytes(&self) -> Vec<u8>;
    fn verify(&self, data_hash: &[u8], sig: &MessageSignature) -> Result<bool, &'static str>;
}

pub trait PrivateKey: Clone + fmt::Debug + serde::Serialize + serde::de::DeserializeOwned {
    fn to_bytes(&self) -> Vec<u8>;
    fn sign(&self, data_hash: &[u8]) -> Result<MessageSignature, &'static str>;
}

pub trait Address: Clone + fmt::Debug + fmt::Display {
    fn to_bytes(&self) -> Vec<u8>;
    fn from_string(from: &str) -> Option<Self>
    where
        Self: Sized;
    fn is_burn(&self) -> bool;
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct BurnchainSigner {
    pub hash_mode: AddressHashMode,
    pub num_sigs: usize,
    pub public_keys: Vec<StacksPublicKey>,
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct BurnchainRecipient {
    pub address: StacksAddress,
    pub amount: u64,
}

#[derive(Debug, PartialEq, Clone)]
pub enum BurnchainTransaction {
    Bitcoin(BitcoinTransaction),
    // TODO: fill in more types as we support them
}

impl BurnchainTransaction {
    pub fn txid(&self) -> Txid {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc.txid.clone(),
        }
    }

    pub fn vtxindex(&self) -> u32 {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc.vtxindex,
        }
    }

    pub fn opcode(&self) -> u8 {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc.opcode,
        }
    }

    pub fn data(&self) -> Vec<u8> {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc.data.clone(),
        }
    }

    pub fn num_signers(&self) -> usize {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc.inputs.len(),
        }
    }

    pub fn get_signers(&self) -> Vec<BurnchainSigner> {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc
                .inputs
                .iter()
                .map(|ref i| BurnchainSigner::from_bitcoin_input(i))
                .collect(),
        }
    }

    pub fn get_signer(&self, input: usize) -> Option<BurnchainSigner> {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc
                .inputs
                .get(input)
                .map(|ref i| BurnchainSigner::from_bitcoin_input(i)),
        }
    }

    pub fn get_input_tx_ref(&self, input: usize) -> Option<&(Txid, u32)> {
        match self {
            BurnchainTransaction::Bitcoin(ref btc) => {
                btc.inputs.get(input).map(|txin| &txin.tx_ref)
            }
        }
    }

    pub fn get_recipients(&self) -> Vec<BurnchainRecipient> {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc
                .outputs
                .iter()
                .map(|ref o| BurnchainRecipient::from_bitcoin_output(o))
                .collect(),
        }
    }

    pub fn get_burn_amount(&self) -> u64 {
        match *self {
            BurnchainTransaction::Bitcoin(ref btc) => btc.data_amt,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BurnchainBlock {
    Bitcoin(BitcoinBlock),
    // TODO: fill in some more types as we support them
}

#[derive(Debug, PartialEq, Clone)]
pub struct BurnchainBlockHeader {
    pub block_height: u64,
    pub block_hash: BurnchainHeaderHash,
    pub parent_block_hash: BurnchainHeaderHash,
    pub num_txs: u64,
    pub timestamp: u64,
}

#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub struct Burnchain {
    pub peer_version: u32,
    pub network_id: u32,
    pub chain_name: String,
    pub network_name: String,
    pub working_dir: String,
    pub consensus_hash_lifetime: u32,
    pub stable_confirmations: u32,
    pub first_block_height: u64,
    pub first_block_hash: BurnchainHeaderHash,
    pub first_block_timestamp: u32,
    pub pox_constants: PoxConstants,
    pub initial_reward_start_block: u64,
}

#[derive(Debug, PartialEq, Clone, Serialize, Deserialize)]
pub struct PoxConstants {
    /// the length (in burn blocks) of the reward cycle
    pub reward_cycle_length: u32,
    /// the length (in burn blocks) of the prepare phase
    pub prepare_length: u32,
    /// the number of confirmations a PoX anchor block must
    ///  receive in order to become the anchor. must be at least > prepare_length/2
    pub anchor_threshold: u32,
    /// fraction of liquid STX that must vote to reject PoX for
    /// it to revert to PoB in the next reward cycle
    pub pox_rejection_fraction: u64,
    /// percentage of liquid STX that must participate for PoX
    ///  to occur
    pub pox_participation_threshold_pct: u64,
    /// last+1 block height of sunset phase
    pub sunset_end: u64,
    /// first block height of sunset phase
    pub sunset_start: u64,
    _shadow: PhantomData<()>,
}

impl PoxConstants {
    pub fn new(
        reward_cycle_length: u32,
        prepare_length: u32,
        anchor_threshold: u32,
        pox_rejection_fraction: u64,
        pox_participation_threshold_pct: u64,
        sunset_start: u64,
        sunset_end: u64,
    ) -> PoxConstants {
        assert!(anchor_threshold > (prepare_length / 2));
        assert!(prepare_length < reward_cycle_length);
        assert!(sunset_start <= sunset_end);

        PoxConstants {
            reward_cycle_length,
            prepare_length,
            anchor_threshold,
            pox_rejection_fraction,
            pox_participation_threshold_pct,
            sunset_start,
            sunset_end,
            _shadow: PhantomData,
        }
    }
    #[cfg(test)]
    pub fn test_default() -> PoxConstants {
        // 20 reward slots; 10 prepare-phase slots
        PoxConstants::new(10, 5, 3, 25, 5, 5000, 10000)
    }

    pub fn reward_slots(&self) -> u32 {
        (self.reward_cycle_length - self.prepare_length) * (OUTPUTS_PER_COMMIT as u32)
    }

    /// is participating_ustx enough to engage in PoX in the next reward cycle?
    pub fn enough_participation(&self, participating_ustx: u128, liquid_ustx: u128) -> bool {
        participating_ustx
            .checked_mul(100)
            .expect("OVERFLOW: uSTX overflowed u128")
            > liquid_ustx
                .checked_mul(self.pox_participation_threshold_pct as u128)
                .expect("OVERFLOW: uSTX overflowed u128")
    }

    pub fn mainnet_default() -> PoxConstants {
        PoxConstants::new(
            POX_REWARD_CYCLE_LENGTH,
            POX_PREPARE_WINDOW_LENGTH,
            80,
            25,
            5,
            BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT + POX_SUNSET_START,
            BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT + POX_SUNSET_END,
        )
    }

    pub fn testnet_default() -> PoxConstants {
        PoxConstants::new(
            POX_REWARD_CYCLE_LENGTH / 2,   // 1050
            POX_PREPARE_WINDOW_LENGTH / 2, // 50
            40,
            12,
            2,
            BITCOIN_TESTNET_FIRST_BLOCK_HEIGHT + POX_SUNSET_START,
            BITCOIN_TESTNET_FIRST_BLOCK_HEIGHT + POX_SUNSET_END,
        ) // total liquid supply is 40000000000000000 µSTX
    }

    pub fn regtest_default() -> PoxConstants {
        PoxConstants::new(
            5,
            1,
            1,
            3333333333333333,
            1,
            BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT + POX_SUNSET_START,
            BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT + POX_SUNSET_END,
        )
    }
}

/// Structure for encoding our view of the network
#[derive(Debug, PartialEq, Clone)]
pub struct BurnchainView {
    pub burn_block_height: u64, // last-seen block height (at chain tip)
    pub burn_block_hash: BurnchainHeaderHash, // last-seen burn block hash
    pub burn_stable_block_height: u64, // latest stable block height (e.g. chain tip minus 7)
    pub burn_stable_block_hash: BurnchainHeaderHash, // latest stable burn block hash
    pub last_burn_block_hashes: HashMap<u64, BurnchainHeaderHash>, // map all block heights from burn_block_height back to the oldest one we'll take for considering the peer a neighbor
}

/// The burnchain block's encoded state transition:
/// -- the new burn distribution
/// -- the sequence of valid blockstack operations that went into it
/// -- the set of previously-accepted leader VRF keys consumed
#[derive(Debug, Clone)]
pub struct BurnchainStateTransition {
    pub burn_dist: Vec<BurnSamplePoint>,
    pub accepted_ops: Vec<BlockstackOperationType>,
    pub consumed_leader_keys: Vec<LeaderKeyRegisterOp>,
}

/// The burnchain block's state transition's ops:
/// -- the new burn distribution
/// -- the sequence of valid blockstack operations that went into it
/// -- the set of previously-accepted leader VRF keys consumed
#[derive(Debug, Clone)]
pub struct BurnchainStateTransitionOps {
    pub accepted_ops: Vec<BlockstackOperationType>,
    pub consumed_leader_keys: Vec<LeaderKeyRegisterOp>,
}

#[derive(Debug)]
pub enum Error {
    /// Unsupported burn chain
    UnsupportedBurnchain,
    /// Bitcoin-related error
    Bitcoin(btc_error),
    /// burn database error
    DBError(db_error),
    /// Download error
    DownloadError(btc_error),
    /// Parse error
    ParseError,
    /// Thread channel error
    ThreadChannelError,
    /// Missing headers
    MissingHeaders,
    /// Missing parent block
    MissingParentBlock,
    /// Remote burnchain peer has misbehaved
    BurnchainPeerBroken,
    /// filesystem error
    FSError(io::Error),
    /// Operation processing error
    OpError(op_error),
    /// Try again error
    TrySyncAgain,
    UnknownBlock(BurnchainHeaderHash),
    NonCanonicalPoxId(PoxId, PoxId),
    CoordinatorClosed,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::UnsupportedBurnchain => write!(f, "Unsupported burnchain"),
            Error::Bitcoin(ref btce) => fmt::Display::fmt(btce, f),
            Error::DBError(ref dbe) => fmt::Display::fmt(dbe, f),
            Error::DownloadError(ref btce) => fmt::Display::fmt(btce, f),
            Error::ParseError => write!(f, "Parse error"),
            Error::MissingHeaders => write!(f, "Missing block headers"),
            Error::MissingParentBlock => write!(f, "Missing parent block"),
            Error::ThreadChannelError => write!(f, "Error in thread channel"),
            Error::BurnchainPeerBroken => write!(f, "Remote burnchain peer has misbehaved"),
            Error::FSError(ref e) => fmt::Display::fmt(e, f),
            Error::OpError(ref e) => fmt::Display::fmt(e, f),
            Error::TrySyncAgain => write!(f, "Try synchronizing again"),
            Error::UnknownBlock(block) => write!(f, "Unknown burnchain block {}", block),
            Error::NonCanonicalPoxId(parent, child) => write!(
                f,
                "{} is not a descendant of the canonical parent PoXId: {}",
                parent, child
            ),
            Error::CoordinatorClosed => write!(f, "ChainsCoordinator channel hung up"),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Error::UnsupportedBurnchain => None,
            Error::Bitcoin(ref e) => Some(e),
            Error::DBError(ref e) => Some(e),
            Error::DownloadError(ref e) => Some(e),
            Error::ParseError => None,
            Error::MissingHeaders => None,
            Error::MissingParentBlock => None,
            Error::ThreadChannelError => None,
            Error::BurnchainPeerBroken => None,
            Error::FSError(ref e) => Some(e),
            Error::OpError(ref e) => Some(e),
            Error::TrySyncAgain => None,
            Error::UnknownBlock(_) => None,
            Error::NonCanonicalPoxId(_, _) => None,
            Error::CoordinatorClosed => None,
        }
    }
}

impl From<db_error> for Error {
    fn from(e: db_error) -> Error {
        Error::DBError(e)
    }
}

impl From<sqlite_error> for Error {
    fn from(e: sqlite_error) -> Error {
        Error::DBError(db_error::SqliteError(e))
    }
}

impl From<btc_error> for Error {
    fn from(e: btc_error) -> Error {
        Error::Bitcoin(e)
    }
}

impl BurnchainView {
    #[cfg(test)]
    pub fn make_test_data(&mut self) {
        let oldest_height = if self.burn_stable_block_height < MAX_NEIGHBOR_BLOCK_DELAY {
            0
        } else {
            self.burn_stable_block_height - MAX_NEIGHBOR_BLOCK_DELAY
        };

        let mut ret = HashMap::new();
        for i in oldest_height..self.burn_block_height + 1 {
            if i == self.burn_stable_block_height {
                ret.insert(i, self.burn_stable_block_hash.clone());
            } else if i == self.burn_block_height {
                ret.insert(i, self.burn_block_hash.clone());
            } else {
                let data = {
                    use sha2::Digest;
                    use sha2::Sha256;
                    let mut hasher = Sha256::new();
                    hasher.input(&i.to_le_bytes());
                    hasher.result()
                };
                let mut data_32 = [0x00; 32];
                data_32.copy_from_slice(&data[0..32]);
                ret.insert(i, BurnchainHeaderHash(data_32));
            }
        }
        self.last_burn_block_hashes = ret;
    }
}

#[cfg(test)]
pub mod test {
    use std::collections::HashMap;

    use address::*;
    use burnchains::db::*;
    use burnchains::Burnchain;
    use burnchains::*;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::operations::BlockstackOperationType;
    use chainstate::burn::operations::*;
    use chainstate::burn::*;
    use chainstate::coordinator::comm::*;
    use chainstate::coordinator::*;
    use chainstate::stacks::*;
    use util::db::*;
    use util::get_epoch_time_secs;
    use util::hash::*;
    use util::secp256k1::*;
    use util::vrf::*;

    use crate::types::chainstate::{BlockHeaderHash, SortitionId, VRFSeed};

    use super::*;

    impl Txid {
        pub fn from_test_data(
            block_height: u64,
            vtxindex: u32,
            burn_header_hash: &BurnchainHeaderHash,
            noise: u64,
        ) -> Txid {
            let mut bytes = vec![];
            bytes.extend_from_slice(&block_height.to_be_bytes());
            bytes.extend_from_slice(&vtxindex.to_be_bytes());
            bytes.extend_from_slice(burn_header_hash.as_bytes());
            bytes.extend_from_slice(&noise.to_be_bytes());
            let h = DoubleSha256::from_data(&bytes[..]);
            let mut hb = [0u8; 32];
            hb.copy_from_slice(h.as_bytes());

            Txid(hb)
        }
    }

    impl BurnchainHeaderHash {
        pub fn from_test_data(
            block_height: u64,
            index_root: &TrieHash,
            noise: u64,
        ) -> BurnchainHeaderHash {
            let mut bytes = vec![];
            bytes.extend_from_slice(&block_height.to_be_bytes());
            bytes.extend_from_slice(index_root.as_bytes());
            bytes.extend_from_slice(&noise.to_be_bytes());
            let h = DoubleSha256::from_data(&bytes[..]);
            let mut hb = [0u8; 32];
            hb.copy_from_slice(h.as_bytes());

            BurnchainHeaderHash(hb)
        }
    }

    impl BurnchainBlockHeader {
        pub fn from_parent_snapshot(
            parent_sn: &BlockSnapshot,
            block_hash: BurnchainHeaderHash,
            num_txs: u64,
        ) -> BurnchainBlockHeader {
            BurnchainBlockHeader {
                block_height: parent_sn.block_height + 1,
                block_hash: block_hash,
                parent_block_hash: parent_sn.burn_header_hash.clone(),
                num_txs: num_txs,
                timestamp: get_epoch_time_secs(),
            }
        }
    }

    #[derive(Debug, Clone)]
    pub struct TestBurnchainBlock {
        pub block_height: u64,
        pub parent_snapshot: BlockSnapshot,
        pub txs: Vec<BlockstackOperationType>,
        pub fork_id: u64,
        pub timestamp: u64,
    }

    #[derive(Debug, Clone)]
    pub struct TestBurnchainFork {
        pub start_height: u64,
        pub mined: u64,
        pub tip_index_root: TrieHash,
        pub tip_header_hash: BurnchainHeaderHash,
        pub tip_sortition_id: SortitionId,
        pub pending_blocks: Vec<TestBurnchainBlock>,
        pub blocks: Vec<TestBurnchainBlock>,
        pub fork_id: u64,
    }

    pub struct TestBurnchainNode {
        pub sortdb: SortitionDB,
        pub dirty: bool,
        pub burnchain: Burnchain,
    }

    #[derive(Debug, Clone)]
    pub struct TestMiner {
        pub burnchain: Burnchain,
        pub privks: Vec<StacksPrivateKey>,
        pub num_sigs: u16,
        pub hash_mode: AddressHashMode,
        pub microblock_privks: Vec<StacksPrivateKey>,
        pub vrf_keys: Vec<VRFPrivateKey>,
        pub vrf_key_map: HashMap<VRFPublicKey, VRFPrivateKey>,
        pub block_commits: Vec<LeaderBlockCommitOp>,
        pub id: usize,
        pub nonce: u64,
        pub spent_at_nonce: HashMap<u64, u128>, // how much uSTX this miner paid in a given tx's nonce
        pub test_with_tx_fees: bool, // set to true to make certain helper methods attach a pre-defined tx fee
    }

    pub struct TestMinerFactory {
        pub key_seed: [u8; 32],
        pub next_miner_id: usize,
    }

    impl TestMiner {
        pub fn new(
            burnchain: &Burnchain,
            privks: &Vec<StacksPrivateKey>,
            num_sigs: u16,
            hash_mode: &AddressHashMode,
        ) -> TestMiner {
            TestMiner {
                burnchain: burnchain.clone(),
                privks: privks.clone(),
                num_sigs,
                hash_mode: hash_mode.clone(),
                microblock_privks: vec![],
                vrf_keys: vec![],
                vrf_key_map: HashMap::new(),
                block_commits: vec![],
                id: 0,
                nonce: 0,
                spent_at_nonce: HashMap::new(),
                test_with_tx_fees: true,
            }
        }

        pub fn last_VRF_public_key(&self) -> Option<VRFPublicKey> {
            match self.vrf_keys.len() {
                0 => None,
                x => Some(VRFPublicKey::from_private(&self.vrf_keys[x - 1])),
            }
        }

        pub fn last_block_commit(&self) -> Option<LeaderBlockCommitOp> {
            match self.block_commits.len() {
                0 => None,
                x => Some(self.block_commits[x - 1].clone()),
            }
        }

        pub fn next_VRF_key(&mut self) -> VRFPrivateKey {
            let pk = if self.vrf_keys.len() == 0 {
                // first key is simply the 32-byte hash of the secret state
                let mut buf: Vec<u8> = vec![];
                for i in 0..self.privks.len() {
                    buf.extend_from_slice(&self.privks[i].to_bytes()[..]);
                }
                buf.extend_from_slice(&[
                    (self.num_sigs >> 8) as u8,
                    (self.num_sigs & 0xff) as u8,
                    self.hash_mode as u8,
                ]);
                let h = Sha256Sum::from_data(&buf[..]);
                VRFPrivateKey::from_bytes(h.as_bytes()).unwrap()
            } else {
                // next key is just the hash of the last
                let h = Sha256Sum::from_data(self.vrf_keys[self.vrf_keys.len() - 1].as_bytes());
                VRFPrivateKey::from_bytes(h.as_bytes()).unwrap()
            };

            self.vrf_keys.push(pk.clone());
            self.vrf_key_map
                .insert(VRFPublicKey::from_private(&pk), pk.clone());
            pk
        }

        pub fn next_microblock_privkey(&mut self) -> StacksPrivateKey {
            let pk = if self.microblock_privks.len() == 0 {
                // first key is simply the 32-byte hash of the secret state
                let mut buf: Vec<u8> = vec![];
                for i in 0..self.privks.len() {
                    buf.extend_from_slice(&self.privks[i].to_bytes()[..]);
                }
                buf.extend_from_slice(&[
                    (self.num_sigs >> 8) as u8,
                    (self.num_sigs & 0xff) as u8,
                    self.hash_mode as u8,
                ]);
                let h = Sha256Sum::from_data(&buf[..]);
                StacksPrivateKey::from_slice(h.as_bytes()).unwrap()
            } else {
                // next key is the hash of the last
                let h = Sha256Sum::from_data(
                    &self.microblock_privks[self.microblock_privks.len() - 1].to_bytes(),
                );
                StacksPrivateKey::from_slice(h.as_bytes()).unwrap()
            };

            self.microblock_privks.push(pk.clone());
            pk
        }

        pub fn make_proof(
            &self,
            vrf_pubkey: &VRFPublicKey,
            last_sortition_hash: &SortitionHash,
        ) -> Option<VRFProof> {
            test_debug!(
                "Make proof from {} over {}",
                vrf_pubkey.to_hex(),
                last_sortition_hash
            );
            match self.vrf_key_map.get(vrf_pubkey) {
                Some(ref prover_key) => {
                    let proof = VRF::prove(prover_key, &last_sortition_hash.as_bytes().to_vec());
                    let valid = match VRF::verify(
                        vrf_pubkey,
                        &proof,
                        &last_sortition_hash.as_bytes().to_vec(),
                    ) {
                        Ok(v) => v,
                        Err(e) => false,
                    };
                    assert!(valid);
                    Some(proof)
                }
                None => None,
            }
        }

        pub fn as_transaction_auth(&self) -> Option<TransactionAuth> {
            match self.hash_mode {
                AddressHashMode::SerializeP2PKH => TransactionAuth::from_p2pkh(&self.privks[0]),
                AddressHashMode::SerializeP2SH => {
                    TransactionAuth::from_p2sh(&self.privks, self.num_sigs)
                }
                AddressHashMode::SerializeP2WPKH => TransactionAuth::from_p2wpkh(&self.privks[0]),
                AddressHashMode::SerializeP2WSH => {
                    TransactionAuth::from_p2wsh(&self.privks, self.num_sigs)
                }
            }
        }

        pub fn origin_address(&self) -> Option<StacksAddress> {
            match self.as_transaction_auth() {
                Some(auth) => Some(auth.origin().address_testnet()),
                None => None,
            }
        }

        pub fn get_nonce(&self) -> u64 {
            self.nonce
        }

        pub fn set_nonce(&mut self, n: u64) -> () {
            self.nonce = n;
        }

        pub fn sign_as_origin(&mut self, tx_signer: &mut StacksTransactionSigner) -> () {
            let num_keys = if self.privks.len() < self.num_sigs as usize {
                self.privks.len()
            } else {
                self.num_sigs as usize
            };

            for i in 0..num_keys {
                tx_signer.sign_origin(&self.privks[i]).unwrap();
            }

            self.nonce += 1
        }

        pub fn sign_as_sponsor(&mut self, tx_signer: &mut StacksTransactionSigner) -> () {
            let num_keys = if self.privks.len() < self.num_sigs as usize {
                self.privks.len()
            } else {
                self.num_sigs as usize
            };

            for i in 0..num_keys {
                tx_signer.sign_sponsor(&self.privks[i]).unwrap();
            }

            self.nonce += 1
        }
    }

    // creates miners deterministically
    impl TestMinerFactory {
        pub fn new() -> TestMinerFactory {
            TestMinerFactory {
                key_seed: [0u8; 32],
                next_miner_id: 1,
            }
        }

        pub fn from_u16(seed: u16) -> TestMinerFactory {
            let mut bytes = [0u8; 32];
            (&mut bytes[0..2]).copy_from_slice(&seed.to_be_bytes());
            TestMinerFactory {
                key_seed: bytes,
                next_miner_id: seed as usize,
            }
        }

        pub fn next_private_key(&mut self) -> StacksPrivateKey {
            let h = Sha256Sum::from_data(&self.key_seed);
            self.key_seed.copy_from_slice(h.as_bytes());

            StacksPrivateKey::from_slice(h.as_bytes()).unwrap()
        }

        pub fn next_miner(
            &mut self,
            burnchain: &Burnchain,
            num_keys: u16,
            num_sigs: u16,
            hash_mode: AddressHashMode,
        ) -> TestMiner {
            let mut keys = vec![];
            for i in 0..num_keys {
                keys.push(self.next_private_key());
            }

            test_debug!("New miner: {:?} {}:{:?}", &hash_mode, num_sigs, &keys);
            let mut m = TestMiner::new(burnchain, &keys, num_sigs, &hash_mode);
            m.id = self.next_miner_id;
            self.next_miner_id += 1;
            m
        }
    }

    impl TestBurnchainBlock {
        pub fn new(parent_snapshot: &BlockSnapshot, fork_id: u64) -> TestBurnchainBlock {
            TestBurnchainBlock {
                parent_snapshot: parent_snapshot.clone(),
                block_height: parent_snapshot.block_height + 1,
                txs: vec![],
                fork_id: fork_id,
                timestamp: get_epoch_time_secs(),
            }
        }

        pub fn add_leader_key_register(&mut self, miner: &mut TestMiner) -> LeaderKeyRegisterOp {
            let next_vrf_key = miner.next_VRF_key();
            let mut txop = LeaderKeyRegisterOp::new_from_secrets(
                &miner.privks,
                miner.num_sigs,
                &miner.hash_mode,
                &next_vrf_key,
            )
            .unwrap();

            txop.vtxindex = self.txs.len() as u32;
            txop.block_height = self.block_height;
            txop.burn_header_hash = BurnchainHeaderHash::from_test_data(
                txop.block_height,
                &self.parent_snapshot.index_root,
                self.fork_id,
            );
            txop.txid =
                Txid::from_test_data(txop.block_height, txop.vtxindex, &txop.burn_header_hash, 0);
            txop.consensus_hash = self.parent_snapshot.consensus_hash.clone();

            self.txs
                .push(BlockstackOperationType::LeaderKeyRegister(txop.clone()));

            txop
        }

        pub fn add_leader_block_commit(
            &mut self,
            ic: &SortitionDBConn,
            miner: &mut TestMiner,
            block_hash: &BlockHeaderHash,
            burn_fee: u64,
            leader_key: &LeaderKeyRegisterOp,
            fork_snapshot: Option<&BlockSnapshot>,
            parent_block_snapshot: Option<&BlockSnapshot>,
        ) -> LeaderBlockCommitOp {
            let input = (Txid([0; 32]), 0);
            let pubks = miner
                .privks
                .iter()
                .map(|ref pk| StacksPublicKey::from_private(pk))
                .collect();
            let apparent_sender = BurnchainSigner {
                hash_mode: miner.hash_mode.clone(),
                num_sigs: miner.num_sigs as usize,
                public_keys: pubks,
            };

            let last_snapshot = match fork_snapshot {
                Some(sn) => sn.clone(),
                None => SortitionDB::get_canonical_burn_chain_tip(ic).unwrap(),
            };

            let last_snapshot_with_sortition = match parent_block_snapshot {
                Some(sn) => sn.clone(),
                None => SortitionDB::get_first_block_snapshot(ic).unwrap(),
            };

            // prove on the last-ever sortition's hash to produce the new seed
            let proof = miner
                .make_proof(&leader_key.public_key, &last_snapshot.sortition_hash)
                .expect(&format!(
                    "FATAL: no private key for {}",
                    leader_key.public_key.to_hex()
                ));

            let new_seed = VRFSeed::from_proof(&proof);

            let get_commit_res = SortitionDB::get_block_commit(
                ic.conn(),
                &last_snapshot_with_sortition.winning_block_txid,
                &last_snapshot_with_sortition.sortition_id,
            )
            .expect("FATAL: failed to read block commit");
            let mut txop = match get_commit_res {
                Some(parent) => {
                    let txop = LeaderBlockCommitOp::new(
                        block_hash,
                        self.block_height,
                        &new_seed,
                        &parent,
                        leader_key.block_height as u32,
                        leader_key.vtxindex as u16,
                        burn_fee,
                        &input,
                        &apparent_sender,
                    );
                    txop
                }
                None => {
                    // initial
                    let txop = LeaderBlockCommitOp::initial(
                        block_hash,
                        self.block_height,
                        &new_seed,
                        leader_key,
                        burn_fee,
                        &input,
                        &apparent_sender,
                    );
                    txop
                }
            };

            txop.set_burn_height(self.block_height);
            txop.vtxindex = self.txs.len() as u32;
            txop.burn_header_hash = BurnchainHeaderHash::from_test_data(
                txop.block_height,
                &self.parent_snapshot.index_root,
                self.fork_id,
            ); // NOTE: override this if you intend to insert into the sortdb!
            txop.txid =
                Txid::from_test_data(txop.block_height, txop.vtxindex, &txop.burn_header_hash, 0);

            self.txs
                .push(BlockstackOperationType::LeaderBlockCommit(txop.clone()));

            miner.block_commits.push(txop.clone());
            txop
        }

        // TODO: user burn support

        pub fn patch_from_chain_tip(&mut self, parent_snapshot: &BlockSnapshot) -> () {
            assert_eq!(parent_snapshot.block_height + 1, self.block_height);

            for i in 0..self.txs.len() {
                match self.txs[i] {
                    BlockstackOperationType::LeaderKeyRegister(ref mut data) => {
                        assert_eq!(data.block_height, self.block_height);
                        data.consensus_hash = parent_snapshot.consensus_hash.clone();
                    }

                    BlockstackOperationType::UserBurnSupport(ref mut data) => {
                        assert_eq!(data.block_height, self.block_height);
                        data.consensus_hash = parent_snapshot.consensus_hash.clone();
                    }
                    _ => {}
                }
            }
        }

        pub fn mine(&self, db: &mut SortitionDB, burnchain: &Burnchain) -> BlockSnapshot {
            let block_hash = BurnchainHeaderHash::from_test_data(
                self.block_height,
                &self.parent_snapshot.index_root,
                self.fork_id,
            );
            let mock_bitcoin_block = BitcoinBlock::new(
                self.block_height,
                &block_hash,
                &self.parent_snapshot.burn_header_hash,
                &vec![],
                get_epoch_time_secs(),
            );
            let block = BurnchainBlock::Bitcoin(mock_bitcoin_block);

            // this is basically lifted verbatum from Burnchain::process_block_ops()

            test_debug!(
                "Process block {} {}",
                block.block_height(),
                &block.block_hash()
            );

            let header = block.header();
            let sort_id = SortitionId::stubbed(&header.parent_block_hash);
            let mut sortition_db_handle = SortitionHandleTx::begin(db, &sort_id).unwrap();

            let parent_snapshot = sortition_db_handle
                .get_block_snapshot(&header.parent_block_hash, &sort_id)
                .unwrap()
                .expect("FATAL: failed to get burnchain linkage info");

            let blockstack_txs = self.txs.clone();

            let new_snapshot = sortition_db_handle
                .process_block_txs(
                    &parent_snapshot,
                    &header,
                    burnchain,
                    blockstack_txs,
                    None,
                    PoxId::stubbed(),
                    None,
                    0,
                )
                .unwrap();
            sortition_db_handle.commit().unwrap();

            new_snapshot.0
        }

        pub fn mine_pox<
            'a,
            T: BlockEventDispatcher,
            N: CoordinatorNotices,
            R: RewardSetProvider,
        >(
            &self,
            db: &mut SortitionDB,
            burnchain: &Burnchain,
            coord: &mut ChainsCoordinator<'a, T, N, R>,
        ) -> BlockSnapshot {
            let block_hash = BurnchainHeaderHash::from_test_data(
                self.block_height,
                &self.parent_snapshot.index_root,
                self.fork_id,
            );
            let mock_bitcoin_block = BitcoinBlock::new(
                self.block_height,
                &block_hash,
                &self.parent_snapshot.burn_header_hash,
                &vec![],
                get_epoch_time_secs(),
            );
            let block = BurnchainBlock::Bitcoin(mock_bitcoin_block);

            test_debug!(
                "Process PoX block {} {}",
                block.block_height(),
                &block.block_hash()
            );

            let header = block.header();

            let mut burnchain_db =
                BurnchainDB::open(&burnchain.get_burnchaindb_path(), true).unwrap();
            burnchain_db
                .raw_store_burnchain_block(header.clone(), self.txs.clone())
                .unwrap();

            coord.handle_new_burnchain_block().unwrap();

            let snapshot = SortitionDB::get_canonical_burn_chain_tip(db.conn()).unwrap();
            snapshot
        }
    }

    impl TestBurnchainFork {
        pub fn new(
            start_height: u64,
            start_header_hash: &BurnchainHeaderHash,
            start_index_root: &TrieHash,
            fork_id: u64,
        ) -> TestBurnchainFork {
            TestBurnchainFork {
                start_height,
                mined: 0,
                tip_header_hash: start_header_hash.clone(),
                tip_sortition_id: SortitionId([0x00; 32]),
                tip_index_root: start_index_root.clone(),
                blocks: vec![],
                pending_blocks: vec![],
                fork_id: fork_id,
            }
        }

        pub fn fork(&self) -> TestBurnchainFork {
            let mut new_fork = (*self).clone();
            new_fork.fork_id += 1;
            new_fork
        }

        pub fn append_block(&mut self, b: TestBurnchainBlock) -> () {
            self.pending_blocks.push(b);
        }

        pub fn get_tip(&mut self, ic: &SortitionDBConn) -> BlockSnapshot {
            test_debug!(
                "Get tip snapshot at {} (sortition ID {})",
                &self.tip_header_hash,
                &self.tip_sortition_id
            );
            SortitionDB::get_block_snapshot(ic, &self.tip_sortition_id)
                .unwrap()
                .unwrap()
        }

        pub fn next_block(&mut self, ic: &SortitionDBConn) -> TestBurnchainBlock {
            let fork_tip = self.get_tip(ic);
            TestBurnchainBlock::new(&fork_tip, self.fork_id)
        }

        pub fn mine_pending_blocks(
            &mut self,
            db: &mut SortitionDB,
            burnchain: &Burnchain,
        ) -> BlockSnapshot {
            let mut snapshot = {
                let ic = db.index_conn();
                self.get_tip(&ic)
            };

            for mut block in self.pending_blocks.drain(..) {
                // fill in consensus hash and block hash, which we may not have known at the call
                // to next_block (since we can call next_block() many times without mining blocks)
                block.patch_from_chain_tip(&snapshot);

                snapshot = block.mine(db, burnchain);

                self.blocks.push(block);
                self.mined += 1;
                self.tip_index_root = snapshot.index_root;
                self.tip_header_hash = snapshot.burn_header_hash;
                self.tip_sortition_id = snapshot.sortition_id;
            }

            // give back the new chain tip
            snapshot
        }

        pub fn mine_pending_blocks_pox<
            'a,
            T: BlockEventDispatcher,
            N: CoordinatorNotices,
            R: RewardSetProvider,
        >(
            &mut self,
            db: &mut SortitionDB,
            burnchain: &Burnchain,
            coord: &mut ChainsCoordinator<'a, T, N, R>,
        ) -> BlockSnapshot {
            let mut snapshot = {
                let ic = db.index_conn();
                self.get_tip(&ic)
            };

            for mut block in self.pending_blocks.drain(..) {
                // fill in consensus hash and block hash, which we may not have known at the call
                // to next_block (since we can call next_block() many times without mining blocks)
                block.patch_from_chain_tip(&snapshot);

                snapshot = block.mine_pox(db, burnchain, coord);

                self.blocks.push(block);
                self.mined += 1;
                self.tip_index_root = snapshot.index_root;
                self.tip_header_hash = snapshot.burn_header_hash;
                self.tip_sortition_id = snapshot.sortition_id;
            }

            // give back the new chain tip
            snapshot
        }
    }

    impl TestBurnchainNode {
        pub fn new() -> TestBurnchainNode {
            let first_block_height = 100;
            let first_block_hash = BurnchainHeaderHash([0u8; 32]);
            let db = SortitionDB::connect_test(first_block_height, &first_block_hash).unwrap();
            TestBurnchainNode {
                sortdb: db,
                dirty: false,
                burnchain: Burnchain::default_unittest(first_block_height, &first_block_hash),
            }
        }

        pub fn mine_fork(&mut self, fork: &mut TestBurnchainFork) -> BlockSnapshot {
            fork.mine_pending_blocks(&mut self.sortdb, &self.burnchain)
        }
    }

    fn process_next_sortition(
        node: &mut TestBurnchainNode,
        fork: &mut TestBurnchainFork,
        miners: &mut Vec<TestMiner>,
        prev_keys: &Vec<LeaderKeyRegisterOp>,
        block_hashes: &Vec<BlockHeaderHash>,
    ) -> (
        BlockSnapshot,
        Vec<LeaderKeyRegisterOp>,
        Vec<LeaderBlockCommitOp>,
        Vec<UserBurnSupportOp>,
    ) {
        assert_eq!(miners.len(), block_hashes.len());

        let mut block = {
            let ic = node.sortdb.index_conn();
            fork.next_block(&ic)
        };

        let mut next_commits = vec![];
        let mut next_prev_keys = vec![];

        if prev_keys.len() > 0 {
            assert_eq!(miners.len(), prev_keys.len());

            // make a Stacks block (hash) for each of the prior block's keys
            for j in 0..miners.len() {
                let block_commit_op = {
                    let ic = node.sortdb.index_conn();
                    let hash = block_hashes[j].clone();
                    block.add_leader_block_commit(
                        &ic,
                        &mut miners[j],
                        &hash,
                        ((j + 1) as u64) * 1000,
                        &prev_keys[j],
                        None,
                        None,
                    )
                };
                next_commits.push(block_commit_op);
            }
        }

        // have each leader register a VRF key
        for j in 0..miners.len() {
            let key_register_op = block.add_leader_key_register(&mut miners[j]);
            next_prev_keys.push(key_register_op);
        }

        test_debug!("Mine {} transactions", block.txs.len());

        fork.append_block(block);
        let tip_snapshot = node.mine_fork(fork);

        // TODO: user burn support
        (tip_snapshot, next_prev_keys, next_commits, vec![])
    }

    fn verify_keys_accepted(
        node: &mut TestBurnchainNode,
        prev_keys: &Vec<LeaderKeyRegisterOp>,
    ) -> () {
        // all keys accepted
        for key in prev_keys.iter() {
            let tx_opt =
                SortitionDB::get_burnchain_transaction(node.sortdb.conn(), &key.txid).unwrap();
            assert!(tx_opt.is_some());

            let tx = tx_opt.unwrap();
            match tx {
                BlockstackOperationType::LeaderKeyRegister(ref op) => {
                    assert_eq!(*op, *key);
                }
                _ => {
                    assert!(false);
                }
            }
        }
    }

    fn verify_commits_accepted(
        node: &TestBurnchainNode,
        next_block_commits: &Vec<LeaderBlockCommitOp>,
    ) -> () {
        // all commits accepted
        for commit in next_block_commits.iter() {
            let tx_opt =
                SortitionDB::get_burnchain_transaction(node.sortdb.conn(), &commit.txid).unwrap();
            assert!(tx_opt.is_some());

            let tx = tx_opt.unwrap();
            match tx {
                BlockstackOperationType::LeaderBlockCommit(ref op) => {
                    assert_eq!(*op, *commit);
                }
                _ => {
                    assert!(false);
                }
            }
        }
    }

    #[test]
    fn mine_10_stacks_blocks_1_fork() {
        let mut node = TestBurnchainNode::new();
        let mut miner_factory = TestMinerFactory::new();

        let mut miners = vec![];
        for i in 0..10 {
            miners.push(miner_factory.next_miner(
                &node.burnchain,
                1,
                1,
                AddressHashMode::SerializeP2PKH,
            ));
        }

        let first_snapshot = SortitionDB::get_first_block_snapshot(node.sortdb.conn()).unwrap();
        let mut fork = TestBurnchainFork::new(
            first_snapshot.block_height,
            &first_snapshot.burn_header_hash,
            &first_snapshot.index_root,
            0,
        );
        let mut prev_keys = vec![];

        for i in 0..10 {
            let mut next_block_hashes = vec![];
            for j in 0..miners.len() {
                let hash = BlockHeaderHash([(i * 10 + j + miners.len()) as u8; 32]);
                next_block_hashes.push(hash);
            }

            let (next_snapshot, mut next_prev_keys, next_block_commits, next_user_burns) =
                process_next_sortition(
                    &mut node,
                    &mut fork,
                    &mut miners,
                    &prev_keys,
                    &next_block_hashes,
                );

            verify_keys_accepted(&mut node, &prev_keys);
            verify_commits_accepted(&mut node, &next_block_commits);

            prev_keys.clear();
            prev_keys.append(&mut next_prev_keys);
        }
    }

    #[test]
    fn mine_10_stacks_blocks_2_forks_disjoint() {
        let mut node = TestBurnchainNode::new();
        let mut miner_factory = TestMinerFactory::new();

        let mut miners = vec![];
        for i in 0..10 {
            miners.push(miner_factory.next_miner(
                &node.burnchain,
                1,
                1,
                AddressHashMode::SerializeP2PKH,
            ));
        }

        let first_snapshot = SortitionDB::get_first_block_snapshot(node.sortdb.conn()).unwrap();
        let mut fork_1 = TestBurnchainFork::new(
            first_snapshot.block_height,
            &first_snapshot.burn_header_hash,
            &first_snapshot.index_root,
            0,
        );
        let mut prev_keys_1 = vec![];

        // one fork for 5 blocks...
        for i in 0..5 {
            let mut next_block_hashes = vec![];
            for j in 0..miners.len() {
                let hash = BlockHeaderHash([(i * 10 + j + miners.len()) as u8; 32]);
                next_block_hashes.push(hash);
            }

            let (next_snapshot, mut next_prev_keys, next_block_commits, next_user_burns) =
                process_next_sortition(
                    &mut node,
                    &mut fork_1,
                    &mut miners,
                    &prev_keys_1,
                    &next_block_hashes,
                );

            verify_keys_accepted(&mut node, &prev_keys_1);
            verify_commits_accepted(&mut node, &next_block_commits);

            prev_keys_1.clear();
            prev_keys_1.append(&mut next_prev_keys);
        }

        let mut fork_2 = fork_1.fork();
        let mut prev_keys_2 = prev_keys_1[5..].to_vec();
        prev_keys_1.truncate(5);

        let mut miners_1 = vec![];
        let mut miners_2 = vec![];

        let mut miners_drain = miners.drain(..);
        for i in 0..5 {
            let m = miners_drain.next().unwrap();
            miners_1.push(m);
        }
        for i in 0..5 {
            let m = miners_drain.next().unwrap();
            miners_2.push(m);
        }

        // two disjoint forks for 5 blocks...
        for i in 5..10 {
            let mut next_block_hashes_1 = vec![];
            for j in 0..miners_1.len() {
                let hash = BlockHeaderHash(
                    [(i * (miners_1.len() + miners_2.len()) + j + miners_1.len() + miners_2.len())
                        as u8; 32],
                );
                next_block_hashes_1.push(hash);
            }

            let mut next_block_hashes_2 = vec![];
            for j in 0..miners_2.len() {
                let hash = BlockHeaderHash(
                    [(i * (miners_1.len() + miners_2.len())
                        + (5 + j)
                        + miners_1.len()
                        + miners_2.len()) as u8; 32],
                );
                next_block_hashes_2.push(hash);
            }

            let (next_snapshot_1, mut next_prev_keys_1, next_block_commits_1, next_user_burns_1) =
                process_next_sortition(
                    &mut node,
                    &mut fork_1,
                    &mut miners_1,
                    &prev_keys_1,
                    &next_block_hashes_1,
                );
            let (next_snapshot_2, mut next_prev_keys_2, next_block_commits_2, next_user_burns_2) =
                process_next_sortition(
                    &mut node,
                    &mut fork_2,
                    &mut miners_2,
                    &prev_keys_2,
                    &next_block_hashes_2,
                );

            assert!(next_snapshot_1.burn_header_hash != next_snapshot_2.burn_header_hash);

            verify_keys_accepted(&mut node, &prev_keys_1);
            verify_commits_accepted(&mut node, &next_block_commits_1);

            verify_keys_accepted(&mut node, &prev_keys_2);
            verify_commits_accepted(&mut node, &next_block_commits_2);

            prev_keys_1.clear();
            prev_keys_1.append(&mut next_prev_keys_1);

            prev_keys_2.clear();
            prev_keys_2.append(&mut next_prev_keys_2);
        }
    }

    #[test]
    fn mine_10_stacks_blocks_2_forks_disjoint_same_blocks() {
        let mut node = TestBurnchainNode::new();
        let mut miner_factory = TestMinerFactory::new();

        let mut miners = vec![];
        for i in 0..10 {
            miners.push(miner_factory.next_miner(
                &node.burnchain,
                1,
                1,
                AddressHashMode::SerializeP2PKH,
            ));
        }

        let first_snapshot = SortitionDB::get_first_block_snapshot(node.sortdb.conn()).unwrap();
        let mut fork_1 = TestBurnchainFork::new(
            first_snapshot.block_height,
            &first_snapshot.burn_header_hash,
            &first_snapshot.index_root,
            0,
        );
        let mut prev_keys_1 = vec![];

        // one fork for 5 blocks...
        for i in 0..5 {
            let mut next_block_hashes = vec![];
            for j in 0..miners.len() {
                let hash = BlockHeaderHash([(i * 10 + j + miners.len()) as u8; 32]);
                next_block_hashes.push(hash);
            }

            let (snapshot, mut next_prev_keys, next_block_commits, next_user_burns) =
                process_next_sortition(
                    &mut node,
                    &mut fork_1,
                    &mut miners,
                    &prev_keys_1,
                    &next_block_hashes,
                );

            verify_keys_accepted(&mut node, &prev_keys_1);
            verify_commits_accepted(&mut node, &next_block_commits);

            prev_keys_1.clear();
            prev_keys_1.append(&mut next_prev_keys);
        }

        let mut fork_2 = fork_1.fork();
        let mut prev_keys_2 = prev_keys_1[5..].to_vec();
        prev_keys_1.truncate(5);

        let mut miners_1 = vec![];
        let mut miners_2 = vec![];

        let mut miners_drain = miners.drain(..);
        for i in 0..5 {
            let m = miners_drain.next().unwrap();
            miners_1.push(m);
        }
        for i in 0..5 {
            let m = miners_drain.next().unwrap();
            miners_2.push(m);
        }

        // two disjoint forks for 5 blocks, but miners in each fork mine the same blocks.
        // This tests that we can accept two burnchain forks that each contain the same stacks
        // block history.
        for i in 5..10 {
            let mut next_block_hashes_1 = vec![];
            for j in 0..miners_1.len() {
                let hash = BlockHeaderHash(
                    [(i * (miners_1.len() + miners_2.len()) + j + miners_1.len() + miners_2.len())
                        as u8; 32],
                );
                next_block_hashes_1.push(hash);
            }

            let mut next_block_hashes_2 = vec![];
            for j in 0..miners_2.len() {
                let hash = BlockHeaderHash(
                    [(i * (miners_1.len() + miners_2.len()) + j + miners_1.len() + miners_2.len())
                        as u8; 32],
                );
                next_block_hashes_2.push(hash);
            }

            let (snapshot_1, mut next_prev_keys_1, next_block_commits_1, next_user_burns_1) =
                process_next_sortition(
                    &mut node,
                    &mut fork_1,
                    &mut miners_1,
                    &prev_keys_1,
                    &next_block_hashes_1,
                );
            let (snapshot_2, mut next_prev_keys_2, next_block_commits_2, next_user_burns_2) =
                process_next_sortition(
                    &mut node,
                    &mut fork_2,
                    &mut miners_2,
                    &prev_keys_2,
                    &next_block_hashes_2,
                );

            assert!(snapshot_1.burn_header_hash != snapshot_2.burn_header_hash);
            assert!(snapshot_1.consensus_hash != snapshot_2.consensus_hash);

            // same blocks mined in both forks
            assert_eq!(next_block_commits_1.len(), next_block_commits_2.len());
            for i in 0..next_block_commits_1.len() {
                assert_eq!(
                    next_block_commits_1[i].block_header_hash,
                    next_block_commits_2[i].block_header_hash
                );
            }

            verify_keys_accepted(&mut node, &prev_keys_1);
            verify_commits_accepted(&mut node, &next_block_commits_1);

            verify_keys_accepted(&mut node, &prev_keys_2);
            verify_commits_accepted(&mut node, &next_block_commits_2);

            prev_keys_1.clear();
            prev_keys_1.append(&mut next_prev_keys_1);

            prev_keys_2.clear();
            prev_keys_2.append(&mut next_prev_keys_2);
        }
    }
}
