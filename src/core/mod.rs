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

use burnchains::Burnchain;
use burnchains::Error as burnchain_error;
use chainstate::burn::ConsensusHash;
use chainstate::coordinator::comm::CoordinatorCommunication;
use std::convert::TryFrom;
use util::log;
use vm::costs::ExecutionCost;

use crate::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash};

pub use self::mempool::MemPoolDB;

pub mod mempool;

use std::cmp::Ord;
use std::cmp::Ordering;
use std::cmp::PartialOrd;

// fork set identifier -- to be mixed with the consensus hash (encodes the version)
pub const SYSTEM_FORK_SET_VERSION: [u8; 4] = [23u8, 0u8, 0u8, 0u8];

// chain id
pub const CHAIN_ID_MAINNET: u32 = 0x00000001;
pub const CHAIN_ID_TESTNET: u32 = 0x80000000;

// peer version
pub const PEER_VERSION_MAINNET: u32 = 0x18000000; // 24.0.0.0
pub const PEER_VERSION_TESTNET: u32 = 0xfacade01;

// network identifiers
pub const NETWORK_ID_MAINNET: u32 = 0x17000000;
pub const NETWORK_ID_TESTNET: u32 = 0xff000000;

// default port
pub const NETWORK_P2P_PORT: u16 = 6265;

// sliding burnchain window over which a miner's past block-commit payouts will be used to weight
// its current block-commit in a sortition
pub const MINING_COMMITMENT_WINDOW: u8 = 6;

// This controls a miner heuristic for dropping a transaction from repeated consideration
//  in the mempool. If the transaction caused the block limit to be reached when the block
//  was previously `TX_BLOCK_LIMIT_PROPORTION_HEURISTIC`% full, the transaction will be dropped
//  from the mempool. 20% is chosen as a heuristic here to allow for large transactions to be
//  attempted, but if they cannot be included in an otherwise mostly empty block, not to consider
//  them again.
pub const TX_BLOCK_LIMIT_PROPORTION_HEURISTIC: u64 = 20;

/// The number of blocks which will share the block bonus
///   from burn blocks that occurred without a sortition.
///   (See: https://forum.stacks.org/t/pox-consensus-and-stx-future-supply)
#[cfg(test)]
pub const INITIAL_MINING_BONUS_WINDOW: u16 = 10;
#[cfg(not(test))]
pub const INITIAL_MINING_BONUS_WINDOW: u16 = 10_000;

pub const STACKS_2_0_LAST_BLOCK_TO_PROCESS: u64 = 700_000;
pub const MAINNET_2_0_GENESIS_ROOT_HASH: &str =
    "9653c92b1ad726e2dc17862a3786f7438ab9239c16dd8e7aaba8b0b5c34b52af";

pub const STACKS_EPOCH_MAX: u64 = i64::MAX as u64;

/// This is the "dummy" parent to the actual first burnchain block that we process.
pub const FIRST_BURNCHAIN_CONSENSUS_HASH: ConsensusHash = ConsensusHash([0u8; 20]);

// TODO: TO BE SET BY STACKS_V1_MINER_THRESHOLD
pub const BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT: u64 = 666050;
pub const BITCOIN_MAINNET_FIRST_BLOCK_TIMESTAMP: u32 = 1610643248;
pub const BITCOIN_MAINNET_FIRST_BLOCK_HASH: &str =
    "0000000000000000000ab248c8e35c574514d052a83dbc12669e19bc43df486e";
pub const BITCOIN_MAINNET_INITIAL_REWARD_START_BLOCK: u64 = 651389;

pub const BITCOIN_TESTNET_FIRST_BLOCK_HEIGHT: u64 = 1931620;
pub const BITCOIN_TESTNET_FIRST_BLOCK_TIMESTAMP: u32 = 1612282029;
pub const BITCOIN_TESTNET_FIRST_BLOCK_HASH: &str =
    "00000000000000b8275ac9907d4d8f3b862f93d6f986ba628a2784748e56e51b";

pub const BITCOIN_REGTEST_FIRST_BLOCK_HEIGHT: u64 = 0;
pub const BITCOIN_REGTEST_FIRST_BLOCK_TIMESTAMP: u32 = 0;
pub const BITCOIN_REGTEST_FIRST_BLOCK_HASH: &str =
    "0000000000000000000000000000000000000000000000000000000000000000";

pub const FIRST_STACKS_BLOCK_HASH: BlockHeaderHash = BlockHeaderHash([0u8; 32]);
pub const EMPTY_MICROBLOCK_PARENT_HASH: BlockHeaderHash = BlockHeaderHash([0u8; 32]);

pub const BOOT_BLOCK_HASH: BlockHeaderHash = BlockHeaderHash([0xff; 32]);
pub const BURNCHAIN_BOOT_CONSENSUS_HASH: ConsensusHash = ConsensusHash([0xff; 20]);

pub const MICROSTACKS_PER_STACKS: u32 = 1_000_000;

pub const POX_SUNSET_START: u64 = 100_000;
pub const POX_SUNSET_END: u64 = POX_SUNSET_START + 400_000;

pub const POX_PREPARE_WINDOW_LENGTH: u32 = 100;
pub const POX_REWARD_CYCLE_LENGTH: u32 = 2100;
/// The maximum amount that PoX rewards can be scaled by.
///  That is, if participation is very low, rewards are:
///      POX_MAXIMAL_SCALING x (rewards with 100% participation)
///  Set a 4x, this implies the lower bound of participation for scaling
///   is 25%
pub const POX_MAXIMAL_SCALING: u128 = 4;
/// This is the amount that PoX threshold adjustments are stepped by.
pub const POX_THRESHOLD_STEPS_USTX: u128 = 10_000 * (MICROSTACKS_PER_STACKS as u128);

pub const POX_MAX_NUM_CYCLES: u8 = 12;

pub const BLOCK_LIMIT_MAINNET: ExecutionCost = ExecutionCost {
    write_length: 15_000_000, // roughly 15 mb
    write_count: 7_750,
    read_length: 100_000_000,
    read_count: 7_750,
    runtime: 5_000_000_000,
};

pub const HELIUM_BLOCK_LIMIT: ExecutionCost = ExecutionCost {
    write_length: 15_0_000_000,
    write_count: 5_0_000,
    read_length: 1_000_000_000,
    read_count: 5_0_000,
    // allow much more runtime in helium blocks than mainnet
    runtime: 100_000_000_000,
};

pub const FAULT_DISABLE_MICROBLOCKS_COST_CHECK: &str = "MICROBLOCKS_DISABLE_COST_CHECK";
pub const FAULT_DISABLE_MICROBLOCKS_BYTES_CHECK: &str = "MICROBLOCKS_DISABLE_BYTES_CHECK";

pub fn check_fault_injection(fault_name: &str) -> bool {
    use std::env;

    // only activates if we're testing
    if env::var("BITCOIND_TEST") != Ok("1".to_string()) {
        return false;
    }

    env::var(fault_name) == Ok("1".to_string())
}

#[repr(u32)]
#[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
pub enum StacksEpochId {
    Epoch10 = 0x1000,
    Epoch20 = 0x0200,
    Epoch21 = 0x0201,
}

impl PartialOrd for StacksEpochId {
    // Note: this comparison makes Epoch10 > Epoch21 > Epoch20. Is that the intention?
    fn partial_cmp(&self, other: &StacksEpochId) -> Option<Ordering> {
        (*self as u32).partial_cmp(&(*other as u32))
    }
}

impl Ord for StacksEpochId {
    fn cmp(&self, other: &StacksEpochId) -> Ordering {
        (*self as u32).cmp(&(*other as u32))
    }
}

impl TryFrom<u32> for StacksEpochId {
    type Error = &'static str;

    fn try_from(value: u32) -> Result<StacksEpochId, Self::Error> {
        match value {
            x if x == StacksEpochId::Epoch10 as u32 => Ok(StacksEpochId::Epoch10),
            x if x == StacksEpochId::Epoch20 as u32 => Ok(StacksEpochId::Epoch20),
            x if x == StacksEpochId::Epoch21 as u32 => Ok(StacksEpochId::Epoch21),
            _ => Err("Invalid epoch"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StacksEpoch {
    pub epoch_id: StacksEpochId,
    pub start_height: u64,
    pub end_height: u64,
}

impl StacksEpoch {
    #[cfg(test)]
    pub fn unit_test(first_burnchain_height: u64) -> Vec<StacksEpoch> {
        vec![
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch10,
                start_height: 0,
                end_height: first_burnchain_height,
            },
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch20,
                start_height: first_burnchain_height,
                end_height: STACKS_EPOCH_MAX,
            },
        ]
    }

    #[cfg(test)]
    pub fn unit_test_2_1(first_burnchain_height: u64) -> Vec<StacksEpoch> {
        vec![
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch10,
                start_height: 0,
                end_height: 0,
            },
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch20,
                start_height: 0,
                end_height: first_burnchain_height,
            },
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch21,
                start_height: first_burnchain_height,
                end_height: STACKS_EPOCH_MAX,
            },
        ]
    }

    pub fn all(first_burnchain_height: u64, epoch_2_1_block_height: u64) -> Vec<StacksEpoch> {
        vec![
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch10,
                start_height: 0,
                end_height: first_burnchain_height,
            },
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch20,
                start_height: first_burnchain_height,
                end_height: epoch_2_1_block_height,
            },
            StacksEpoch {
                epoch_id: StacksEpochId::Epoch21,
                start_height: epoch_2_1_block_height,
                end_height: STACKS_EPOCH_MAX,
            },
        ]
    }
}

// StacksEpochs are ordered by start block height
impl PartialOrd for StacksEpoch {
    fn partial_cmp(&self, other: &StacksEpoch) -> Option<Ordering> {
        self.start_height.partial_cmp(&other.start_height)
    }
}

impl Ord for StacksEpoch {
    fn cmp(&self, other: &StacksEpoch) -> Ordering {
        self.start_height.cmp(&other.start_height)
    }
}

pub const STACKS_EPOCHS_MAINNET: &[StacksEpoch] = &[
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch10,
        start_height: 0,
        end_height: BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT,
    },
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch20,
        start_height: BITCOIN_MAINNET_FIRST_BLOCK_HEIGHT,
        end_height: STACKS_2_0_LAST_BLOCK_TO_PROCESS + 1,
    },
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch21,
        start_height: STACKS_2_0_LAST_BLOCK_TO_PROCESS + 1,
        end_height: STACKS_EPOCH_MAX,
    },
];

pub const STACKS_EPOCHS_TESTNET: &[StacksEpoch] = &[
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch10,
        start_height: 0,
        end_height: BITCOIN_TESTNET_FIRST_BLOCK_HEIGHT,
    },
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch20,
        start_height: BITCOIN_TESTNET_FIRST_BLOCK_HEIGHT,
        end_height: STACKS_EPOCH_MAX,
    }, // TODO: add Epoch21 when its start height is decided
];

pub const STACKS_EPOCHS_REGTEST: &[StacksEpoch] = &[
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch10,
        start_height: 0,
        end_height: 0,
    },
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch20,
        start_height: 0,
        end_height: 1000,
    },
    StacksEpoch {
        epoch_id: StacksEpochId::Epoch21,
        start_height: 1000,
        end_height: STACKS_EPOCH_MAX,
    },
];
