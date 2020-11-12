// Copyright (C) 2013-2020 Blocstack PBC, a public benefit corporation
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

use std::collections::{BTreeMap, HashMap};

use chainstate::burn::operations::{
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp, UserBurnSupportOp,
};

use burnchains::Address;
use burnchains::Burnchain;
use burnchains::PublicKey;
use burnchains::Txid;
use burnchains::{BurnchainRecipient, BurnchainSigner, BurnchainTransaction};

use address::AddressHashMode;
use chainstate::stacks::StacksPublicKey;

use util::hash::Hash160;
use util::uint::BitArray;
use util::uint::Uint256;
use util::uint::Uint512;

use util::log;

use util::vrf::VRFPublicKey;

use core::MINING_COMMITMENT_WINDOW;

#[derive(Debug, Clone, PartialEq)]
pub struct BurnSamplePoint {
    pub burns: u128,
    pub range_start: Uint256,
    pub range_end: Uint256,
    pub candidate: LeaderBlockCommitOp,
    pub user_burns: Vec<UserBurnSupportOp>,
}

#[derive(Clone)]
struct LinkedCommitmentScore {
    rel_block_height: u8,
    op: LeaderBlockCommitOp,
    user_burns: u64,
}

#[derive(PartialEq, Eq, Hash)]
struct UserBurnIdentifier {
    rel_block_height: u8,
    key_vtxindex: u16,
    key_block_ptr: u32,
    block_hash: Hash160,
}

impl BurnSamplePoint {
    ///
    /// * `block_commits`: this is a mapping from relative block_height to the block
    ///     commits that occurred at that height. These relative block heights start
    ///     at 0 and increment towards the present. When the mining window is 6, the
    ///     "current" sortition's block commits would be in index 5.
    /// * `sunset_finished_at`: if set, this indicates that the PoX sunset finished before or
    ///     during the mining window. This value is the first index in the block_commits
    ///     for which PoX is fully disabled (i.e., the block commit has a single burn output).
    pub fn make_min_median_distribution(
        mut block_commits: Vec<Vec<LeaderBlockCommitOp>>,
        mut user_burns: Vec<Vec<UserBurnSupportOp>>,
        sunset_finished_at: Option<u8>,
    ) -> Vec<BurnSamplePoint> {
        // sanity check
        assert!(MINING_COMMITMENT_WINDOW > 0);
        assert_eq!(block_commits.len(), user_burns.len());
        assert!(block_commits.len() <= (MINING_COMMITMENT_WINDOW as usize));

        let window_size = block_commits.len() as u8;

        // first, let's link all of the current block commits to the priors
        let mut commits_with_priors: Vec<_> =
            // start with the most recent
            block_commits
            .remove((window_size - 1) as usize)
            .into_iter()
            .map(|op| {
                let mut linked_commits = vec![None; window_size as usize];
                linked_commits[0] = Some(LinkedCommitmentScore {
                        rel_block_height: window_size - 1,
                        op,
                        user_burns: 0
                    });
                linked_commits
            })
            .collect();

        let mut user_burn_targets: HashMap<UserBurnIdentifier, Vec<usize>> = HashMap::new();

        for (ix, linked_commit) in commits_with_priors.iter().enumerate() {
            let cur_commit = &linked_commit[0].as_ref().unwrap().op;
            let user_burn_target_key = UserBurnIdentifier {
                rel_block_height: window_size - 1,
                key_vtxindex: cur_commit.key_vtxindex,
                key_block_ptr: cur_commit.key_block_ptr,
                block_hash: Hash160::from_sha256(&cur_commit.block_header_hash.0),
            };
            if let Some(user_burn_recipients) = user_burn_targets.get_mut(&user_burn_target_key) {
                user_burn_recipients.push(ix);
            } else {
                user_burn_targets.insert(user_burn_target_key, vec![ix]);
            }
        }

        for rel_block_height in (0..(window_size - 1)).rev() {
            let cur_commits = block_commits.remove(rel_block_height as usize);
            let mut cur_commits_map: HashMap<_, _> = cur_commits
                .into_iter()
                .map(|commit| (commit.txid.clone(), commit))
                .collect();
            let sunset_finished = if let Some(sunset_finished_at) = sunset_finished_at {
                sunset_finished_at <= rel_block_height
            } else {
                false
            };
            let expected_index = LeaderBlockCommitOp::expected_chained_utxo(sunset_finished);
            for (commitment_ix, linked_commit) in commits_with_priors.iter_mut().enumerate() {
                let end = linked_commit.iter().rev().find_map(|o| o.as_ref()).unwrap(); // guaranteed to be at least 1 non-none entry

                // check that the commit is using the right output index
                if end.op.input.1 != expected_index {
                    continue;
                }
                if let Some(referenced_commit) = cur_commits_map.remove(&end.op.input.0) {
                    let user_burn_target_key = UserBurnIdentifier {
                        rel_block_height,
                        key_vtxindex: referenced_commit.key_vtxindex,
                        key_block_ptr: referenced_commit.key_block_ptr,
                        block_hash: Hash160::from_sha256(&referenced_commit.block_header_hash.0),
                    };

                    if let Some(user_burn_recipients) =
                        user_burn_targets.get_mut(&user_burn_target_key)
                    {
                        user_burn_recipients.push(commitment_ix);
                    } else {
                        user_burn_targets.insert(user_burn_target_key, vec![commitment_ix]);
                    }

                    // found a chained utxo, connect
                    linked_commit[(window_size - rel_block_height) as usize] =
                        Some(LinkedCommitmentScore {
                            op: referenced_commit,
                            rel_block_height,
                            user_burns: 0,
                        });
                }
            }
        }

        // next, we need to associate user burns with the leader block commits.
        //   this is where things start to go a little wild:
        //
        //  User burns identify a block commit using VRF public key, so we'll use the
        //    user_burn_targets map to figure out which linked commitment should receive
        //    the user burn
        let mut commit_txid_to_user_burns: HashMap<_, Vec<UserBurnSupportOp>> = HashMap::new();

        // iterate across user burns in block_height order
        for (rel_block_height, user_burns_at_height) in user_burns.into_iter().enumerate() {
            for mut user_burn in user_burns_at_height.into_iter() {
                let UserBurnSupportOp {
                    key_vtxindex,
                    key_block_ptr,
                    block_header_hash_160,
                    burn_fee,
                    ..
                } = user_burn.clone();

                let user_burn_target_key = UserBurnIdentifier {
                    rel_block_height: rel_block_height as u8,
                    key_vtxindex: key_vtxindex,
                    key_block_ptr: key_block_ptr,
                    block_hash: block_header_hash_160,
                };

                if let Some(user_burn_recipients) = user_burn_targets.get(&user_burn_target_key) {
                    let per_recipient = burn_fee / (user_burn_recipients.len() as u64);
                    // set the burn fee to the per recipient amount for when we include this
                    //  user burn op in the burn samples
                    user_burn.burn_fee = per_recipient;

                    for recipient in user_burn_recipients.iter() {
                        let recipient_commit = commits_with_priors[*recipient]
                            .get_mut(window_size as usize - 1 - rel_block_height)
                            .expect("BUG: (window_size - i) should be in window range")
                            .as_mut()
                            .expect("BUG: Should have a non-none commit entry");
                        // cheap sanity checks
                        assert_eq!(
                            recipient_commit.op.key_block_ptr,
                            user_burn_target_key.key_block_ptr
                        );
                        assert_eq!(
                            recipient_commit.op.key_vtxindex,
                            user_burn_target_key.key_vtxindex
                        );
                        // are we at the last block in the window?
                        //  if so, track the user burn op
                        if rel_block_height as u8 == window_size - 1 {
                            if let Some(user_burns) =
                                commit_txid_to_user_burns.get_mut(&recipient_commit.op.txid)
                            {
                                user_burns.push(user_burn.clone());
                            } else {
                                commit_txid_to_user_burns.insert(
                                    recipient_commit.op.txid.clone(),
                                    vec![user_burn.clone()],
                                );
                            }
                        }

                        recipient_commit.user_burns += per_recipient;
                    }
                }
            }
        }

        // now, commits_with_priors has the burn amounts and user burn supports for each
        //   linked commitment, we can now generate the burn sample points.
        let mut burn_sample = commits_with_priors
            .into_iter()
            .map(|mut linked_commits| {
                let mut all_burns: Vec<_> = linked_commits
                    .iter()
                    .map(|commit| {
                        if let Some(commit) = commit {
                            (commit.op.burn_fee as u128) + (commit.user_burns as u128)
                        } else {
                            0
                        }
                    })
                    .collect();
                all_burns.sort();
                let min_burn = all_burns[0];
                let median_burn = if window_size % 2 == 0 {
                    (all_burns[(window_size / 2) as usize]
                        + all_burns[(window_size / 2 - 1) as usize])
                        / 2
                } else {
                    all_burns[(window_size / 2) as usize]
                };

                let burns = (min_burn + median_burn) / 2;
                let candidate = linked_commits.remove(0).unwrap().op;
                let user_burns = commit_txid_to_user_burns
                    .get(&candidate.txid)
                    .cloned()
                    .unwrap_or_default();
                BurnSamplePoint {
                    burns,
                    range_start: Uint256::zero(), // To be filled in
                    range_end: Uint256::zero(),   // To be filled in
                    candidate,
                    user_burns,
                }
            })
            .collect();

        // calculate burn ranges
        BurnSamplePoint::make_sortition_ranges(&mut burn_sample);
        burn_sample
    }

    /// Make a burn distribution -- a list of (burn total, block candidate) pairs -- from a block's
    /// block commits, leader keys, and user support burns.
    ///
    /// All operations need to be from the same block height, or this method panics.
    ///
    /// If a key is used more than once (i.e. by two or more commits), then only the first commit
    /// will be incorporated.  All other commits will be dropped.
    ///
    /// Returns the distribution, which consumes the given lists of operations.
    pub fn make_distribution(
        all_block_candidates: Vec<LeaderBlockCommitOp>,
        consumed_leader_keys: Vec<LeaderKeyRegisterOp>,
        user_burns: Vec<UserBurnSupportOp>,
    ) -> Vec<BurnSamplePoint> {
        Self::make_min_median_distribution(vec![all_block_candidates], vec![user_burns], None)
    }

    // sanity checks for making a burn distribution
    fn ops_sanity_checks(
        block_candidates: &Vec<LeaderBlockCommitOp>,
        user_burns: &Vec<UserBurnSupportOp>,
    ) -> () {
        // sanity checks
        if block_candidates.len() > 1 {
            let block_height = block_candidates[0].block_height;
            for i in 1..block_candidates.len() {
                if block_candidates[i].block_height != block_height {
                    panic!(
                        "FATAL ERROR: block commit {} is at ({},{}) not {}",
                        &block_candidates[i].txid,
                        block_candidates[i].block_height,
                        block_candidates[i].vtxindex,
                        block_height
                    );
                }
            }

            for i in 0..block_candidates.len() - 1 {
                if block_candidates[i].vtxindex >= block_candidates[i + 1].vtxindex {
                    panic!("FATAL ERROR: block candidates are not in order");
                }
            }
        }

        if user_burns.len() > 1 {
            let block_height = user_burns[0].block_height;
            for i in 0..user_burns.len() {
                if user_burns[i].block_height != block_height {
                    panic!(
                        "FATAL ERROR: user burn {} is at ({},{}) not {}",
                        &user_burns[i].txid,
                        user_burns[i].block_height,
                        user_burns[i].vtxindex,
                        block_height
                    );
                }
            }

            for i in 0..user_burns.len() - 1 {
                if user_burns[i].vtxindex >= user_burns[i + 1].vtxindex {
                    panic!("FATAL ERROR: user burns are not in order");
                }
            }
        }
    }

    /// Calculate the ranges between 0 and 2**256 - 1 over which each point in the burn sample
    /// applies, so we can later select which block to use.
    fn make_sortition_ranges(burn_sample: &mut Vec<BurnSamplePoint>) -> () {
        if burn_sample.len() == 0 {
            // empty sample
            return;
        }
        if burn_sample.len() == 1 {
            // sample that covers the whole range
            burn_sample[0].range_start = Uint256::zero();
            burn_sample[0].range_end = Uint256::max();
            return;
        }

        // total burns for valid blocks?
        // NOTE: this can't overflow -- there's no way we get that many (u64) burns
        let total_burns_u128 = BurnSamplePoint::get_total_burns(&burn_sample).unwrap() as u128;
        let total_burns = Uint512::from_u128(total_burns_u128);

        // determine range start/end for each sample.
        // Use fixed-point math on an unsigned 512-bit number --
        //   * the upper 256 bits are the integer
        //   * the lower 256 bits are the fraction
        // These range fields correspond to ranges in the 32-byte hash space
        let mut burn_acc = Uint512::from_u128(burn_sample[0].burns);

        burn_sample[0].range_start = Uint256::zero();
        burn_sample[0].range_end =
            ((Uint512::from_uint256(&Uint256::max()) * burn_acc) / total_burns).to_uint256();
        for i in 1..burn_sample.len() {
            burn_sample[i].range_start = burn_sample[i - 1].range_end;

            burn_acc = burn_acc + Uint512::from_u128(burn_sample[i].burns);
            burn_sample[i].range_end =
                ((Uint512::from_uint256(&Uint256::max()) * burn_acc) / total_burns).to_uint256();
        }

        for _i in 0..burn_sample.len() {
            test_debug!(
                "Range for block {}: {} / {}: {} - {}",
                burn_sample[_i].candidate.block_header_hash,
                burn_sample[_i].burns,
                total_burns_u128,
                burn_sample[_i].range_start,
                burn_sample[_i].range_end
            );
        }
    }

    /// Calculate the total amount of crypto destroyed in this burn distribution.
    /// Returns None if there was an overflow.
    pub fn get_total_burns(burn_dist: &Vec<BurnSamplePoint>) -> Option<u64> {
        let block_burn_total_u128: u128 =
            burn_dist
                .iter()
                .fold(0u128, |mut burns_so_far, sample_point| {
                    burns_so_far += sample_point.burns;
                    burns_so_far
                });

        // check overflow
        if block_burn_total_u128 >= u64::max_value().into() {
            return None;
        }
        let block_burn_total = block_burn_total_u128 as u64;
        Some(block_burn_total)
    }
}

#[cfg(test)]
mod tests {
    use super::BurnSamplePoint;

    use std::marker::PhantomData;

    use burnchains::Address;
    use burnchains::Burnchain;
    use burnchains::BurnchainSigner;
    use burnchains::PublicKey;

    use chainstate::burn::operations::{
        BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp, UserBurnSupportOp,
    };

    use burnchains::bitcoin::address::BitcoinAddress;
    use burnchains::bitcoin::keys::BitcoinPublicKey;
    use burnchains::bitcoin::BitcoinNetworkType;

    use burnchains::{BurnchainHeaderHash, Txid};
    use chainstate::burn::{BlockHeaderHash, ConsensusHash, VRFSeed};
    use util::hash::hex_bytes;
    use util::vrf::VRFPublicKey;

    use util::hash::Hash160;
    use util::uint::BitArray;
    use util::uint::Uint256;
    use util::uint::Uint512;

    use util::log;

    use address::AddressHashMode;
    use chainstate::stacks::StacksAddress;
    use chainstate::stacks::StacksPublicKey;

    struct BurnDistFixture {
        consumed_leader_keys: Vec<LeaderKeyRegisterOp>,
        block_commits: Vec<LeaderBlockCommitOp>,
        user_burns: Vec<UserBurnSupportOp>,
        res: Vec<BurnSamplePoint>,
    }

    #[test]
    fn make_burn_distribution() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let leader_key_1 = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![01, 02, 03, 04, 05],
            address: StacksAddress::from_bitcoin_address(
                &BitcoinAddress::from_scriptpubkey(
                    BitcoinNetworkType::Testnet,
                    &hex_bytes("76a9140be3e286a15ea85882761618e366586b5574100d88ac").unwrap(),
                )
                .unwrap(),
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 456,
            block_height: 123,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000001",
            )
            .unwrap(),
        };

        let leader_key_2 = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("bb519494643f79f1dea0350e6fb9a1da88dfdb6137117fc2523824a8aa44fe1c")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![01, 02, 03, 04, 05],
            address: StacksAddress::from_bitcoin_address(
                &BitcoinAddress::from_scriptpubkey(
                    BitcoinNetworkType::Testnet,
                    &hex_bytes("76a91432b6c66189da32bd0a9f00ee4927f569957d71aa88ac").unwrap(),
                )
                .unwrap(),
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("9410df84e2b440055c33acb075a0687752df63fe8fe84aeec61abe469f0448c7")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 457,
            block_height: 122,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000002",
            )
            .unwrap(),
        };

        let leader_key_3 = LeaderKeyRegisterOp {
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("de8af7037e522e65d2fe2d63fb1b764bfea829df78b84444338379df13144a02")
                    .unwrap(),
            )
            .unwrap(),
            memo: vec![01, 02, 03, 04, 05],
            address: StacksAddress::from_bitcoin_address(
                &BitcoinAddress::from_scriptpubkey(
                    BitcoinNetworkType::Testnet,
                    &hex_bytes("76a91432b6c66189da32bd0a9f00ee4927f569957d71aa88ac").unwrap(),
                )
                .unwrap(),
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("eb54704f71d4a2d1128d60ffccced547054b52250ada6f3e7356165714f44d4c")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 10,
            block_height: 121,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000012",
            )
            .unwrap(),
        };

        let user_burn_noblock = UserBurnSupportOp {
            address: StacksAddress::new(1, Hash160([1u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("4444444444444444444444444444444444444444").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333").unwrap(),
            )
            .unwrap(),
            key_block_ptr: 1,
            key_vtxindex: 772,
            burn_fee: 12345,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 12,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let user_burn_1 = UserBurnSupportOp {
            address: StacksAddress::new(2, Hash160([2u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("4444444444444444444444444444444444444444").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("7150f635054b87df566a970b21e07030d6444bf2").unwrap(),
            )
            .unwrap(), // 22222....2222
            key_block_ptr: 123,
            key_vtxindex: 456,
            burn_fee: 10000,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 13,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let user_burn_1_2 = UserBurnSupportOp {
            address: StacksAddress::new(3, Hash160([3u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("4444444444444444444444444444444444444444").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("a366b51292bef4edd64063d9145c617fec373bceb0758e98cd72becd84d54c7a")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("7150f635054b87df566a970b21e07030d6444bf2").unwrap(),
            )
            .unwrap(), // 22222....2222
            key_block_ptr: 123,
            key_vtxindex: 456,
            burn_fee: 30000,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 14,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let user_burn_2 = UserBurnSupportOp {
            address: StacksAddress::new(4, Hash160([4u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("4444444444444444444444444444444444444444").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("bb519494643f79f1dea0350e6fb9a1da88dfdb6137117fc2523824a8aa44fe1c")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("037a1e860899a4fa823c18b66f6264d20236ec58").unwrap(),
            )
            .unwrap(), // 22222....2223
            key_block_ptr: 122,
            key_vtxindex: 457,
            burn_fee: 20000,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716d")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 15,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let user_burn_2_2 = UserBurnSupportOp {
            address: StacksAddress::new(5, Hash160([5u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("4444444444444444444444444444444444444444").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("bb519494643f79f1dea0350e6fb9a1da88dfdb6137117fc2523824a8aa44fe1c")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("037a1e860899a4fa823c18b66f6264d20236ec58").unwrap(),
            )
            .unwrap(), // 22222....2223
            key_block_ptr: 122,
            key_vtxindex: 457,
            burn_fee: 40000,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716c")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 16,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let user_burn_nokey = UserBurnSupportOp {
            address: StacksAddress::new(6, Hash160([6u8; 20])),
            consensus_hash: ConsensusHash::from_bytes(
                &hex_bytes("4444444444444444444444444444444444444444").unwrap(),
            )
            .unwrap(),
            public_key: VRFPublicKey::from_bytes(
                &hex_bytes("3f3338db51f2b1f6ac0cf6177179a24ee130c04ef2f9849a64a216969ab60e70")
                    .unwrap(),
            )
            .unwrap(),
            block_header_hash_160: Hash160::from_bytes(
                &hex_bytes("037a1e860899a4fa823c18b66f6264d20236ec58").unwrap(),
            )
            .unwrap(),
            key_block_ptr: 121,
            key_vtxindex: 772,
            burn_fee: 12345,

            txid: Txid::from_bytes_be(
                &hex_bytes("1d5cbdd276495b07f0e0bf0181fa57c175b217bc35531b078d62fc20986c716e")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 17,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let block_commit_1 = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222222")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333333")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: 111,
            parent_vtxindex: 456,
            key_block_ptr: 123,
            key_vtxindex: 456,
            memo: vec![0x80],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            commit_outs: vec![],

            txid: Txid::from_bytes_be(
                &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 443,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let block_commit_2 = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222223")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333334")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: 112,
            parent_vtxindex: 111,
            key_block_ptr: 122,
            key_vtxindex: 457,
            memo: vec![0x80],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            commit_outs: vec![],

            txid: Txid::from_bytes_be(
                &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27d0")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 444,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        let block_commit_3 = LeaderBlockCommitOp {
            sunset_burn: 0,
            block_header_hash: BlockHeaderHash::from_bytes(
                &hex_bytes("2222222222222222222222222222222222222222222222222222222222222224")
                    .unwrap(),
            )
            .unwrap(),
            new_seed: VRFSeed::from_bytes(
                &hex_bytes("3333333333333333333333333333333333333333333333333333333333333335")
                    .unwrap(),
            )
            .unwrap(),
            parent_block_ptr: 113,
            parent_vtxindex: 111,
            key_block_ptr: 121,
            key_vtxindex: 10,
            memo: vec![0x80],

            burn_fee: 23456,
            input: (Txid([0; 32]), 0),
            commit_outs: vec![],

            txid: Txid::from_bytes_be(
                &hex_bytes("301dc687a9f06a1ae87a013f27133e9cec0843c2983567be73e185827c7c13de")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 445,
            block_height: 124,
            burn_header_hash: BurnchainHeaderHash::from_hex(
                "0000000000000000000000000000000000000000000000000000000000000004",
            )
            .unwrap(),
        };

        /*
         You can generate the burn sample ranges with this Python script:
         #!/usr/bin/python

         import sys

         a = eval(sys.argv[1])
         b = eval(sys.argv[2])

         s = '{:0128x}'.format((a * (2**256 - 1)) / b).decode('hex')[::-1];
         l = ['0x{:016x}'.format(int(s[(8*i):(8*(i+1))][::-1].encode('hex'),16)) for i in range(0,(256/8/8))]

         print float(a) / b
         print '{:0128x}'.format((a * (2**256 - 1)) / b)
         print '[' + ', '.join(l) + ']'
        */

        let fixtures: Vec<BurnDistFixture> = vec![
            BurnDistFixture {
                consumed_leader_keys: vec![],
                block_commits: vec![],
                user_burns: vec![],
                res: vec![],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![leader_key_1.clone()],
                block_commits: vec![block_commit_1.clone()],
                user_burns: vec![],
                res: vec![BurnSamplePoint {
                    burns: block_commit_1.burn_fee.into(),
                    range_start: Uint256::zero(),
                    range_end: Uint256::max(),
                    candidate: block_commit_1.clone(),
                    user_burns: vec![],
                }],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![leader_key_1.clone(), leader_key_2.clone()],
                block_commits: vec![block_commit_1.clone(), block_commit_2.clone()],
                user_burns: vec![],
                res: vec![
                    BurnSamplePoint {
                        burns: block_commit_1.burn_fee.into(),
                        range_start: Uint256::zero(),
                        range_end: Uint256([
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0x7fffffffffffffff,
                        ]),
                        candidate: block_commit_1.clone(),
                        user_burns: vec![],
                    },
                    BurnSamplePoint {
                        burns: block_commit_2.burn_fee.into(),
                        range_start: Uint256([
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0x7fffffffffffffff,
                        ]),
                        range_end: Uint256::max(),
                        candidate: block_commit_2.clone(),
                        user_burns: vec![],
                    },
                ],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![leader_key_1.clone(), leader_key_2.clone()],
                block_commits: vec![block_commit_1.clone(), block_commit_2.clone()],
                user_burns: vec![user_burn_noblock.clone()],
                res: vec![
                    BurnSamplePoint {
                        burns: block_commit_1.burn_fee.into(),
                        range_start: Uint256::zero(),
                        range_end: Uint256([
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0x7fffffffffffffff,
                        ]),
                        candidate: block_commit_1.clone(),
                        user_burns: vec![],
                    },
                    BurnSamplePoint {
                        burns: block_commit_2.burn_fee.into(),
                        range_start: Uint256([
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0x7fffffffffffffff,
                        ]),
                        range_end: Uint256::max(),
                        candidate: block_commit_2.clone(),
                        user_burns: vec![],
                    },
                ],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![leader_key_1.clone(), leader_key_2.clone()],
                block_commits: vec![block_commit_1.clone(), block_commit_2.clone()],
                user_burns: vec![user_burn_nokey.clone()],
                res: vec![
                    BurnSamplePoint {
                        burns: block_commit_1.burn_fee.into(),
                        range_start: Uint256::zero(),
                        range_end: Uint256([
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0x7fffffffffffffff,
                        ]),
                        candidate: block_commit_1.clone(),
                        user_burns: vec![],
                    },
                    BurnSamplePoint {
                        burns: block_commit_2.burn_fee.into(),
                        range_start: Uint256([
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0xffffffffffffffff,
                            0x7fffffffffffffff,
                        ]),
                        range_end: Uint256::max(),
                        candidate: block_commit_2.clone(),
                        user_burns: vec![],
                    },
                ],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![leader_key_1.clone(), leader_key_2.clone()],
                block_commits: vec![block_commit_1.clone(), block_commit_2.clone()],
                user_burns: vec![
                    user_burn_noblock.clone(),
                    user_burn_1.clone(),
                    user_burn_nokey.clone(),
                ],
                res: vec![
                    BurnSamplePoint {
                        burns: (block_commit_1.burn_fee + user_burn_1.burn_fee).into(),
                        range_start: Uint256::zero(),
                        range_end: Uint256([
                            0x441d393138e5a796,
                            0xbada4a3d4046d839,
                            0xa24749933957018c,
                            0xa4e5f328cf38744d,
                        ]),
                        candidate: block_commit_1.clone(),
                        user_burns: vec![user_burn_1.clone()],
                    },
                    BurnSamplePoint {
                        burns: block_commit_2.burn_fee.into(),
                        range_start: Uint256([
                            0x441d393138e5a796,
                            0xbada4a3d4046d839,
                            0xa24749933957018c,
                            0xa4e5f328cf38744d,
                        ]),
                        range_end: Uint256::max(),
                        candidate: block_commit_2.clone(),
                        user_burns: vec![],
                    },
                ],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![leader_key_1.clone(), leader_key_2.clone()],
                block_commits: vec![block_commit_1.clone(), block_commit_2.clone()],
                user_burns: vec![
                    user_burn_noblock.clone(),
                    user_burn_1.clone(),
                    user_burn_2.clone(),
                    user_burn_nokey.clone(),
                ],
                res: vec![
                    BurnSamplePoint {
                        burns: (block_commit_1.burn_fee + user_burn_1.burn_fee).into(),
                        range_start: Uint256::zero(),
                        range_end: Uint256([
                            0x65db6527a5c06ed7,
                            0xfbf9725ae754dd80,
                            0xeafb8d991cf9964d,
                            0x6898693a2f1713b4,
                        ]),
                        candidate: block_commit_1.clone(),
                        user_burns: vec![user_burn_1.clone()],
                    },
                    BurnSamplePoint {
                        burns: (block_commit_2.burn_fee + user_burn_2.burn_fee).into(),
                        range_start: Uint256([
                            0x65db6527a5c06ed7,
                            0xfbf9725ae754dd80,
                            0xeafb8d991cf9964d,
                            0x6898693a2f1713b4,
                        ]),
                        range_end: Uint256::max(),
                        candidate: block_commit_2.clone(),
                        user_burns: vec![user_burn_2.clone()],
                    },
                ],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![leader_key_1.clone(), leader_key_2.clone()],
                block_commits: vec![block_commit_1.clone(), block_commit_2.clone()],
                user_burns: vec![
                    user_burn_noblock.clone(),
                    user_burn_1.clone(),
                    user_burn_1_2.clone(),
                    user_burn_2.clone(),
                    user_burn_2_2.clone(),
                    user_burn_nokey.clone(),
                ],
                res: vec![
                    BurnSamplePoint {
                        burns: (block_commit_1.burn_fee
                            + user_burn_1.burn_fee
                            + user_burn_1_2.burn_fee)
                            .into(),
                        range_start: Uint256::zero(),
                        range_end: Uint256([
                            0xbc9e168afe8ad47e,
                            0xbbb6d3eb8d1be6c9,
                            0x45a410039d0a7dc5,
                            0x6b7815d84b0f9fc0,
                        ]),
                        candidate: block_commit_1.clone(),
                        user_burns: vec![user_burn_1.clone(), user_burn_1_2.clone()],
                    },
                    BurnSamplePoint {
                        burns: (block_commit_2.burn_fee
                            + user_burn_2.burn_fee
                            + user_burn_2_2.burn_fee)
                            .into(),
                        range_start: Uint256([
                            0xbc9e168afe8ad47e,
                            0xbbb6d3eb8d1be6c9,
                            0x45a410039d0a7dc5,
                            0x6b7815d84b0f9fc0,
                        ]),
                        range_end: Uint256::max(),
                        candidate: block_commit_2.clone(),
                        user_burns: vec![user_burn_2.clone(), user_burn_2_2.clone()],
                    },
                ],
            },
            BurnDistFixture {
                consumed_leader_keys: vec![
                    leader_key_1.clone(),
                    leader_key_2.clone(),
                    leader_key_3.clone(),
                ],
                block_commits: vec![
                    block_commit_1.clone(),
                    block_commit_2.clone(),
                    block_commit_3.clone(),
                ],
                user_burns: vec![
                    user_burn_noblock.clone(),
                    user_burn_1.clone(),
                    user_burn_1_2.clone(),
                    user_burn_2.clone(),
                    user_burn_2_2.clone(),
                    user_burn_nokey.clone(),
                ],
                res: vec![
                    BurnSamplePoint {
                        burns: (block_commit_1.burn_fee
                            + user_burn_1.burn_fee
                            + user_burn_1_2.burn_fee)
                            .into(),
                        range_start: Uint256::zero(),
                        range_end: Uint256([
                            0xcb48ed15c5086a5c,
                            0x6b29682cfbe4089c,
                            0x4a30e732285c18c9,
                            0x5a7416b691bddbad,
                        ]),
                        candidate: block_commit_1.clone(),
                        user_burns: vec![user_burn_1.clone(), user_burn_1_2.clone()],
                    },
                    BurnSamplePoint {
                        burns: (block_commit_2.burn_fee
                            + user_burn_2.burn_fee
                            + user_burn_2_2.burn_fee)
                            .into(),
                        range_start: Uint256([
                            0xcb48ed15c5086a5c,
                            0x6b29682cfbe4089c,
                            0x4a30e732285c18c9,
                            0x5a7416b691bddbad,
                        ]),
                        range_end: Uint256([
                            0xa224e0451efa00f5,
                            0xa57394a7b38d5b1c,
                            0x6bfdbf24cdb0b617,
                            0xd777aa6d9e769e59,
                        ]),
                        candidate: block_commit_2.clone(),
                        user_burns: vec![user_burn_2.clone(), user_burn_2_2.clone()],
                    },
                    BurnSamplePoint {
                        burns: (block_commit_3.burn_fee).into(),
                        range_start: Uint256([
                            0xa224e0451efa00f5,
                            0xa57394a7b38d5b1c,
                            0x6bfdbf24cdb0b617,
                            0xd777aa6d9e769e59,
                        ]),
                        range_end: Uint256::max(),
                        candidate: block_commit_3.clone(),
                        user_burns: vec![],
                    },
                ],
            },
        ];

        for i in 0..fixtures.len() {
            let f = &fixtures[i];
            let dist = BurnSamplePoint::make_distribution(
                f.block_commits.iter().cloned().collect(),
                f.consumed_leader_keys.iter().cloned().collect(),
                f.user_burns.iter().cloned().collect(),
            );
            assert_eq!(dist, f.res);
        }
    }
}