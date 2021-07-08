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

use std::collections::BTreeMap;

use rusqlite::Connection;

use burnchains::Address;
use burnchains::Burnchain;
use burnchains::BurnchainBlock;
use burnchains::BurnchainBlockHeader;
use burnchains::PublicKey;
use chainstate::burn::db::sortdb::SortitionHandleTx;
use chainstate::burn::distribution::BurnSamplePoint;
use chainstate::burn::operations::{
    BlockstackOperationType, LeaderBlockCommitOp, LeaderKeyRegisterOp, UserBurnSupportOp,
};
use chainstate::burn::BlockSnapshot;
use chainstate::burn::{BurnchainHeaderHash, ConsensusHash, OpsHash, SortitionHash, Txid};
use chainstate::stacks::db::StacksChainState;
use chainstate::stacks::index::MarfTrieId;
use core::*;
use util::db::Error as db_error;
use util::hash::Hash160;
use util::log;
use util::uint::BitArray;
use util::uint::Uint256;
use util::uint::Uint512;

use crate::types::chainstate::StacksBlockId;
use crate::types::chainstate::{BlockHeaderHash, PoxId, SortitionId, VRFSeed};
use crate::types::proof::{ClarityMarfTrieId, TrieHash};

impl BlockSnapshot {
    /// Create the sentinel block snapshot -- the first one
    pub fn initial(
        first_block_height: u64,
        first_burn_header_hash: &BurnchainHeaderHash,
        first_burn_header_timestamp: u64,
    ) -> BlockSnapshot {
        BlockSnapshot {
            block_height: first_block_height,
            burn_header_hash: first_burn_header_hash.clone(),
            burn_header_timestamp: first_burn_header_timestamp,
            parent_burn_header_hash: BurnchainHeaderHash::sentinel(),
            consensus_hash: ConsensusHash([0u8; 20]),
            ops_hash: OpsHash([0u8; 32]),
            total_burn: 0,
            sortition: true,
            sortition_hash: SortitionHash::initial(),
            winning_block_txid: Txid([0u8; 32]),
            winning_stacks_block_hash: FIRST_STACKS_BLOCK_HASH.clone(),
            index_root: TrieHash::from_empty_data(),
            num_sortitions: 0,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: 0,
            canonical_stacks_tip_hash: FIRST_STACKS_BLOCK_HASH.clone(),
            canonical_stacks_tip_consensus_hash: FIRST_BURNCHAIN_CONSENSUS_HASH.clone(),
            // Initial snapshot sets sortition_id = burn_header_hash,
            //  we shouldn't need to update this to use PoxId::initial(),
            //  but if we do, we need to update a lot of test cases.
            sortition_id: SortitionId::stubbed(first_burn_header_hash),
            parent_sortition_id: SortitionId::stubbed(first_burn_header_hash),
            pox_valid: true,
            accumulated_coinbase_ustx: 0,
        }
    }

    pub fn is_initial(&self) -> bool {
        self.sortition_hash == SortitionHash::initial()
    }

    pub fn get_canonical_stacks_block_id(&self) -> StacksBlockId {
        StacksBlockId::new(&self.consensus_hash, &self.canonical_stacks_tip_hash)
    }

    /// Given the weighted burns, VRF seed of the last winner, and sortition hash, pick the next
    /// winner.  Return the index into the distribution *if there is a sample to take*.
    fn sample_burn_distribution(
        dist: &[BurnSamplePoint],
        VRF_seed: &VRFSeed,
        sortition_hash: &SortitionHash,
    ) -> Option<usize> {
        if dist.len() == 0 {
            // no winners
            return None;
        }
        if dist.len() == 1 {
            // only one winner
            return Some(0);
        }

        let index = sortition_hash.mix_VRF_seed(VRF_seed).to_uint256();
        for i in 0..dist.len() {
            if (dist[i].range_start <= index) && (index < dist[i].range_end) {
                debug!(
                    "Sampled {}: sortition index = {}",
                    dist[i].candidate.block_header_hash, &index
                );
                return Some(i);
            }
        }

        // should never happen
        panic!("FATAL ERROR: unable to map {} to a range", index);
    }

    /// Select the next Stacks block header hash using cryptographic sortition.
    /// Go through all block commits at this height, find out how any burn tokens
    /// were spent for them, and select one at random using the relative burn amounts
    /// to weight the sample.  Use HASH(sortition_hash ++ last_VRF_seed) to pick the
    /// winning block commit, and by extension, the next VRF seed.
    ///
    /// If there are no block commits outstanding, then no winner is picked.
    ///
    /// Note that the VRF seed is not guaranteed to be the hash of a valid VRF
    /// proof.  Miners would only build off of leader block commits for which they
    /// (1) have the associated block data and (2) the proof in that block is valid.
    fn select_winning_block(
        sort_tx: &mut SortitionHandleTx,
        block_header: &BurnchainBlockHeader,
        sortition_hash: &SortitionHash,
        burn_dist: &[BurnSamplePoint],
    ) -> Result<Option<LeaderBlockCommitOp>, db_error> {
        let burn_block_height = block_header.block_height;

        // get the last winner's VRF seed in this block's fork
        let last_sortition_snapshot =
            sort_tx.get_last_snapshot_with_sortition(burn_block_height - 1)?;

        let VRF_seed = if last_sortition_snapshot.is_initial() {
            // this is the sentinal "first-sortition" block
            VRFSeed::initial()
        } else {
            // there may have been a prior winning block commit.  Use its VRF seed if possible
            sort_tx
                .get_block_commit(
                    &last_sortition_snapshot.winning_block_txid,
                    &last_sortition_snapshot.sortition_id,
                )?
                .expect("FATAL ERROR: no winning block commits in database (indicates corruption)")
                .new_seed
        };

        // pick the next winner
        let win_idx_opt =
            BlockSnapshot::sample_burn_distribution(burn_dist, &VRF_seed, sortition_hash);
        match win_idx_opt {
            None => {
                // no winner
                Ok(None)
            }
            Some(win_idx) => {
                // winner!
                Ok(Some(burn_dist[win_idx].candidate.clone()))
            }
        }
    }

    /// Make the snapshot struct for the case where _no sortition_ takes place
    fn make_snapshot_no_sortition(
        sort_tx: &mut SortitionHandleTx,
        sortition_id: &SortitionId,
        pox_id: &PoxId,
        parent_snapshot: &BlockSnapshot,
        block_header: &BurnchainBlockHeader,
        first_block_height: u64,
        burn_total: u64,
        sortition_hash: &SortitionHash,
        txids: &Vec<Txid>,
        accumulated_coinbase_ustx: u128,
    ) -> Result<BlockSnapshot, db_error> {
        let block_height = block_header.block_height;
        let block_hash = block_header.block_hash.clone();
        let parent_block_hash = block_header.parent_block_hash.clone();

        let non_winning_block_txid = Txid::from_bytes(&[0u8; 32]).unwrap();
        let non_winning_block_hash = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();

        let ops_hash = OpsHash::from_txids(txids);
        let ch = ConsensusHash::from_parent_block_data(
            sort_tx,
            &ops_hash,
            block_height - 1,
            first_block_height,
            &block_hash,
            burn_total,
            pox_id,
        )?;

        debug!("SORTITION({}): NO BLOCK CHOSEN", block_height);

        Ok(BlockSnapshot {
            block_height: block_height,
            burn_header_hash: block_hash,
            burn_header_timestamp: block_header.timestamp,
            parent_burn_header_hash: parent_block_hash,
            consensus_hash: ch,
            ops_hash: ops_hash,
            total_burn: burn_total,
            sortition: false,
            sortition_hash: sortition_hash.clone(),
            winning_block_txid: non_winning_block_txid,
            winning_stacks_block_hash: non_winning_block_hash,
            index_root: TrieHash::from_empty_data(), // will be overwritten
            num_sortitions: parent_snapshot.num_sortitions,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: parent_snapshot.canonical_stacks_tip_height,
            canonical_stacks_tip_hash: parent_snapshot.canonical_stacks_tip_hash.clone(),
            canonical_stacks_tip_consensus_hash: parent_snapshot
                .canonical_stacks_tip_consensus_hash
                .clone(),
            sortition_id: sortition_id.clone(),
            parent_sortition_id: parent_snapshot.sortition_id.clone(),
            pox_valid: true,
            accumulated_coinbase_ustx,
        })
    }

    /// Make a block snapshot from is block's data and the previous block.
    /// This process will:
    /// * calculate the new consensus hash
    /// * calculate the total burn so far
    /// * determine whether or not we can do a sortition, and if so,
    /// * carry out the sortition to select the next candidate block.
    ///
    /// All of this is rolled into the BlockSnapshot struct.
    ///
    /// Call this *after* you store all of the block's transactions to the burn db.
    pub fn make_snapshot(
        sort_tx: &mut SortitionHandleTx,
        burnchain: &Burnchain,
        my_sortition_id: &SortitionId,
        my_pox_id: &PoxId,
        parent_snapshot: &BlockSnapshot,
        block_header: &BurnchainBlockHeader,
        burn_dist: &[BurnSamplePoint],
        txids: &Vec<Txid>,
        block_burn_total: Option<u64>,
        initial_mining_bonus_ustx: u128,
    ) -> Result<BlockSnapshot, db_error> {
        assert_eq!(
            parent_snapshot.burn_header_hash,
            block_header.parent_block_hash
        );
        assert_eq!(parent_snapshot.block_height + 1, block_header.block_height);

        let block_height = block_header.block_height;
        let block_hash = block_header.block_hash.clone();
        let parent_block_hash = block_header.parent_block_hash.clone();
        let first_block_height = burnchain.first_block_height;

        let last_sortition_hash = parent_snapshot.sortition_hash.clone();
        let last_burn_total = parent_snapshot.total_burn;

        let accumulated_coinbase_ustx = if parent_snapshot.total_burn == 0 {
            0
        } else if parent_snapshot.sortition {
            initial_mining_bonus_ustx
        } else {
            let missed_coinbase = StacksChainState::get_coinbase_reward(
                parent_snapshot.block_height,
                first_block_height,
            );
            parent_snapshot
                .accumulated_coinbase_ustx
                .saturating_add(missed_coinbase)
                .saturating_add(initial_mining_bonus_ustx)
        };

        // next sortition hash
        let next_sortition_hash = last_sortition_hash.mix_burn_header(&block_hash);
        let mut make_snapshot_no_sortition = || {
            BlockSnapshot::make_snapshot_no_sortition(
                sort_tx,
                my_sortition_id,
                my_pox_id,
                parent_snapshot,
                block_header,
                first_block_height,
                last_burn_total,
                &next_sortition_hash,
                &txids,
                accumulated_coinbase_ustx,
            )
        };

        if burn_dist.len() == 0 {
            // no burns happened
            debug!(
                "No burns happened in block";
                "burn_block_height" => %block_height.to_string(),
                "burn_block_hash" => %block_hash.to_string(),
            );

            return make_snapshot_no_sortition();
        }

        // NOTE: this only counts burns from leader block commits and user burns that match them.
        // It ignores user burns that don't match any block.
        let block_burn_total = match block_burn_total {
            Some(total) => {
                if total == 0 {
                    // no one burned, so no sortition
                    debug!(
                        "No transactions submitted burns in block";
                        "burn_block_height" => %block_height.to_string(),
                        "burn_block_hash" => %block_hash.to_string(),
                    );
                    return make_snapshot_no_sortition();
                } else {
                    total
                }
            }
            None => {
                // overflow -- treat as 0 (no sortition)
                warn!("Burn count exceeds maximum threshold");
                return make_snapshot_no_sortition();
            }
        };

        // total burn.  If this ever overflows, then just stall the chain and deny all future
        // sortitions (at least the chain will remain available to serve queries, but it won't be
        // able to make progress).
        let next_burn_total = match last_burn_total.checked_add(block_burn_total) {
            Some(new_total) => new_total,
            None => {
                // overflow.  Deny future sortitions
                warn!("Cumulative sortition burn has overflown.  Subsequent sortitions will be denied.");
                return make_snapshot_no_sortition();
            }
        };

        // Try to pick a next block.
        let winning_block = BlockSnapshot::select_winning_block(
            sort_tx,
            block_header,
            &next_sortition_hash,
            burn_dist,
        )?
        .expect("FATAL: there must be a winner if the burn distribution has 1 or more points");

        // mix in the winning block's VRF seed to the sortition hash.  The next block commits must
        // prove on this final sortition hash.
        let final_sortition_hash = next_sortition_hash.mix_VRF_seed(&winning_block.new_seed);
        let next_ops_hash = OpsHash::from_txids(&txids);
        let next_ch = ConsensusHash::from_parent_block_data(
            sort_tx,
            &next_ops_hash,
            block_height - 1,
            first_block_height,
            &block_hash,
            next_burn_total,
            my_pox_id,
        )?;

        debug!(
            "SORTITION({}): WINNER IS {:?} (from {:?})",
            block_height, &winning_block.block_header_hash, &winning_block.txid
        );

        Ok(BlockSnapshot {
            block_height: block_height,
            burn_header_hash: block_hash,
            burn_header_timestamp: block_header.timestamp,
            parent_burn_header_hash: parent_block_hash,
            consensus_hash: next_ch,
            ops_hash: next_ops_hash,
            total_burn: next_burn_total,
            sortition: true,
            sortition_hash: final_sortition_hash,
            winning_block_txid: winning_block.txid,
            winning_stacks_block_hash: winning_block.block_header_hash,
            index_root: TrieHash::from_empty_data(), // will be overwritten,
            num_sortitions: parent_snapshot.num_sortitions + 1,
            stacks_block_accepted: false,
            stacks_block_height: 0,
            arrival_index: 0,
            canonical_stacks_tip_height: parent_snapshot.canonical_stacks_tip_height,
            canonical_stacks_tip_hash: parent_snapshot.canonical_stacks_tip_hash.clone(),
            canonical_stacks_tip_consensus_hash: parent_snapshot
                .canonical_stacks_tip_consensus_hash
                .clone(),
            sortition_id: my_sortition_id.clone(),
            parent_sortition_id: parent_snapshot.sortition_id.clone(),
            pox_valid: true,
            accumulated_coinbase_ustx,
        })
    }
}

#[cfg(test)]
mod test {
    use address::*;
    use burnchains::tests::*;
    use burnchains::*;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::operations::*;
    use chainstate::stacks::*;
    use util::get_epoch_time_secs;
    use util::hash::hex_bytes;
    use util::vrf::VRFPrivateKey;
    use util::vrf::VRFPublicKey;

    use crate::types::chainstate::BlockHeaderHash;
    use crate::types::chainstate::BurnchainHeaderHash;
    use crate::types::chainstate::VRFSeed;

    use super::*;

    fn test_make_snapshot(
        sort_tx: &mut SortitionHandleTx,
        burnchain: &Burnchain,
        my_sortition_id: &SortitionId,
        my_pox_id: &PoxId,
        parent_snapshot: &BlockSnapshot,
        block_header: &BurnchainBlockHeader,
        burn_dist: &[BurnSamplePoint],
        txids: &Vec<Txid>,
    ) -> Result<BlockSnapshot, db_error> {
        let total_burn = BurnSamplePoint::get_total_burns(burn_dist);
        BlockSnapshot::make_snapshot(
            sort_tx,
            burnchain,
            my_sortition_id,
            my_pox_id,
            parent_snapshot,
            block_header,
            burn_dist,
            txids,
            total_burn,
            0,
        )
    }

    #[test]
    fn make_snapshot_no_sortition() {
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000123",
        )
        .unwrap();
        let first_block_height = 120;

        let burnchain = Burnchain {
            pox_constants: PoxConstants::test_default(),
            peer_version: 0x012345678,
            network_id: 0x9abcdef0,
            chain_name: "bitcoin".to_string(),
            network_name: "testnet".to_string(),
            working_dir: "/nope".to_string(),
            consensus_hash_lifetime: 24,
            stable_confirmations: 7,
            first_block_timestamp: 0,
            first_block_height,
            initial_reward_start_block: first_block_height,
            first_block_hash: first_burn_hash.clone(),
        };

        let mut db = SortitionDB::connect_test(first_block_height, &first_burn_hash).unwrap();

        let empty_block_header = BurnchainBlockHeader {
            block_height: first_block_height + 1,
            block_hash: BurnchainHeaderHash([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0x01, 0x24,
            ]),
            parent_block_hash: first_burn_hash.clone(),
            num_txs: 0,
            timestamp: get_epoch_time_secs(),
        };

        let initial_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();

        let snapshot_no_transactions = {
            let pox_id = PoxId::stubbed();
            let sort_id = SortitionId::stubbed(&empty_block_header.block_hash);
            let mut ic = SortitionHandleTx::begin(&mut db, &sort_id).unwrap();
            let sn = test_make_snapshot(
                &mut ic,
                &burnchain,
                &sort_id,
                &pox_id,
                &initial_snapshot,
                &empty_block_header,
                &vec![],
                &vec![],
            )
            .unwrap();
            sn
        };

        assert!(!snapshot_no_transactions.sortition);
        assert_eq!(snapshot_no_transactions.total_burn, 0);

        let key = LeaderKeyRegisterOp::new_from_secrets(
            &vec![StacksPrivateKey::new()],
            1,
            &AddressHashMode::SerializeP2PKH,
            &VRFPrivateKey::new(),
        )
        .unwrap();

        let empty_burn_point = BurnSamplePoint {
            burns: 0,
            range_start: Uint256::from_u64(0),
            range_end: Uint256([
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF,
            ]),
            candidate: LeaderBlockCommitOp::initial(
                &BlockHeaderHash([1u8; 32]),
                first_block_height + 1,
                &VRFSeed::initial(),
                &key,
                0,
                &(Txid([0; 32]), 0),
                &BurnchainSigner::new_p2pkh(
                    &StacksPublicKey::from_hex(
                        "03ef2340518b5867b23598a9cf74611f8b98064f7d55cdb8c107c67b5efcbc5c77",
                    )
                    .unwrap(),
                ),
            ),
            user_burns: vec![],
        };

        let snapshot_no_burns = {
            let sort_id = SortitionId::stubbed(&empty_block_header.block_hash);
            let pox_id = PoxId::stubbed();
            let mut ic = SortitionHandleTx::begin(&mut db, &sort_id).unwrap();
            let sn = test_make_snapshot(
                &mut ic,
                &burnchain,
                &sort_id,
                &pox_id,
                &initial_snapshot,
                &empty_block_header,
                &vec![empty_burn_point.clone()],
                &vec![key.txid.clone()],
            )
            .unwrap();
            sn
        };

        assert!(!snapshot_no_burns.sortition);
        assert_eq!(snapshot_no_transactions.total_burn, 0);
    }
}
