// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2021 Stacks Open Internet Foundation
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
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::fmt::Write;
use std::sync::mpsc::SyncSender;
use std::time::Duration;

use burnchains::{
    db::{BurnchainBlockData, BurnchainDB, BurnchainDBTransaction, BurnchainHeaderReader},
    Address, Burnchain, BurnchainBlockHeader, Error, PoxConstants, Txid,
};
use chainstate::burn::{
    db::sortdb::SortitionDB,
    operations::leader_block_commit::{RewardSetInfo, BURN_BLOCK_MINED_AT_MODULUS},
    operations::BlockstackOperationType,
    operations::LeaderBlockCommitOp,
    BlockSnapshot, ConsensusHash,
};
use util::db::DBConn;
use util::db::Error as DBError;

use core::StacksEpochId;

use crate::types::chainstate::{
    BlockHeaderHash, BurnchainHeaderHash, PoxId, SortitionId, StacksAddress, StacksBlockHeader,
    StacksBlockId,
};
use crate::util::boot::boot_code_id;

/// Affirmation map entries.  By building on a PoX-mined block,
/// a PoB-mined block (in a PoX reward cycle),
/// or no block in reward cycle _i_, a sortition's miner
/// affirms something about the status of the ancestral anchor blocks.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum AffirmationMapEntry {
    PoxAnchorBlockPresent,
    PoxAnchorBlockAbsent,
    Nothing,
}

impl AffirmationMapEntry {
    pub fn from_chr(c: char) -> Option<AffirmationMapEntry> {
        match c {
            'p' => Some(AffirmationMapEntry::PoxAnchorBlockPresent),
            'a' => Some(AffirmationMapEntry::PoxAnchorBlockAbsent),
            'n' => Some(AffirmationMapEntry::Nothing),
            _ => None,
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct AffirmationMap {
    affirmations: Vec<AffirmationMapEntry>,
}

impl fmt::Display for AffirmationMapEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AffirmationMapEntry::PoxAnchorBlockPresent => write!(f, "p"),
            AffirmationMapEntry::PoxAnchorBlockAbsent => write!(f, "a"),
            AffirmationMapEntry::Nothing => write!(f, "n"),
        }
    }
}

impl fmt::Debug for AffirmationMapEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&format!("{}", &self))
    }
}

impl fmt::Display for AffirmationMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for entry in self.affirmations.iter() {
            write!(f, "{}", &entry)?;
        }
        Ok(())
    }
}

impl fmt::Debug for AffirmationMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl AffirmationMap {
    pub fn new(entries: Vec<AffirmationMapEntry>) -> AffirmationMap {
        AffirmationMap {
            affirmations: entries,
        }
    }

    pub fn empty() -> AffirmationMap {
        AffirmationMap {
            affirmations: vec![],
        }
    }

    pub fn at(&self, reward_cycle: u64) -> Option<AffirmationMapEntry> {
        self.affirmations.get(reward_cycle as usize).cloned()
    }

    pub fn push(&mut self, entry: AffirmationMapEntry) {
        self.affirmations.push(entry)
    }

    pub fn pop(&mut self) -> Option<AffirmationMapEntry> {
        self.affirmations.pop()
    }

    pub fn len(&self) -> usize {
        self.affirmations.len()
    }

    pub fn as_slice(&self) -> &[AffirmationMapEntry] {
        &self.affirmations
    }

    // used to store to database
    pub fn encode(&self) -> String {
        let mut ret = String::with_capacity(self.affirmations.len());
        write!(&mut ret, "{}", self).expect("BUG: failed to serialize affirmations -- likely OOM");
        ret
    }

    // used for database from-row
    pub fn decode(s: &str) -> Option<AffirmationMap> {
        if !s.is_ascii() {
            return None;
        }

        let mut affirmations = Vec::with_capacity(s.len());
        for chr in s.chars() {
            if let Some(next) = AffirmationMapEntry::from_chr(chr) {
                affirmations.push(next);
            } else {
                return None;
            }
        }
        Some(AffirmationMap { affirmations })
    }

    /// Has `other` diverged from `self`?
    /// If `other` contains a reward cycle affirmation that is not present in `self`, then yes.
    /// (Note that this means that if `other` is a prefix of `self`, then no divergence).
    /// Return the index into `other` where the affirmation differs from `self`.
    pub fn find_divergence(&self, other: &AffirmationMap) -> Option<u64> {
        for i in 0..cmp::min(self.len(), other.len()) {
            if self.affirmations[i] != other.affirmations[i] {
                return Some(i as u64);
            }
        }

        if other.len() > self.len() {
            return Some(self.len() as u64);
        }

        None
    }

    /// What is the PoX ID if this affirmation map?
    /// This is a surjective mapping: `n` and `p` are 1, and `a` is 0
    pub fn as_pox_id(&self) -> PoxId {
        let mut pox_id = PoxId::initial();

        // affirmation maps are statements out prepare phases, not about the reward cycle's anchor
        // block status.  So, account for the first reward cycle, which has no anchor block.
        pox_id.extend_with_present_block();

        for affirmation in self.affirmations.iter() {
            match affirmation {
                AffirmationMapEntry::PoxAnchorBlockAbsent => {
                    pox_id.extend_with_not_present_block();
                }
                _ => {
                    pox_id.extend_with_present_block();
                }
            }
        }
        pox_id
    }

    /// What is the weight of this affirmation map?
    /// i.e. how many times did the network either affirm an anchor block, or made no election?
    pub fn weight(&self) -> u64 {
        let mut weight = 0;
        for i in 0..self.len() {
            match self.affirmations[i] {
                AffirmationMapEntry::PoxAnchorBlockAbsent => {}
                _ => {
                    weight += 1;
                }
            }
        }
        weight
    }
}

/// Get a parent/child reward cycle.  Only return Some(..) if the reward cycle is known for both --
/// i.e. their block heights are plausible.
pub fn get_parent_child_reward_cycles(
    parent: &LeaderBlockCommitOp,
    block_commit: &LeaderBlockCommitOp,
    burnchain: &Burnchain,
) -> Option<(u64, u64)> {
    let child_reward_cycle = match burnchain.block_height_to_reward_cycle(block_commit.block_height)
    {
        Some(crc) => crc,
        None => return None,
    };

    let parent_reward_cycle = match burnchain.block_height_to_reward_cycle(parent.block_height) {
        Some(prc) => prc,
        None => {
            if parent.block_height == 0 && parent.vtxindex == 0 {
                // this is a first block commit
                0
            } else {
                return None;
            }
        }
    };

    test_debug!(
        "{},{} is rc={},rc={}",
        parent.block_height,
        block_commit.block_height,
        parent_reward_cycle,
        child_reward_cycle
    );
    Some((parent_reward_cycle, child_reward_cycle))
}

/// Read a range of blockstack operations for a prepare phase of a given reward cycle.
/// Only includes block-commits
pub fn read_prepare_phase_commits<'a, B: BurnchainHeaderReader>(
    burnchain_tx: &BurnchainDBTransaction<'a>,
    indexer: &B,
    pox_consts: &PoxConstants,
    first_block_height: u64,
    reward_cycle: u64,
) -> Result<Vec<Vec<LeaderBlockCommitOp>>, Error> {
    let start_height = pox_consts
        .reward_cycle_to_block_height(first_block_height, reward_cycle + 1)
        - (pox_consts.prepare_length as u64);
    let end_height = start_height + (pox_consts.prepare_length as u64);
    let headers = indexer.read_burnchain_headers(start_height, end_height)?;
    let _num_headers = headers.len();

    let mut ret = vec![];
    for header in headers.into_iter() {
        let blk = BurnchainDB::get_burnchain_block(&burnchain_tx.conn(), &header.block_hash)
            .expect(&format!(
                "BUG: failed to load prepare-phase block {} ({})",
                &header.block_hash, header.block_height
            ));

        let mut block_ops = vec![];
        for op in blk.ops.into_iter() {
            assert!(pox_consts.is_in_prepare_phase(first_block_height, op.block_height()));
            match op {
                BlockstackOperationType::LeaderBlockCommit(opdata) => {
                    // basic validity filtering
                    if opdata.block_height < first_block_height {
                        test_debug!("Skip too-early block commit");
                        continue;
                    }
                    if (opdata.parent_block_ptr as u64) < first_block_height {
                        if opdata.parent_block_ptr != 0 || opdata.parent_vtxindex != 0 {
                            test_debug!("Skip orphaned block-commit");
                            continue;
                        }
                    }
                    if opdata.block_height <= opdata.parent_block_ptr as u64 {
                        test_debug!("Skip block-commit whose 'parent' comes at or after it");
                        continue;
                    }
                    if opdata.burn_fee == 0 {
                        test_debug!("Skip block-commit without burn");
                        continue;
                    }
                    block_ops.push(opdata);
                }
                _ => {
                    continue;
                }
            }
        }
        block_ops.sort_by(|op1, op2| {
            if op1.block_height != op2.block_height {
                op1.block_height.cmp(&op2.block_height)
            } else {
                op1.vtxindex.cmp(&op2.vtxindex)
            }
        });
        ret.push(block_ops);
    }

    test_debug!(
        "Read {} headers, {} prepare-phase commits from reward cycle {} ({}-{})",
        _num_headers,
        ret.len(),
        reward_cycle,
        start_height,
        end_height
    );
    Ok(ret)
}

/// Find all referenced parent block-commits already in the burnchain DB, so we can extract their VRF seeds.
pub fn read_parent_block_commits<'a, B: BurnchainHeaderReader>(
    burnchain_tx: &BurnchainDBTransaction<'a>,
    indexer: &B,
    prepare_phase_ops: &Vec<Vec<LeaderBlockCommitOp>>,
) -> Result<Vec<LeaderBlockCommitOp>, Error> {
    let mut parents = HashMap::new();
    for ops in prepare_phase_ops.iter() {
        for opdata in ops.iter() {
            let hdr =
                if let Some(hdr) = indexer.read_burnchain_header(opdata.parent_block_ptr as u64)? {
                    hdr
                } else {
                    test_debug!(
                        "Orphan block commit {},{},{}: no such block {}",
                        &opdata.txid,
                        opdata.block_height,
                        opdata.vtxindex,
                        opdata.parent_block_ptr
                    );
                    continue;
                };

            test_debug!("Get header at {}: {:?}", opdata.parent_block_ptr, &hdr);
            assert_eq!(hdr.block_height, opdata.parent_block_ptr as u64);

            let mut found = false;
            let blk = BurnchainDB::get_burnchain_block(burnchain_tx.conn(), &hdr.block_hash)
                .expect(&format!(
                    "BUG: failed to load existing block {} ({})",
                    &hdr.block_hash, &hdr.block_height
                ));

            for parent_op in blk.ops.into_iter() {
                if let BlockstackOperationType::LeaderBlockCommit(parent_opdata) = parent_op {
                    if parent_opdata.vtxindex == opdata.parent_vtxindex as u32 {
                        test_debug!(
                            "Parent of {},{},{} is {},{},{}",
                            &opdata.txid,
                            opdata.block_height,
                            opdata.vtxindex,
                            &parent_opdata.txid,
                            parent_opdata.block_height,
                            parent_opdata.vtxindex
                        );
                        parents.insert(parent_opdata.txid.clone(), parent_opdata);
                        found = true;
                    }
                }
            }
            if !found {
                test_debug!(
                    "Orphan block commit {},{},{}",
                    &opdata.txid,
                    opdata.block_height,
                    opdata.vtxindex
                );
            }
        }
    }
    let mut parent_list: Vec<_> = parents.into_iter().map(|(_, cmt)| cmt).collect();
    parent_list.sort_by(|a, b| {
        if a.block_height != b.block_height {
            a.block_height.cmp(&b.block_height)
        } else {
            a.vtxindex.cmp(&b.vtxindex)
        }
    });

    test_debug!("Read {} parent block-commits", parent_list.len());
    Ok(parent_list)
}

/// Given a list of prepare-phase block-commits, and a list of parent commits, filter out and remove
/// the prepare-phase commits that _don't_ have a parent.
pub fn filter_orphan_block_commits(
    parents: &Vec<LeaderBlockCommitOp>,
    prepare_phase_ops: Vec<Vec<LeaderBlockCommitOp>>,
) -> Vec<Vec<LeaderBlockCommitOp>> {
    let mut parent_set = HashSet::new();
    for parent in parents.iter() {
        parent_set.insert((parent.block_height, parent.vtxindex));
    }
    for prepare_phase_block in prepare_phase_ops.iter() {
        for opdata in prepare_phase_block.iter() {
            parent_set.insert((opdata.block_height, opdata.vtxindex));
        }
    }

    prepare_phase_ops
        .into_iter()
        .map(|prepare_phase_block| {
            prepare_phase_block
                .into_iter()
                .filter(|opdata| {
                    if parent_set.contains(&(
                        opdata.parent_block_ptr as u64,
                        opdata.parent_vtxindex as u32,
                    )) {
                        true
                    } else {
                        test_debug!(
                            "Ignore invalid block-commit {},{} ({}): no parent {},{}",
                            opdata.block_height,
                            opdata.vtxindex,
                            &opdata.txid,
                            opdata.parent_block_ptr,
                            opdata.parent_vtxindex
                        );
                        false
                    }
                })
                .collect()
        })
        .collect()
}

/// Given a list of prepare-phase block-commits, filter out the ones that don't have correct burn
/// modulii.
pub fn filter_missed_block_commits(
    prepare_phase_ops: Vec<Vec<LeaderBlockCommitOp>>,
) -> Vec<Vec<LeaderBlockCommitOp>> {
    prepare_phase_ops
        .into_iter()
        .map(|commits| {
            commits
                .into_iter()
                .filter(|cmt| {
                    let intended_modulus =
                        (cmt.burn_block_mined_at() + 1) % BURN_BLOCK_MINED_AT_MODULUS;
                    let actual_modulus = cmt.block_height % BURN_BLOCK_MINED_AT_MODULUS;
                    if actual_modulus == intended_modulus {
                        true
                    } else {
                        test_debug!(
                            "Ignore invalid block-commit {},{} ({}): {} != {}",
                            cmt.block_height,
                            cmt.vtxindex,
                            &cmt.txid,
                            actual_modulus,
                            intended_modulus
                        );
                        false
                    }
                })
                .collect()
        })
        .collect()
}

/// Given a list of block-commits in the prepare-phase, find the block-commit outside the
/// prepare-phase which must be the anchor block, if it exists at all.  This is always
/// the block-commit that has the most cumulative BTC committed behind it (and the highest
/// such in the event of a tie), as well as at least `anchor_threshold` confirmations.  If the anchor block
/// commit is found, return the descendancy matrix for it as well.
/// Returns Some(the winning block commit, descendancy matrix, total confirmations, total burnt) if
/// there's an anchor block commit.
/// Returns None otherwise
pub fn find_heaviest_block_commit<'a, B: BurnchainHeaderReader>(
    burnchain_tx: &BurnchainDBTransaction<'a>,
    indexer: &B,
    prepare_ops: &Vec<Vec<LeaderBlockCommitOp>>,
    anchor_threshold: u32,
) -> Result<Option<(LeaderBlockCommitOp, Vec<Vec<bool>>, u64, u64)>, DBError> {
    // sanity check -- must be in order by block height and vtxindex
    for prepare_block_ops in prepare_ops.iter() {
        let mut expected_block_height = None;
        let mut last_vtxindex = None;
        for opdata in prepare_block_ops.iter() {
            if let Some(expected_block_height) = expected_block_height.as_ref() {
                assert_eq!(expected_block_height, &opdata.block_height);
            } else {
                expected_block_height = Some(opdata.block_height);
            }

            if let Some(last_vtxindex) = last_vtxindex.as_mut() {
                assert!(*last_vtxindex < opdata.vtxindex);
                *last_vtxindex = opdata.vtxindex;
            } else {
                last_vtxindex = Some(opdata.vtxindex);
            }
            test_debug!(
                "Prepare-phase block-commit {},{}: {}",
                opdata.block_height,
                opdata.vtxindex,
                &opdata.txid
            );
        }
    }

    // map (block_height, vtxindex) to (parent_block_height, parent_vtxindex)
    let mut parents = BTreeMap::new();

    // map (block_height, vtxindex) to (non-prepare-ancestor-height, non-prepare-ancestor-vtxindex)
    let mut ancestors = BTreeMap::new();

    // map (non-prepare-ancestor-height, non-prepare-ancestor-vtxindex) to (set-of-block-heights, total_burnt)
    // that contain descendants
    let mut ancestor_confirmations: BTreeMap<(u64, u32), (HashSet<u64>, u64)> = BTreeMap::new();

    // calculate each block-commit's parents
    for prepare_block_ops in prepare_ops.iter() {
        for opdata in prepare_block_ops.iter() {
            parents.insert(
                (opdata.block_height, opdata.vtxindex),
                (
                    opdata.parent_block_ptr as u64,
                    opdata.parent_vtxindex as u32,
                ),
            );
        }
    }

    // calculate the ancestor map -- find the highest non-prepare-phase ancestor for each prepare-phase block-commit.
    for prepare_block_ops in prepare_ops.iter().rev() {
        for opdata in prepare_block_ops.iter() {
            let mut cursor = (opdata.block_height, opdata.vtxindex);
            while let Some((parent_block, parent_vtxindex)) = parents.get(&cursor) {
                cursor = (*parent_block, *parent_vtxindex);
            }
            ancestors.insert((opdata.block_height, opdata.vtxindex), (cursor.0, cursor.1));
        }
    }

    // calculate the ancestor confirmations -- figure out how many distinct blocks contain
    // block-commits that descend from each pre-prepare-phase ancestor
    for prepare_block_ops in prepare_ops.iter() {
        for opdata in prepare_block_ops.iter() {
            if let Some((ancestor_height, ancestor_vtxindex)) =
                ancestors.get(&(opdata.block_height, opdata.vtxindex))
            {
                if let Some((ref mut confirmed_block_set, ref mut ancestor_burnt)) =
                    ancestor_confirmations.get_mut(&(*ancestor_height, *ancestor_vtxindex))
                {
                    confirmed_block_set.insert(opdata.block_height);
                    *ancestor_burnt += opdata.burn_fee;
                } else {
                    let mut block_set = HashSet::new();
                    block_set.insert(opdata.block_height);
                    ancestor_confirmations.insert(
                        (*ancestor_height, *ancestor_vtxindex),
                        (block_set, opdata.burn_fee),
                    );
                }
            }
        }
    }

    test_debug!("parents = {:?}", &parents);
    test_debug!("ancestors = {:?}", &ancestors);
    test_debug!("ancestor_confirmations = {:?}", &ancestor_confirmations);

    if ancestor_confirmations.len() == 0 {
        // empty prepare phase
        test_debug!("Prepare-phase has no block-commits");
        return Ok(None);
    }

    // find the ancestors with at least $anchor_threshold confirmations, and pick the one that has the
    // most total BTC.  Break ties by ancestor order -- highest ancestor commit wins.
    let mut ancestor_block = 0;
    let mut ancestor_vtxindex = 0;
    let mut most_burnt = 0;
    let mut most_confs = 0;

    // consider ancestor candidates in _highest_-first order
    for ((height, vtxindex), (block_set, burnt)) in ancestor_confirmations.iter().rev() {
        let confs = block_set.len() as u64;
        if confs < anchor_threshold.into() {
            continue;
        }

        // only consider an earlier ancestor if it burned more than the candidate
        if *burnt > most_burnt {
            most_burnt = *burnt;
            most_confs = confs;
            ancestor_block = *height;
            ancestor_vtxindex = *vtxindex;
        }
    }

    if most_burnt == 0 {
        // no anchor block possible -- no block-commit has enough confirmations
        test_debug!("No block-commit has enough support to be an anchor block");
        return Ok(None);
    }

    // find the ancestor that this tip confirms
    let heaviest_ancestor_header = indexer
        .read_burnchain_headers(ancestor_block, ancestor_block + 1)?
        .first()
        .expect(&format!(
            "BUG: no block headers for height {}",
            ancestor_block
        ))
        .to_owned();

    let heaviest_ancestor_block =
        BurnchainDB::get_burnchain_block(burnchain_tx.conn(), &heaviest_ancestor_header.block_hash)
            .expect(&format!(
                "BUG: no ancestor block {:?} ({})",
                &heaviest_ancestor_header.block_hash, heaviest_ancestor_header.block_height
            ));

    // find the PoX anchor block-commit, if it exists at all
    // (note that it may not -- a rich attacker can force F*w confirmations with lots of BTC on a
    // commit that was never mined).
    for block_op in heaviest_ancestor_block.ops.into_iter() {
        if let BlockstackOperationType::LeaderBlockCommit(opdata) = block_op {
            if opdata.block_height == ancestor_block && opdata.vtxindex == ancestor_vtxindex {
                // found
                debug!(
                    "PoX anchor block-commit {},{},{} has {} burnt, {} confs",
                    &opdata.txid, opdata.block_height, opdata.vtxindex, most_burnt, most_confs
                );

                // sanity check -- there should be exactly as many confirmations on the suspected
                // anchor block as there are distinct descendancies.
                let mut conf_count = 0;

                // sanity check -- there should be exactly as many BTC burnt for the suspected
                // anchor block as the most_burnt.
                let mut burn_count = 0;

                let mut descendancy = Vec::with_capacity(prepare_ops.len());
                for prepare_block_ops in prepare_ops.iter() {
                    let mut block_descendancy = Vec::with_capacity(prepare_ops.len());
                    let mut found_conf = false;
                    for opdata in prepare_block_ops.iter() {
                        if let Some((op_ancestor_height, op_ancestor_vtxindex, ..)) =
                            ancestors.get(&(opdata.block_height, opdata.vtxindex))
                        {
                            if *op_ancestor_height == ancestor_block
                                && *op_ancestor_vtxindex == ancestor_vtxindex
                            {
                                debug!("Block-commit {},{} descends from likely PoX anchor block {},{}", opdata.block_height, opdata.vtxindex, op_ancestor_height, op_ancestor_vtxindex);
                                block_descendancy.push(true);
                                if !found_conf {
                                    conf_count += 1;
                                    found_conf = true;
                                }
                                burn_count += opdata.burn_fee;
                            } else {
                                debug!("Block-commit {},{} does NOT descend from likely PoX anchor block {},{}", opdata.block_height, opdata.vtxindex, ancestor_block, ancestor_vtxindex);
                                block_descendancy.push(false);
                            }
                        } else {
                            debug!("Block-commit {},{} does NOT descend from likely PoX anchor block {},{}", opdata.block_height, opdata.vtxindex, ancestor_block, ancestor_vtxindex);
                            block_descendancy.push(false);
                        }
                    }
                    descendancy.push(block_descendancy);
                }

                assert_eq!(conf_count, most_confs);
                assert_eq!(burn_count, most_burnt);

                return Ok(Some((opdata, descendancy, most_confs, most_burnt)));
            }
        }
    }

    warn!("Evil miners confirmed a non-existant PoX anchor block!");
    Ok(None)
}

/// Find the PoX anchor block selected in a reward cycle, if it exists.  This is the heaviest F*w-confirmed
/// block-commit before the prepare-phase of this reward cycle, provided that it is not already an
/// anchor block for some other reward cycle.  Note that the anchor block found will be the anchor
/// block for the *next* reward cycle.
/// Returns:
///     (a) the list of block-commits, grouped by block and ordered by vtxindex, in this prepare phase
///     (b) the PoX anchor block-commit, if it exists, and
///     (c) the descendancy data for the prepare phase.  Descendency[i][j] is true if the jth
///     block-commit in the ith block in the prepare phase descends from the anchor block, or False
///     if not.
pub fn find_pox_anchor_block<'a, B: BurnchainHeaderReader>(
    burnchain_tx: &BurnchainDBTransaction<'a>,
    reward_cycle: u64,
    indexer: &B,
    burnchain: &Burnchain,
) -> Result<
    (
        Vec<Vec<LeaderBlockCommitOp>>,
        Option<(LeaderBlockCommitOp, Vec<Vec<bool>>)>,
    ),
    Error,
> {
    let pox_consts = &burnchain.pox_constants;
    let first_block_height = burnchain.first_block_height;

    let prepare_ops = read_prepare_phase_commits(
        burnchain_tx,
        indexer,
        pox_consts,
        first_block_height,
        reward_cycle,
    )?;
    test_debug!("{} prepare-phase commits", prepare_ops.len());

    let parent_commits = read_parent_block_commits(burnchain_tx, indexer, &prepare_ops)?;
    test_debug!("{} parent block-commits", parent_commits.len());

    let prepare_ops_no_orphans = filter_orphan_block_commits(&parent_commits, prepare_ops);
    test_debug!(
        "{} prepare-phase block-commits that have parents",
        prepare_ops_no_orphans.len()
    );

    let prepare_ops_valid = filter_missed_block_commits(prepare_ops_no_orphans);
    test_debug!(
        "{} prepare-phase block-commits that have parents and are on-time",
        prepare_ops_valid.len()
    );

    let anchor_block_and_descendancy_opt = find_heaviest_block_commit(
        &burnchain_tx,
        indexer,
        &prepare_ops_valid,
        burnchain.pox_constants.anchor_threshold,
    )?;
    if let Some((ref anchor_block_commit, ..)) = anchor_block_and_descendancy_opt.as_ref() {
        // cannot have been an anchor block in some other reward cycle
        let md = BurnchainDB::get_commit_metadata(
            burnchain_tx.conn(),
            &anchor_block_commit.burn_header_hash,
            &anchor_block_commit.txid,
        )?
        .expect("BUG: anchor block commit has not metadata");

        if let Some(rc) = md.anchor_block {
            warn!(
                "Block-commit {} is already an anchor block for reward cycle {}",
                &anchor_block_commit.txid, rc
            );
            return Ok((prepare_ops_valid, None));
        }
    }

    if anchor_block_and_descendancy_opt.is_some() {
        test_debug!(
            "Selected an anchor block in prepare phase of reward cycle {}",
            reward_cycle
        );
    } else {
        test_debug!(
            "Did NOT select an anchor block in prepare phase of reward cycle {}",
            reward_cycle
        );
    }

    Ok((
        prepare_ops_valid,
        anchor_block_and_descendancy_opt
            .map(|(anchor_block_commit, descendancy, ..)| (anchor_block_commit, descendancy)),
    ))
}

/// Update a completed reward cycle's affirmation maps
pub fn update_pox_affirmation_maps<B: BurnchainHeaderReader>(
    burnchain_db: &mut BurnchainDB,
    indexer: &B,
    reward_cycle: u64,
    burnchain: &Burnchain,
) -> Result<(), Error> {
    debug!("Process PoX affirmations for reward cycle {}", reward_cycle);

    let tx = burnchain_db.tx_begin()?;

    let (prepare_ops, pox_anchor_block_info_opt) =
        find_pox_anchor_block(&tx, reward_cycle, indexer, burnchain)?;

    if let Some((anchor_block, descendancy)) = pox_anchor_block_info_opt.clone() {
        debug!(
            "PoX anchor block elected in reward cycle {} for reward cycle {} is {}",
            reward_cycle,
            reward_cycle + 1,
            &anchor_block.block_header_hash
        );

        // anchor block found for this upcoming reward cycle
        tx.set_anchor_block(&anchor_block, reward_cycle + 1)?;
        assert_eq!(descendancy.len(), prepare_ops.len());

        // mark the prepare-phase commits that elected this next reward cycle's anchor block as
        // having descended or not descended from this anchor block.
        for (block_idx, block_ops) in prepare_ops.iter().enumerate() {
            assert_eq!(block_ops.len(), descendancy[block_idx].len());

            for (tx_idx, tx_op) in block_ops.iter().enumerate() {
                test_debug!(
                    "Make affirmation map for block-commit at {},{}",
                    tx_op.block_height,
                    tx_op.vtxindex
                );
                tx.make_prepare_phase_affirmation_map(
                    indexer,
                    burnchain,
                    reward_cycle + 1,
                    tx_op,
                    Some(&anchor_block),
                    descendancy[block_idx][tx_idx],
                )?;
            }
        }
    } else {
        debug!("PoX anchor block selected in reward cycle {} is None. Reward cycle {} has no anchor block", reward_cycle, reward_cycle + 1);

        // anchor block not found for this upcoming reward cycle
        tx.clear_anchor_block(reward_cycle + 1)?;

        // mark the prepare-phase commits that did NOT elect this next reward cycle's anchor
        // block as NOT having descended from any anchor block (since one was not chosen)
        for block_ops in prepare_ops.iter() {
            for tx_op in block_ops.iter() {
                test_debug!(
                    "Make affirmation map for block-commit at {},{}",
                    tx_op.block_height,
                    tx_op.vtxindex
                );
                tx.make_prepare_phase_affirmation_map(
                    indexer,
                    burnchain,
                    reward_cycle + 1,
                    tx_op,
                    None,
                    false,
                )?;
            }
        }
    }

    tx.commit()?;
    debug!(
        "Processed PoX affirmations for reward cycle {}",
        reward_cycle
    );

    Ok(())
}
