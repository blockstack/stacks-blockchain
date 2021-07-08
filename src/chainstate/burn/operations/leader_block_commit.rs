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

use std::io::{Read, Write};

use crate::codec::{write_next, Error as codec_error, StacksMessageCodec};
use crate::types::proof::TrieHash;
use address::AddressHashMode;
use burnchains::bitcoin::BitcoinNetworkType;
use burnchains::Address;
use burnchains::Burnchain;
use burnchains::BurnchainBlockHeader;
use burnchains::Txid;
use burnchains::{BurnchainRecipient, BurnchainSigner};
use burnchains::{BurnchainTransaction, PublicKey};
use chainstate::burn::db::sortdb::{SortitionDB, SortitionHandleTx};
use chainstate::burn::operations::Error as op_error;
use chainstate::burn::operations::{
    parse_u16_from_be, parse_u32_from_be, BlockstackOperationType, LeaderBlockCommitOp,
    LeaderKeyRegisterOp, UserBurnSupportOp,
};
use chainstate::burn::ConsensusHash;
use chainstate::burn::Opcodes;
use chainstate::burn::SortitionId;
use chainstate::stacks::index::storage::TrieFileStorage;
use chainstate::stacks::{StacksPrivateKey, StacksPublicKey};
use net::Error as net_error;
use util::hash::to_hex;
use util::log;
use util::vrf::{VRFPrivateKey, VRFPublicKey, VRF};

use crate::types::chainstate::{BlockHeaderHash, BurnchainHeaderHash, StacksAddress, VRFSeed};

// return type from parse_data below
struct ParsedData {
    block_header_hash: BlockHeaderHash,
    new_seed: VRFSeed,
    parent_block_ptr: u32,
    parent_vtxindex: u16,
    key_block_ptr: u32,
    key_vtxindex: u16,
    burn_parent_modulus: u8,
    memo: u8,
}

pub static OUTPUTS_PER_COMMIT: usize = 2;
pub static BURN_BLOCK_MINED_AT_MODULUS: u64 = 5;

impl LeaderBlockCommitOp {
    #[cfg(test)]
    pub fn initial(
        block_header_hash: &BlockHeaderHash,
        block_height: u64,
        new_seed: &VRFSeed,
        paired_key: &LeaderKeyRegisterOp,
        burn_fee: u64,
        input: &(Txid, u32),
        apparent_sender: &BurnchainSigner,
    ) -> LeaderBlockCommitOp {
        LeaderBlockCommitOp {
            sunset_burn: 0,
            block_height: block_height,
            burn_parent_modulus: if block_height > 0 {
                ((block_height - 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8
            } else {
                BURN_BLOCK_MINED_AT_MODULUS as u8 - 1
            },
            new_seed: new_seed.clone(),
            key_block_ptr: paired_key.block_height as u32,
            key_vtxindex: paired_key.vtxindex as u16,
            parent_block_ptr: 0,
            parent_vtxindex: 0,
            memo: vec![0x00],
            burn_fee: burn_fee,
            input: input.clone(),
            block_header_hash: block_header_hash.clone(),
            commit_outs: vec![],
            apparent_sender: apparent_sender.clone(),

            // to be filled in
            txid: Txid([0u8; 32]),
            vtxindex: 0,
            burn_header_hash: BurnchainHeaderHash::zero(),
        }
    }

    #[cfg(test)]
    pub fn new(
        block_header_hash: &BlockHeaderHash,
        block_height: u64,
        new_seed: &VRFSeed,
        parent: &LeaderBlockCommitOp,
        key_block_ptr: u32,
        key_vtxindex: u16,
        burn_fee: u64,
        input: &(Txid, u32),
        apparent_sender: &BurnchainSigner,
    ) -> LeaderBlockCommitOp {
        LeaderBlockCommitOp {
            sunset_burn: 0,
            new_seed: new_seed.clone(),
            key_block_ptr: key_block_ptr,
            key_vtxindex: key_vtxindex,
            parent_block_ptr: parent.block_height as u32,
            parent_vtxindex: parent.vtxindex as u16,
            memo: vec![],
            burn_fee: burn_fee,
            input: input.clone(),
            block_header_hash: block_header_hash.clone(),
            commit_outs: vec![],
            apparent_sender: apparent_sender.clone(),

            // to be filled in
            txid: Txid([0u8; 32]),
            vtxindex: 0,
            block_height: 0,
            burn_parent_modulus: BURN_BLOCK_MINED_AT_MODULUS as u8 - 1,

            burn_header_hash: BurnchainHeaderHash::zero(),
        }
    }

    #[cfg(test)]
    pub fn set_burn_height(&mut self, height: u64) {
        self.block_height = height;
        self.burn_parent_modulus = if height > 0 {
            (height - 1) % BURN_BLOCK_MINED_AT_MODULUS
        } else {
            BURN_BLOCK_MINED_AT_MODULUS - 1
        } as u8;
    }

    pub fn expected_chained_utxo(burn_only: bool) -> u32 {
        if burn_only {
            2 // if sunset has occurred, or we're in the prepare phase, then chained commits should spend the output after the burn commit
        } else {
            // otherwise, it's the output after the last PoX output
            (OUTPUTS_PER_COMMIT as u32) + 1
        }
    }

    pub fn burn_block_mined_at(&self) -> u64 {
        self.burn_parent_modulus as u64 % BURN_BLOCK_MINED_AT_MODULUS
    }

    fn parse_data(data: &Vec<u8>) -> Option<ParsedData> {
        /*
            Wire format:
            0      2  3            35               67     71     73    77   79     80
            |------|--|-------------|---------------|------|------|-----|-----|-----|
             magic  op   block hash     new seed     parent parent key   key    burn_block_parent modulus
                                                     block  txoff  block txoff

             Note that `data` is missing the first 3 bytes -- the magic and op have been stripped

             The values parent-block, parent-txoff, key-block, and key-txoff are in network byte order.

             parent-delta and parent-txoff will both be 0 if this block builds off of the genesis block.
        */

        if data.len() < 77 {
            // too short
            warn!(
                "LEADER_BLOCK_COMMIT payload is malformed ({} bytes)",
                data.len()
            );
            return None;
        }

        let block_header_hash = BlockHeaderHash::from_bytes(&data[0..32]).unwrap();
        let new_seed = VRFSeed::from_bytes(&data[32..64]).unwrap();
        let parent_block_ptr = parse_u32_from_be(&data[64..68]).unwrap();
        let parent_vtxindex = parse_u16_from_be(&data[68..70]).unwrap();
        let key_block_ptr = parse_u32_from_be(&data[70..74]).unwrap();
        let key_vtxindex = parse_u16_from_be(&data[74..76]).unwrap();

        let burn_parent_modulus_and_memo_byte = data[76];

        let burn_parent_modulus = ((burn_parent_modulus_and_memo_byte & 0b111) as u64
            % BURN_BLOCK_MINED_AT_MODULUS) as u8;
        let memo = (burn_parent_modulus_and_memo_byte >> 3) & 0x1f;

        Some(ParsedData {
            block_header_hash,
            new_seed,
            parent_block_ptr,
            parent_vtxindex,
            key_block_ptr,
            key_vtxindex,
            burn_parent_modulus,
            memo,
        })
    }

    pub fn from_tx(
        burnchain: &Burnchain,
        block_header: &BurnchainBlockHeader,
        tx: &BurnchainTransaction,
    ) -> Result<LeaderBlockCommitOp, op_error> {
        LeaderBlockCommitOp::parse_from_tx(
            burnchain,
            block_header.block_height,
            &block_header.block_hash,
            tx,
        )
    }

    pub fn is_parent_genesis(&self) -> bool {
        self.parent_block_ptr == 0 && self.parent_vtxindex == 0
    }

    /// parse a LeaderBlockCommitOp
    /// `pox_sunset_ht` is the height at which PoX *disables*
    pub fn parse_from_tx(
        burnchain: &Burnchain,
        block_height: u64,
        block_hash: &BurnchainHeaderHash,
        tx: &BurnchainTransaction,
    ) -> Result<LeaderBlockCommitOp, op_error> {
        // can't be too careful...
        let mut outputs = tx.get_recipients();

        if tx.num_signers() == 0 {
            warn!(
                "Invalid tx: inputs: {}, outputs: {}",
                tx.num_signers(),
                outputs.len()
            );
            return Err(op_error::InvalidInput);
        }

        if outputs.len() == 0 {
            warn!(
                "Invalid tx: inputs: {}, outputs: {}",
                tx.num_signers(),
                outputs.len()
            );
            return Err(op_error::InvalidInput);
        }

        if tx.opcode() != Opcodes::LeaderBlockCommit as u8 {
            warn!("Invalid tx: invalid opcode {}", tx.opcode());
            return Err(op_error::InvalidInput);
        };

        let data = LeaderBlockCommitOp::parse_data(&tx.data()).ok_or_else(|| {
            warn!("Invalid tx data");
            op_error::ParseError
        })?;

        // basic sanity checks
        if data.parent_block_ptr == 0 {
            if data.parent_vtxindex != 0 {
                warn!("Invalid tx: parent block back-pointer must be positive");
                return Err(op_error::ParseError);
            }
            // if parent block ptr and parent vtxindex are both 0, then this block's parent is
            // the genesis block.
        }

        if data.parent_block_ptr as u64 >= block_height {
            warn!(
                "Invalid tx: parent block back-pointer {} exceeds block height {}",
                data.parent_block_ptr, block_height
            );
            return Err(op_error::ParseError);
        }

        if data.key_block_ptr == 0 {
            warn!("Invalid tx: key block back-pointer must be positive");
            return Err(op_error::ParseError);
        }

        if data.key_block_ptr as u64 >= block_height {
            warn!(
                "Invalid tx: key block back-pointer {} exceeds block height {}",
                data.key_block_ptr, block_height
            );
            return Err(op_error::ParseError);
        }

        // check if we've reached PoX disable
        let (commit_outs, sunset_burn, burn_fee) = if block_height
            >= burnchain.pox_constants.sunset_end
        {
            // should be only one burn output
            if !outputs[0].address.is_burn() {
                return Err(op_error::BlockCommitBadOutputs);
            }
            let BurnchainRecipient { address, amount } = outputs.remove(0);
            (vec![address], 0, amount)
        // check if we're in a prepare phase
        } else if burnchain.is_in_prepare_phase(block_height) {
            // should be only one burn output
            if !outputs[0].address.is_burn() {
                return Err(op_error::BlockCommitBadOutputs);
            }
            let BurnchainRecipient { address, amount } = outputs.remove(0);
            (vec![address], 0, amount)
        } else {
            // check if this transaction provided a sunset burn
            let sunset_burn = tx.get_burn_amount();

            let mut commit_outs = vec![];
            let mut pox_fee = None;
            for (ix, output) in outputs.into_iter().enumerate() {
                // only look at the first OUTPUTS_PER_COMMIT outputs
                if ix >= OUTPUTS_PER_COMMIT {
                    break;
                }
                // all pox outputs must have the same fee
                if let Some(pox_fee) = pox_fee {
                    if output.amount != pox_fee {
                        warn!("Invalid commit tx: different output amounts for different PoX reward addresses");
                        return Err(op_error::ParseError);
                    }
                } else {
                    pox_fee.replace(output.amount);
                }
                commit_outs.push(output.address);
            }

            if commit_outs.len() != OUTPUTS_PER_COMMIT {
                warn!("Invalid commit tx: {} commit addresses, but {} PoX addresses should be committed to", commit_outs.len(), OUTPUTS_PER_COMMIT);
                return Err(op_error::InvalidInput);
            }

            // compute the total amount transfered/burned, and check that the burn amount
            //   is expected given the amount transfered.
            let burn_fee = pox_fee
                .expect("A 0-len output should have already errored")
                .checked_mul(OUTPUTS_PER_COMMIT as u64) // total commitment is the pox_amount * outputs
                .ok_or_else(|| op_error::ParseError)?;

            if burn_fee == 0 {
                warn!("Invalid commit tx: burn/transfer amount is 0");
                return Err(op_error::ParseError);
            }

            (commit_outs, sunset_burn, burn_fee)
        };

        let input = tx
            .get_input_tx_ref(0)
            .expect("UNREACHABLE: checked that inputs > 0")
            .clone();

        let apparent_sender = tx
            .get_signer(0)
            .expect("UNREACHABLE: checked that inputs > 0");

        Ok(LeaderBlockCommitOp {
            block_header_hash: data.block_header_hash,
            new_seed: data.new_seed,
            parent_block_ptr: data.parent_block_ptr,
            parent_vtxindex: data.parent_vtxindex,
            key_block_ptr: data.key_block_ptr,
            key_vtxindex: data.key_vtxindex,
            memo: vec![data.memo],
            burn_parent_modulus: data.burn_parent_modulus,

            commit_outs,
            sunset_burn,
            burn_fee,
            input,
            apparent_sender,

            txid: tx.txid(),
            vtxindex: tx.vtxindex(),
            block_height: block_height,
            burn_header_hash: block_hash.clone(),
        })
    }

    /// are all the outputs for this block commit burns?
    pub fn all_outputs_burn(&self) -> bool {
        self.commit_outs
            .iter()
            .fold(true, |previous_is_burn, output_addr| {
                previous_is_burn && output_addr.is_burn()
            })
    }

    pub fn spent_txid(&self) -> &Txid {
        &self.input.0
    }

    pub fn spent_output(&self) -> u32 {
        self.input.1
    }

    pub fn is_first_block(&self) -> bool {
        self.parent_block_ptr == 0 && self.parent_vtxindex == 0
    }
}

impl StacksMessageCodec for LeaderBlockCommitOp {
    /*
        Wire format:

        0      2  3            35               67     71     73    77   79     80
        |------|--|-------------|---------------|------|------|-----|-----|-----|
         magic  op   block hash     new seed     parent parent key   key   burn parent modulus
                                                block  txoff  block txoff
    */
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        write_next(fd, &(Opcodes::LeaderBlockCommit as u8))?;
        write_next(fd, &self.block_header_hash)?;
        fd.write_all(&self.new_seed.as_bytes()[..])
            .map_err(codec_error::WriteError)?;
        write_next(fd, &self.parent_block_ptr)?;
        write_next(fd, &self.parent_vtxindex)?;
        write_next(fd, &self.key_block_ptr)?;
        write_next(fd, &self.key_vtxindex)?;
        let memo_burn_parent_modulus =
            (self.memo.get(0).copied().unwrap_or(0x00) << 3) + (self.burn_parent_modulus & 0b111);
        write_next(fd, &memo_burn_parent_modulus)?;
        Ok(())
    }

    fn consensus_deserialize<R: Read>(_fd: &mut R) -> Result<LeaderBlockCommitOp, codec_error> {
        // Op deserialized through burchain indexer
        unimplemented!();
    }
}

#[derive(Debug)]
pub struct RewardSetInfo {
    pub anchor_block: BlockHeaderHash,
    pub recipients: Vec<(StacksAddress, u16)>,
}

#[derive(Debug, Clone)]
pub struct MissedBlockCommit {
    pub txid: Txid,
    pub input: (Txid, u32),
    pub intended_sortition: SortitionId,
}

impl MissedBlockCommit {
    pub fn spent_txid(&self) -> &Txid {
        &self.input.0
    }

    pub fn spent_output(&self) -> u32 {
        self.input.1
    }
}

impl RewardSetInfo {
    /// Takes an Option<RewardSetInfo> and produces the commit_outs
    ///   for a corresponding LeaderBlockCommitOp. If RewardSetInfo is none,
    ///   the LeaderBlockCommitOp will use burn addresses.
    pub fn into_commit_outs(from: Option<RewardSetInfo>, mainnet: bool) -> Vec<StacksAddress> {
        if let Some(recipient_set) = from {
            let mut outs: Vec<_> = recipient_set
                .recipients
                .into_iter()
                .map(|(recipient, _)| recipient)
                .collect();
            while outs.len() < OUTPUTS_PER_COMMIT {
                outs.push(StacksAddress::burn_address(mainnet));
            }
            outs
        } else {
            (0..OUTPUTS_PER_COMMIT)
                .map(|_| StacksAddress::burn_address(mainnet))
                .collect()
        }
    }
}

impl LeaderBlockCommitOp {
    fn check_pox(
        &self,
        burnchain: &Burnchain,
        tx: &mut SortitionHandleTx,
        reward_set_info: Option<&RewardSetInfo>,
    ) -> Result<(), op_error> {
        let parent_block_height = self.parent_block_ptr as u64;

        let total_committed = self
            .burn_fee
            .checked_add(self.sunset_burn)
            .expect("BUG: Overflow in total committed calculation");
        let expected_sunset_burn =
            burnchain.expected_sunset_burn(self.block_height, total_committed);
        if self.sunset_burn < expected_sunset_burn {
            warn!(
                "Invalid block commit: should have included sunset burn amount of {}, found {}",
                expected_sunset_burn, self.sunset_burn
            );
            return Err(op_error::BlockCommitBadOutputs);
        }

        /////////////////////////////////////////////////////////////////////////////////////
        // This tx must have the expected commit or burn outputs:
        //    * if there is a known anchor block for the current reward cycle, and this
        //       block commit descends from that block, and this block commit is not in the
        //       prepare phase of the reward cycle, and there are still reward addresses
        //       left in this reward cycle to pay out to, then
        //       the commit outputs must = the expected set of commit outputs.
        //    * otherwise, the commit outputs must be burn outputs.
        /////////////////////////////////////////////////////////////////////////////////////
        if let Some(reward_set_info) = reward_set_info {
            // we do some check-inversion here so that we check the commit_outs _before_
            //   we check whether or not the block is descended from the anchor.
            // we do this because the descended_from check isn't particularly cheap, so
            //   we want to make sure that any TX that forces us to perform the check
            //   has either burned BTC or sent BTC to the PoX recipients

            // if we're in the prepare phase, then this block-commit _must_ burn.
            // No PoX descent check needs to be performed -- prepare-phase block commits
            // stand alone.
            if burnchain.is_in_prepare_phase(self.block_height) {
                if let Err(e) = self.check_prepare_commit_burn() {
                    warn!("Invalid block commit: in block {} which is in the prepare phase, but did not burn to a single output as expected ({:?})", self.block_height, &e);
                    return Err(op_error::BlockCommitBadOutputs);
                }
            } else {
                // Not in prepare phase, so this can be either PoB or PoX (a descent check from the
                // anchor block will be necessary if the block-commit is well-formed).
                //
                // first, handle a corner case:
                //    all of the commitment outputs are _burns_
                //    _and_ the reward set chose two burn addresses as reward addresses.
                // then, don't need to do a pox descendant check.
                let recipient_set_all_burns = reward_set_info
                    .recipients
                    .iter()
                    .fold(true, |prior_is_burn, (addr, _)| {
                        prior_is_burn && addr.is_burn()
                    });

                if recipient_set_all_burns {
                    if !self.all_outputs_burn() {
                        warn!("Invalid block commit: recipient set should be all burns");
                        return Err(op_error::BlockCommitBadOutputs);
                    }
                } else {
                    let expect_pox_descendant = if self.all_outputs_burn() {
                        false
                    } else {
                        let mut check_recipients: Vec<_> = reward_set_info
                            .recipients
                            .iter()
                            .map(|(addr, _)| addr.clone())
                            .collect();

                        if check_recipients.len() == 1 {
                            // If the number of recipients in the set was odd, we need to pad
                            // with a burn address
                            check_recipients
                                .push(StacksAddress::burn_address(burnchain.is_mainnet()))
                        }

                        if self.commit_outs.len() != check_recipients.len() {
                            warn!(
                                "Invalid block commit: expected {} PoX transfers, but commit has {}",
                                reward_set_info.recipients.len(),
                                self.commit_outs.len()
                            );
                            return Err(op_error::BlockCommitBadOutputs);
                        }

                        // sort check_recipients and commit_outs so that we can perform an
                        //  iterative equality check
                        check_recipients.sort();
                        let mut commit_outs = self.commit_outs.clone();
                        commit_outs.sort();
                        for (expected_commit, found_commit) in
                            commit_outs.iter().zip(check_recipients)
                        {
                            if expected_commit != &found_commit {
                                warn!("Invalid block commit: committed output {} does not match expected {}",
                                      found_commit, expected_commit);
                                return Err(op_error::BlockCommitBadOutputs);
                            }
                        }
                        true
                    };

                    let descended_from_anchor = tx.descended_from(parent_block_height, &reward_set_info.anchor_block)
                        .map_err(|e| {
                            error!("Failed to check whether parent (height={}) is descendent of anchor block={}: {}",
                                   parent_block_height, &reward_set_info.anchor_block, e);
                            op_error::BlockCommitAnchorCheck})?;
                    if descended_from_anchor != expect_pox_descendant {
                        if descended_from_anchor {
                            warn!("Invalid block commit: descended from PoX anchor, but used burn outputs");
                        } else {
                            warn!("Invalid block commit: not descended from PoX anchor, but used PoX outputs"
                            );
                        }
                        return Err(op_error::BlockCommitBadOutputs);
                    }
                }
            }
        } else {
            // no recipient info for this sortition, so expect all burns
            if !self.all_outputs_burn() {
                warn!("Invalid block commit: this transaction should only have burn outputs.");
                return Err(op_error::BlockCommitBadOutputs);
            }
        };
        Ok(())
    }

    fn check_single_burn_output(&self) -> Result<(), op_error> {
        if self.commit_outs.len() != 1 {
            warn!("Invalid post-sunset block commit, should have 1 commit out");
            return Err(op_error::BlockCommitBadOutputs);
        }
        if !self.commit_outs[0].is_burn() {
            warn!("Invalid post-sunset block commit, should have burn address output");
            return Err(op_error::BlockCommitBadOutputs);
        }
        Ok(())
    }

    fn check_after_pox_sunset(&self) -> Result<(), op_error> {
        self.check_single_burn_output()
    }

    fn check_prepare_commit_burn(&self) -> Result<(), op_error> {
        self.check_single_burn_output()
    }

    pub fn check(
        &self,
        burnchain: &Burnchain,
        tx: &mut SortitionHandleTx,
        reward_set_info: Option<&RewardSetInfo>,
    ) -> Result<(), op_error> {
        let leader_key_block_height = self.key_block_ptr as u64;
        let parent_block_height = self.parent_block_ptr as u64;

        let tx_tip = tx.context.chain_tip.clone();

        /////////////////////////////////////////////////////////////////////////////////////
        // There must be a burn
        /////////////////////////////////////////////////////////////////////////////////////

        let apparent_sender_address = self
            .apparent_sender
            .to_bitcoin_address(BitcoinNetworkType::Mainnet);

        if self.burn_fee == 0 {
            warn!("Invalid block commit: no burn amount";
                  "apparent_sender" => %apparent_sender_address
            );
            return Err(op_error::BlockCommitBadInput);
        }

        let intended_modulus = (self.burn_block_mined_at() + 1) % BURN_BLOCK_MINED_AT_MODULUS;
        let actual_modulus = self.block_height % BURN_BLOCK_MINED_AT_MODULUS;
        if actual_modulus != intended_modulus {
            warn!("Invalid block commit: missed target block";
                  "intended_modulus" => intended_modulus,
                  "actual_modulus" => actual_modulus,
                  "block_height" => self.block_height,
                  "apparent_sender" => %apparent_sender_address
            );
            // This transaction "missed" its target burn block, the transaction
            //  is not valid, but we should allow this UTXO to "chain" to valid
            //  UTXOs to allow the miner windowing to work in the face of missed
            //  blocks.
            let miss_distance = if actual_modulus > intended_modulus {
                actual_modulus - intended_modulus
            } else {
                BURN_BLOCK_MINED_AT_MODULUS + actual_modulus - intended_modulus
            };
            if miss_distance > self.block_height {
                return Err(op_error::BlockCommitBadModulus);
            }
            let intended_sortition = tx
                .get_ancestor_block_hash(self.block_height - miss_distance, &tx_tip)?
                .ok_or_else(|| op_error::BlockCommitNoParent)?;
            let missed_data = MissedBlockCommit {
                input: self.input.clone(),
                txid: self.txid.clone(),
                intended_sortition,
            };

            return Err(op_error::MissedBlockCommit(missed_data));
        }

        if self.block_height >= burnchain.pox_constants.sunset_end {
            self.check_after_pox_sunset().map_err(|e| {
                warn!("Invalid block-commit: bad PoX after sunset: {:?}", &e;
                          "apparent_sender" => %apparent_sender_address);
                e
            })?;
        } else {
            self.check_pox(burnchain, tx, reward_set_info)
                .map_err(|e| {
                    warn!("Invalid block-commit: bad PoX: {:?}", &e;
                          "apparent_sender" => %apparent_sender_address);
                    e
                })?;
        }

        /////////////////////////////////////////////////////////////////////////////////////
        // This tx must occur after the start of the network
        /////////////////////////////////////////////////////////////////////////////////////

        let first_block_snapshot = SortitionDB::get_first_block_snapshot(tx.tx())?;

        if self.block_height < first_block_snapshot.block_height {
            warn!(
                "Invalid block commit from {}: predates genesis height {}",
                self.block_height,
                first_block_snapshot.block_height;
                "apparent_sender" => %apparent_sender_address
            );
            return Err(op_error::BlockCommitPredatesGenesis);
        }

        /////////////////////////////////////////////////////////////////////////////////////
        // Block must be unique in this burnchain fork
        /////////////////////////////////////////////////////////////////////////////////////

        let is_already_committed = tx.expects_stacks_block_in_fork(&self.block_header_hash)?;

        if is_already_committed {
            warn!(
                "Invalid block commit: already committed to {}",
                self.block_header_hash;
                "apparent_sender" => %apparent_sender_address
            );
            return Err(op_error::BlockCommitAlreadyExists);
        }

        /////////////////////////////////////////////////////////////////////////////////////
        // There must exist a previously-accepted key from a LeaderKeyRegister
        /////////////////////////////////////////////////////////////////////////////////////

        if leader_key_block_height >= self.block_height {
            warn!(
                "Invalid block commit: references leader key in the same or later block ({} >= {})",
                leader_key_block_height, self.block_height;
                "apparent_sender" => %apparent_sender_address
            );
            return Err(op_error::BlockCommitNoLeaderKey);
        }

        let _register_key = tx
            .get_leader_key_at(leader_key_block_height, self.key_vtxindex.into(), &tx_tip)?
            .ok_or_else(|| {
                warn!(
                    "Invalid block commit: no corresponding leader key at {},{} in fork {}",
                    leader_key_block_height, self.key_vtxindex, &tx.context.chain_tip;
                    "apparent_sender" => %apparent_sender_address
                );
                op_error::BlockCommitNoLeaderKey
            })?;

        /////////////////////////////////////////////////////////////////////////////////////
        // There must exist a previously-accepted block from a LeaderBlockCommit, or this
        // LeaderBlockCommit must build off of the genesis block.  If _not_ building off of the
        // genesis block, then the parent block must be in a different epoch (i.e. its parent must
        // be committed already).
        /////////////////////////////////////////////////////////////////////////////////////

        if parent_block_height == self.block_height {
            // tried to build off a block in the same epoch (not allowed)
            warn!("Invalid block commit: cannot build off of a commit in the same block";
                  "apparent_sender" => %apparent_sender_address
            );
            return Err(op_error::BlockCommitNoParent);
        } else if self.parent_block_ptr != 0 || self.parent_vtxindex != 0 {
            // not building off of genesis, so the parent block must exist
            let has_parent = tx
                .get_block_commit_parent(parent_block_height, self.parent_vtxindex.into(), &tx_tip)?
                .is_some();
            if !has_parent {
                warn!("Invalid block commit: no parent block in this fork";
                      "apparent_sender" => %apparent_sender_address
                );
                return Err(op_error::BlockCommitNoParent);
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use address::AddressHashMode;
    use burnchains::bitcoin::address::*;
    use burnchains::bitcoin::blocks::BitcoinBlockParser;
    use burnchains::bitcoin::keys::BitcoinPublicKey;
    use burnchains::bitcoin::*;
    use burnchains::*;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::db::*;
    use chainstate::burn::operations::*;
    use chainstate::burn::ConsensusHash;
    use chainstate::burn::*;
    use chainstate::stacks::StacksPublicKey;
    use deps::bitcoin::blockdata::transaction::Transaction;
    use deps::bitcoin::network::serialize::{deserialize, serialize_hex};
    use util::get_epoch_time_secs;
    use util::hash::*;
    use util::vrf::VRFPublicKey;

    use crate::types::chainstate::StacksAddress;
    use crate::types::chainstate::{BlockHeaderHash, SortitionId, VRFSeed};

    use super::*;

    struct OpFixture {
        txstr: String,
        opstr: String,
        result: Option<LeaderBlockCommitOp>,
    }

    struct CheckFixture {
        op: LeaderBlockCommitOp,
        res: Result<(), op_error>,
    }

    fn make_tx(hex_str: &str) -> Result<Transaction, &'static str> {
        let tx_bin = hex_bytes(hex_str).map_err(|_e| "failed to decode hex string")?;
        let tx = deserialize(&tx_bin.to_vec()).map_err(|_e| "failed to deserialize")?;
        Ok(tx)
    }

    #[test]
    fn test_parse_sunset_end() {
        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 0,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([1; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 30,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([0; 20]),
                    },
                },
            ],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843021;
        burnchain.pox_constants.sunset_end = 16843022;

        let err = LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843022,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap_err();

        assert!(if let op_error::BlockCommitBadOutputs = err {
            true
        } else {
            false
        });

        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 0,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([0; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 30,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([0; 20]),
                    },
                },
            ],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843021;
        burnchain.pox_constants.sunset_end = 16843022;

        let op = LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843022,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap();

        assert_eq!(op.commit_outs.len(), 1);
        assert!(op.commit_outs[0].is_burn());
        assert_eq!(op.burn_fee, 10);
    }

    #[test]
    fn test_parse_pox_commits() {
        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 30,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([1; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 30,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([0; 20]),
                    },
                },
            ],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843019;
        burnchain.pox_constants.sunset_end = 16843020;

        let op = LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843019,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap();

        // should have 2 commit outputs, summing to 20 burned units
        assert_eq!(op.commit_outs.len(), 2);
        assert_eq!(op.burn_fee, 20);
        // the third output, because it's a burn, should have counted as a sunset_burn
        assert_eq!(op.sunset_burn, 30);

        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 0,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([1; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 9,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([0; 20]),
                    },
                },
            ],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843019;
        burnchain.pox_constants.sunset_end = 16843020;

        // burn amount should have been 10, not 9
        match LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843019,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap_err()
        {
            op_error::ParseError => {}
            _ => unreachable!(),
        };

        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 0,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![
                BitcoinTxOutput {
                    units: 13,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([1; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 13,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 13,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 13,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 13,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
            ],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843019;
        burnchain.pox_constants.sunset_end = 16843020;

        let op = LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843019,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap();

        // should have 2 commit outputs
        assert_eq!(op.commit_outs.len(), 2);
        assert_eq!(op.burn_fee, 26);
        // the third output, because it's not a burn, should not have counted as a sunset_burn
        assert_eq!(op.sunset_burn, 0);

        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 0,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![BitcoinTxOutput {
                units: 13,
                address: BitcoinAddress {
                    addrtype: BitcoinAddressType::PublicKeyHash,
                    network_id: BitcoinNetworkType::Mainnet,
                    bytes: Hash160([1; 20]),
                },
            }],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843019;
        burnchain.pox_constants.sunset_end = 16843020;

        // not enough PoX outputs
        match LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843019,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap_err()
        {
            op_error::InvalidInput => {}
            _ => unreachable!(),
        };

        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 0,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![
                BitcoinTxOutput {
                    units: 13,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([1; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 10,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
            ],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843019;
        burnchain.pox_constants.sunset_end = 16843020;

        // unequal PoX outputs
        match LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843019,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap_err()
        {
            op_error::ParseError => {}
            _ => unreachable!(),
        };

        let tx = BurnchainTransaction::Bitcoin(BitcoinTransaction {
            data_amt: 0,
            txid: Txid([0; 32]),
            vtxindex: 0,
            opcode: Opcodes::LeaderBlockCommit as u8,
            data: vec![1; 80],
            inputs: vec![BitcoinTxInput {
                keys: vec![],
                num_required: 0,
                in_type: BitcoinInputType::Standard,
                tx_ref: (Txid([0; 32]), 0),
            }],
            outputs: vec![
                BitcoinTxOutput {
                    units: 0,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([1; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 0,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 0,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 0,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
                BitcoinTxOutput {
                    units: 0,
                    address: BitcoinAddress {
                        addrtype: BitcoinAddressType::PublicKeyHash,
                        network_id: BitcoinNetworkType::Mainnet,
                        bytes: Hash160([2; 20]),
                    },
                },
            ],
        });

        let mut burnchain = Burnchain::regtest("nope");
        burnchain.pox_constants.sunset_start = 16843019;
        burnchain.pox_constants.sunset_end = 16843020;

        // 0 total burn
        match LeaderBlockCommitOp::parse_from_tx(
            &burnchain,
            16843019,
            &BurnchainHeaderHash([0; 32]),
            &tx,
        )
        .unwrap_err()
        {
            op_error::ParseError => {}
            _ => unreachable!(),
        };
    }

    #[test]
    fn test_parse() {
        let vtxindex = 1;
        let block_height = 0x71706363; // epoch number must be strictly smaller than block height
        let burn_header_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();

        let tx_fixtures = vec![
            OpFixture {
                // valid
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006b483045022100eba8c0a57c1eb71cdfba0874de63cf37b3aace1e56dcbd61701548194a79af34022041dd191256f3f8a45562e5d60956bb871421ba69db605716250554b23b08277b012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000040000000000000000536a4c5069645b22222222222222222222222222222222222222222222222222222222222222223333333333333333333333333333333333333333333333333333333333333333404142435051606162637071fa39300000000000001976a914000000000000000000000000000000000000000088ac39300000000000001976a914000000000000000000000000000000000000000088aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".into(),
                opstr: "69645b22222222222222222222222222222222222222222222222222222222222222223333333333333333333333333333333333333333333333333333333333333333404142435051606162637071fa".to_string(),
                result: Some(LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(&hex_bytes("2222222222222222222222222222222222222222222222222222222222222222").unwrap()).unwrap(),
                    new_seed: VRFSeed::from_bytes(&hex_bytes("3333333333333333333333333333333333333333333333333333333333333333").unwrap()).unwrap(),
                    parent_block_ptr: 0x40414243,
                    parent_vtxindex: 0x5051,
                    key_block_ptr: 0x60616263,
                    key_vtxindex: 0x7071,
                    memo: vec![0x1f],

                    commit_outs: vec![
                        StacksAddress { version: 26, bytes: Hash160::empty() },
                        StacksAddress { version: 26, bytes: Hash160::empty() }
                    ],

                    burn_fee: 24690,
                    input: (Txid([0x11; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![
                            StacksPublicKey::from_hex("02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0").unwrap(),
                        ],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH
                    },

                    txid: Txid::from_hex("502f3e5756de7e1bdba8c713cd2daab44adb5337d14ff668fdc57cc27d67f0d4").unwrap(),
                    vtxindex: vtxindex,
                    block_height: block_height,
                    burn_parent_modulus: ((block_height - 1) % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: burn_header_hash,
                })
            },
            OpFixture {
                // invalid -- wrong opcode
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006946304302207129fa2054a61cdb4b7db0b8fab6e8ff4af0edf979627aa5cf41665b7475a451021f70032b48837df091223c1d0bb57fb0298818eb11d0c966acff4b82f4b2d5c8012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000030000000000000000536a4c5069645c222222222222222222222222222222222222222222222222222222222222222233333333333333333333333333333333333333333333333333333333333333334041424350516061626370718039300000000000001976a914000000000000000000000000000000000000000088aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "".to_string(),
                result: None,
            },
            OpFixture {
                // invalid -- wrong burn address
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006b483045022100e25f5f9f660339cd665caba231d5bdfc3f0885bcc0b3f85dc35564058c9089d702206aa142ea6ccd89e56fdc0743cdcf3a2744e133f335e255e9370e4f8a6d0f6ffd012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000030000000000000000536a4c5069645b222222222222222222222222222222222222222222222222222222222222222233333333333333333333333333333333333333333333333333333333333333334041424350516061626370718039300000000000001976a914000000000000000000000000000000000000000188aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "".to_string(),
                result: None,
            },
            OpFixture {
                // invalid -- bad OP_RETURN (missing memo)
                txstr: "01000000011111111111111111111111111111111111111111111111111111111111111111000000006b483045022100c6c3ccc9b5a6ba5161706f3a5e4518bc3964e8de1cf31dbfa4d38082535c88e902205860de620cfe68a72d5a1fc3be1171e6fd8b2cdde0170f76724faca0db5ee0b6012102d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d000000000030000000000000000526a4c4f69645b2222222222222222222222222222222222222222222222222222222222222222333333333333333333333333333333333333333333333333333333333333333340414243505160616263707139300000000000001976a914000000000000000000000000000000000000000088aca05b0000000000001976a9140be3e286a15ea85882761618e366586b5574100d88ac00000000".to_string(),
                opstr: "".to_string(),
                result: None,
            }
        ];

        let parser = BitcoinBlockParser::new(BitcoinNetworkType::Testnet, BLOCKSTACK_MAGIC_MAINNET);

        let mut is_first = false;
        for tx_fixture in tx_fixtures {
            let mut tx = make_tx(&tx_fixture.txstr).unwrap();
            if is_first {
                eprintln!("TX outputs: {}", tx.output.len());
                tx.output.insert(
                    2,
                    StacksAddress::burn_address(false).to_bitcoin_tx_out(12345),
                );
                is_first = false;
                eprintln!("Updated txstr = {}", serialize_hex(&tx).unwrap());
                assert!(false);
            }

            let header = match tx_fixture.result {
                Some(ref op) => BurnchainBlockHeader {
                    block_height: op.block_height,
                    block_hash: op.burn_header_hash.clone(),
                    parent_block_hash: op.burn_header_hash.clone(),
                    num_txs: 1,
                    timestamp: get_epoch_time_secs(),
                },
                None => BurnchainBlockHeader {
                    block_height: 0,
                    block_hash: BurnchainHeaderHash::zero(),
                    parent_block_hash: BurnchainHeaderHash::zero(),
                    num_txs: 0,
                    timestamp: get_epoch_time_secs(),
                },
            };
            let burnchain_tx =
                BurnchainTransaction::Bitcoin(parser.parse_tx(&tx, vtxindex as usize).unwrap());

            let mut burnchain = Burnchain::regtest("nope");
            burnchain.pox_constants.sunset_start = block_height;
            burnchain.pox_constants.sunset_end = block_height + 1;

            let op = LeaderBlockCommitOp::from_tx(&burnchain, &header, &burnchain_tx);

            match (op, tx_fixture.result) {
                (Ok(parsed_tx), Some(result)) => {
                    let opstr = {
                        let mut buffer = vec![];
                        let mut magic_bytes = BLOCKSTACK_MAGIC_MAINNET.as_bytes().to_vec();
                        buffer.append(&mut magic_bytes);
                        parsed_tx
                            .consensus_serialize(&mut buffer)
                            .expect("FATAL: invalid operation");
                        to_hex(&buffer)
                    };

                    assert_eq!(tx_fixture.opstr, opstr);
                    assert_eq!(parsed_tx, result);
                }
                (Err(_e), None) => {}
                (Ok(_parsed_tx), None) => {
                    eprintln!("Parsed a tx when we should not have");
                    assert!(false);
                }
                (Err(_e), Some(_result)) => {
                    eprintln!("Did not parse a tx when we should have");
                    assert!(false);
                }
            };
        }
    }

    #[test]
    fn test_check() {
        let first_block_height = 121;
        let first_burn_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000123",
        )
        .unwrap();

        let block_122_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000001220",
        )
        .unwrap();
        let block_123_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000001230",
        )
        .unwrap();
        let block_124_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000001240",
        )
        .unwrap();
        let block_125_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000001250",
        )
        .unwrap();
        let block_126_hash = BurnchainHeaderHash::from_hex(
            "0000000000000000000000000000000000000000000000000000000000001260",
        )
        .unwrap();

        let block_header_hashes = [
            block_122_hash.clone(),
            block_123_hash.clone(),
            block_124_hash.clone(),
            block_125_hash.clone(), // prepare phase
            block_126_hash.clone(), // prepare phase
        ];

        let burnchain = Burnchain {
            pox_constants: PoxConstants::new(6, 2, 2, 25, 5, 5000, 10000),
            peer_version: 0x012345678,
            network_id: 0x9abcdef0,
            chain_name: "bitcoin".to_string(),
            network_name: "testnet".to_string(),
            working_dir: "/nope".to_string(),
            consensus_hash_lifetime: 24,
            stable_confirmations: 7,
            first_block_height,
            initial_reward_start_block: first_block_height,
            first_block_timestamp: 0,
            first_block_hash: first_burn_hash.clone(),
        };

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
                    &hex_bytes("76a914306231b2782b5f80d944bf69f9d46a1453a0a0eb88ac").unwrap(),
                )
                .unwrap(),
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("1bfa831b5fc56c858198acb8e77e5863c1e9d8ac26d49ddb914e24d8d4083562")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 456,
            block_height: 124,
            burn_header_hash: block_124_hash.clone(),
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
                    &hex_bytes("76a914306231b2782b5f80d944bf69f9d46a1453a0a0eb88ac").unwrap(),
                )
                .unwrap(),
            ),

            txid: Txid::from_bytes_be(
                &hex_bytes("9410df84e2b440055c33acb075a0687752df63fe8fe84aeec61abe469f0448c7")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 457,
            block_height: 124,
            burn_header_hash: block_124_hash.clone(),
        };

        // consumes leader_key_1
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
            parent_block_ptr: 0,
            parent_vtxindex: 0,
            key_block_ptr: 124,
            key_vtxindex: 456,
            memo: vec![0x80],
            commit_outs: vec![],

            burn_fee: 12345,
            input: (Txid([0; 32]), 0),
            apparent_sender: BurnchainSigner {
                public_keys: vec![StacksPublicKey::from_hex(
                    "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                )
                .unwrap()],
                num_sigs: 1,
                hash_mode: AddressHashMode::SerializeP2PKH,
            },

            txid: Txid::from_bytes_be(
                &hex_bytes("3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf")
                    .unwrap(),
            )
            .unwrap(),
            vtxindex: 444,
            block_height: 125,
            burn_parent_modulus: (124 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
            burn_header_hash: block_125_hash.clone(),
        };

        let mut db = SortitionDB::connect_test(first_block_height, &first_burn_hash).unwrap();
        let block_ops = vec![
            // 122
            vec![],
            // 123
            vec![],
            // 124
            vec![
                BlockstackOperationType::LeaderKeyRegister(leader_key_1.clone()),
                BlockstackOperationType::LeaderKeyRegister(leader_key_2.clone()),
            ],
            // 125
            vec![BlockstackOperationType::LeaderBlockCommit(
                block_commit_1.clone(),
            )],
            // 126
            vec![],
        ];

        let tip_index_root = {
            let mut prev_snapshot = SortitionDB::get_first_block_snapshot(db.conn()).unwrap();
            for i in 0..block_header_hashes.len() {
                let mut snapshot_row = BlockSnapshot {
                    accumulated_coinbase_ustx: 0,
                    pox_valid: true,
                    block_height: (i + 1 + first_block_height as usize) as u64,
                    burn_header_timestamp: get_epoch_time_secs(),
                    burn_header_hash: block_header_hashes[i].clone(),
                    sortition_id: SortitionId(block_header_hashes[i as usize].0.clone()),
                    parent_sortition_id: prev_snapshot.sortition_id.clone(),
                    parent_burn_header_hash: prev_snapshot.burn_header_hash.clone(),
                    consensus_hash: ConsensusHash::from_bytes(&[
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        0,
                        (i + 1) as u8,
                    ])
                    .unwrap(),
                    ops_hash: OpsHash::from_bytes(&[
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, i as u8,
                    ])
                    .unwrap(),
                    total_burn: i as u64,
                    sortition: true,
                    sortition_hash: SortitionHash::initial(),
                    winning_block_txid: Txid::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    winning_stacks_block_hash: BlockHeaderHash::from_hex(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    index_root: TrieHash::from_empty_data(),
                    num_sortitions: (i + 1) as u64,
                    stacks_block_accepted: false,
                    stacks_block_height: 0,
                    arrival_index: 0,
                    canonical_stacks_tip_height: 0,
                    canonical_stacks_tip_hash: BlockHeaderHash([0u8; 32]),
                    canonical_stacks_tip_consensus_hash: ConsensusHash([0u8; 20]),
                    ..BlockSnapshot::initial(0, &first_burn_hash, 0)
                };
                let mut tx =
                    SortitionHandleTx::begin(&mut db, &prev_snapshot.sortition_id).unwrap();
                let next_index_root = tx
                    .append_chain_tip_snapshot(
                        &prev_snapshot,
                        &snapshot_row,
                        &block_ops[i],
                        &vec![],
                        None,
                        None,
                        None,
                    )
                    .unwrap();

                snapshot_row.index_root = next_index_root;
                tx.commit().unwrap();

                prev_snapshot = snapshot_row;
            }

            prev_snapshot.index_root.clone()
        };

        let block_height = 124;

        let fixtures = vec![
            CheckFixture {
                // reject -- predates start block
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 50,
                    parent_vtxindex: 456,
                    key_block_ptr: 1,
                    key_vtxindex: 457,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 444,
                    block_height: 80,
                    burn_parent_modulus: (79 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Err(op_error::BlockCommitPredatesGenesis),
            },
            CheckFixture {
                // reject -- no such leader key
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 1,
                    parent_vtxindex: 444,
                    key_block_ptr: 2,
                    key_vtxindex: 400,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 444,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Err(op_error::BlockCommitNoLeaderKey),
            },
            CheckFixture {
                // reject -- previous block must exist
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 125,
                    parent_vtxindex: 445,
                    key_block_ptr: 124,
                    key_vtxindex: 457,
                    commit_outs: vec![],
                    memo: vec![0x80],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 445,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Err(op_error::BlockCommitNoParent),
            },
            CheckFixture {
                // reject -- previous block must exist in a different block
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 126,
                    parent_vtxindex: 444,
                    key_block_ptr: 124,
                    key_vtxindex: 457,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 445,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Err(op_error::BlockCommitNoParent),
            },
            CheckFixture {
                // reject -- tx input does not match any leader keys
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 125,
                    parent_vtxindex: 444,
                    key_block_ptr: 124,
                    key_vtxindex: 457,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "03984286096373539ae529bd997c92792d4e5b5967be72979a42f587a625394116",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 445,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Ok(()),
            },
            CheckFixture {
                // reject -- fee is 0
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 125,
                    parent_vtxindex: 444,
                    key_block_ptr: 124,
                    key_vtxindex: 457,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 0,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 445,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Err(op_error::BlockCommitBadInput),
            },
            CheckFixture {
                // accept -- consumes leader_key_2
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 125,
                    parent_vtxindex: 444,
                    key_block_ptr: 124,
                    key_vtxindex: 457,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 445,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Ok(()),
            },
            CheckFixture {
                // accept -- builds directly off of genesis block and consumes leader_key_2
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 0,
                    parent_vtxindex: 0,
                    key_block_ptr: 124,
                    key_vtxindex: 457,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 445,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Ok(()),
            },
            CheckFixture {
                // accept -- also consumes leader_key_1
                op: LeaderBlockCommitOp {
                    sunset_burn: 0,
                    block_header_hash: BlockHeaderHash::from_bytes(
                        &hex_bytes(
                            "2222222222222222222222222222222222222222222222222222222222222222",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    new_seed: VRFSeed::from_bytes(
                        &hex_bytes(
                            "3333333333333333333333333333333333333333333333333333333333333333",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    parent_block_ptr: 0,
                    parent_vtxindex: 0,
                    key_block_ptr: 124,
                    key_vtxindex: 456,
                    memo: vec![0x80],
                    commit_outs: vec![],

                    burn_fee: 12345,
                    input: (Txid([0; 32]), 0),
                    apparent_sender: BurnchainSigner {
                        public_keys: vec![StacksPublicKey::from_hex(
                            "02d8015134d9db8178ac93acbc43170a2f20febba5087a5b0437058765ad5133d0",
                        )
                        .unwrap()],
                        num_sigs: 1,
                        hash_mode: AddressHashMode::SerializeP2PKH,
                    },

                    txid: Txid::from_bytes_be(
                        &hex_bytes(
                            "3c07a0a93360bc85047bbaadd49e30c8af770f73a37e10fec400174d2e5f27cf",
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                    vtxindex: 444,
                    block_height: 126,
                    burn_parent_modulus: (125 % BURN_BLOCK_MINED_AT_MODULUS) as u8,
                    burn_header_hash: block_126_hash.clone(),
                },
                res: Ok(()),
            },
        ];

        for (ix, fixture) in fixtures.iter().enumerate() {
            eprintln!("Processing {}", ix);
            let header = BurnchainBlockHeader {
                block_height: fixture.op.block_height,
                block_hash: fixture.op.burn_header_hash.clone(),
                parent_block_hash: fixture.op.burn_header_hash.clone(),
                num_txs: 1,
                timestamp: get_epoch_time_secs(),
            };
            let mut ic = SortitionHandleTx::begin(
                &mut db,
                &SortitionId::stubbed(&fixture.op.burn_header_hash),
            )
            .unwrap();
            assert_eq!(
                format!("{:?}", &fixture.res),
                format!("{:?}", &fixture.op.check(&burnchain, &mut ic, None))
            );
        }
    }
}
