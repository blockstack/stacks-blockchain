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

use std::boxed::Box;
use std::cmp;
use std::convert::TryFrom;
use std::convert::TryInto;

use address::AddressHashMode;
use burnchains::bitcoin::address::BitcoinAddress;
use burnchains::Burnchain;
use burnchains::{Address, PoxConstants};
use chainstate::burn::db::sortdb::SortitionDB;
use chainstate::stacks::db::StacksChainState;
use chainstate::stacks::index::marf::MarfConnection;
use chainstate::stacks::Error;
use clarity_vm::clarity::ClarityConnection;
use core::{POX_MAXIMAL_SCALING, POX_THRESHOLD_STEPS_USTX};
use util::hash::Hash160;
use vm::contexts::ContractContext;
use vm::costs::{
    cost_functions::ClarityCostFunction, ClarityCostFunctionReference, CostStateSummary,
};
use vm::database::ClarityDatabase;
use vm::database::{NULL_BURN_STATE_DB, NULL_HEADER_DB};
use vm::representations::ClarityName;
use vm::representations::ContractName;
use vm::types::{
    PrincipalData, QualifiedContractIdentifier, SequenceData, StandardPrincipalData, TupleData,
    TypeSignature, Value,
};

use crate::types;
use crate::types::chainstate::StacksAddress;
use crate::types::chainstate::StacksBlockHeader;
use crate::types::chainstate::StacksBlockId;
use crate::util::boot;
use crate::vm::{costs::LimitedCostTracker, SymbolicExpression};

const BOOT_CODE_POX_BODY: &'static str = std::include_str!("pox.clar");
const BOOT_CODE_POX_TESTNET_CONSTS: &'static str = std::include_str!("pox-testnet.clar");
const BOOT_CODE_POX_MAINNET_CONSTS: &'static str = std::include_str!("pox-mainnet.clar");
const BOOT_CODE_LOCKUP: &'static str = std::include_str!("lockup.clar");
pub const BOOT_CODE_COSTS: &'static str = std::include_str!("costs.clar");
const BOOT_CODE_COST_VOTING_MAINNET: &'static str = std::include_str!("cost-voting.clar");
const BOOT_CODE_BNS: &'static str = std::include_str!("bns.clar");
const BOOT_CODE_GENESIS: &'static str = std::include_str!("genesis.clar");
pub const POX_1_NAME: &'static str = "pox";
pub const POX_2_NAME: &'static str = "pox-2";

const POX_2_TESTNET_CONSTS: &'static str = std::include_str!("pox-testnet.clar");
const POX_2_MAINNET_CONSTS: &'static str = std::include_str!("pox-mainnet.clar");
const POX_2_BODY: &'static str = std::include_str!("pox-2.clar");

lazy_static! {
    pub static ref BOOT_CODE_POX_MAINNET: String =
        format!("{}\n{}", BOOT_CODE_POX_MAINNET_CONSTS, BOOT_CODE_POX_BODY);
    pub static ref BOOT_CODE_POX_TESTNET: String =
        format!("{}\n{}", BOOT_CODE_POX_TESTNET_CONSTS, BOOT_CODE_POX_BODY);
    pub static ref POX_2_MAINNET_CODE: String =
        format!("{}\n{}", BOOT_CODE_POX_MAINNET_CONSTS, POX_2_BODY);
    pub static ref POX_2_TESTNET_CODE: String =
        format!("{}\n{}", BOOT_CODE_POX_TESTNET_CONSTS, POX_2_BODY);
    pub static ref BOOT_CODE_COST_VOTING_TESTNET: String = make_testnet_cost_voting();
    pub static ref STACKS_BOOT_CODE_MAINNET: [(&'static str, &'static str); 6] = [
        ("pox", &BOOT_CODE_POX_MAINNET),
        ("lockup", BOOT_CODE_LOCKUP),
        ("costs", BOOT_CODE_COSTS),
        ("cost-voting", BOOT_CODE_COST_VOTING_MAINNET),
        ("bns", &BOOT_CODE_BNS),
        ("genesis", &BOOT_CODE_GENESIS),
    ];
    pub static ref STACKS_BOOT_CODE_TESTNET: [(&'static str, &'static str); 6] = [
        ("pox", &BOOT_CODE_POX_TESTNET),
        ("lockup", BOOT_CODE_LOCKUP),
        ("costs", BOOT_CODE_COSTS),
        ("cost-voting", &BOOT_CODE_COST_VOTING_TESTNET),
        ("bns", &BOOT_CODE_BNS),
        ("genesis", &BOOT_CODE_GENESIS),
    ];
}

fn make_testnet_cost_voting() -> String {
    BOOT_CODE_COST_VOTING_MAINNET
        .replacen(
            "(define-constant VETO_LENGTH u1008)",
            "(define-constant VETO_LENGTH u50)",
            1,
        )
        .replacen(
            "(define-constant REQUIRED_VETOES u500)",
            "(define-constant REQUIRED_VETOES u25)",
            1,
        )
}

pub fn make_contract_id(addr: &StacksAddress, name: &str) -> QualifiedContractIdentifier {
    QualifiedContractIdentifier::new(
        StandardPrincipalData::from(addr.clone()),
        ContractName::try_from(name.to_string()).unwrap(),
    )
}

impl StacksAddress {
    pub fn as_clarity_tuple(&self) -> TupleData {
        let version = Value::buff_from_byte(AddressHashMode::from_version(self.version) as u8);
        let hashbytes = Value::buff_from(Vec::from(self.bytes.0.clone()))
            .expect("BUG: hash160 bytes do not fit in Clarity Value");
        TupleData::from_data(vec![
            ("version".into(), version),
            ("hashbytes".into(), hashbytes),
        ])
        .expect("BUG: StacksAddress byte representation does not fit in Clarity Value")
    }
}

/// Extract a PoX address from its tuple representation
fn tuple_to_pox_addr(tuple_data: TupleData) -> (AddressHashMode, Hash160) {
    let version_value = tuple_data
        .get("version")
        .expect("FATAL: no 'version' field in pox-addr")
        .to_owned();
    let hashbytes_value = tuple_data
        .get("hashbytes")
        .expect("FATAL: no 'hashbytes' field in pox-addr")
        .to_owned();

    let version_u8 = version_value.expect_buff_padded(1, 0)[0];
    let version: AddressHashMode = version_u8
        .try_into()
        .expect("FATAL: PoX version is not a supported version byte");

    let hashbytes_vec = hashbytes_value.expect_buff_padded(20, 0);

    let mut hashbytes_20 = [0u8; 20];
    hashbytes_20.copy_from_slice(&hashbytes_vec[0..20]);
    let hashbytes = Hash160(hashbytes_20);

    (version, hashbytes)
}

impl StacksChainState {
    fn eval_boot_code_read_only(
        &mut self,
        sortdb: &SortitionDB,
        stacks_block_id: &StacksBlockId,
        boot_contract_name: &str,
        code: &str,
    ) -> Result<Value, Error> {
        let iconn = sortdb.index_conn();
        let dbconn = self.state_index.sqlite_conn();
        self.clarity_state
            .eval_read_only(
                &stacks_block_id,
                dbconn,
                &iconn,
                &boot::boot_code_id(boot_contract_name, self.mainnet),
                code,
            )
            .map_err(Error::ClarityError)
    }

    pub fn get_liquid_ustx(&mut self, stacks_block_id: &StacksBlockId) -> u128 {
        let mut connection = self.clarity_state.read_only_connection(
            stacks_block_id,
            &NULL_HEADER_DB,
            &NULL_BURN_STATE_DB,
        );
        connection.with_clarity_db_readonly_owned(|mut clarity_db| {
            (clarity_db.get_total_liquid_ustx(), clarity_db)
        })
    }

    /// Determine the minimum amount of STX per reward address required to stack in the _next_
    /// reward cycle
    #[cfg(test)]
    pub fn get_stacking_minimum(
        &mut self,
        sortdb: &SortitionDB,
        stacks_block_id: &StacksBlockId,
    ) -> Result<u128, Error> {
        self.eval_boot_code_read_only(
            sortdb,
            stacks_block_id,
            "pox",
            &format!("(get-stacking-minimum)"),
        )
        .map(|value| value.expect_u128())
    }

    pub fn get_total_ustx_stacked(
        &mut self,
        sortdb: &SortitionDB,
        tip: &StacksBlockId,
        reward_cycle: u128,
        pox_contract: &str,
    ) -> Result<u128, Error> {
        let function = "get-total-ustx-stacked";
        let mainnet = self.mainnet;
        let contract_identifier = boot::boot_code_id(pox_contract, mainnet);
        let cost_track = LimitedCostTracker::new_free();
        let sender = PrincipalData::Standard(StandardPrincipalData::transient());
        let result = self
            .maybe_read_only_clarity_tx(&sortdb.index_conn(), tip, |clarity_tx| {
                clarity_tx.with_readonly_clarity_env(mainnet, sender, cost_track, |env| {
                    env.execute_contract(
                        &contract_identifier,
                        function,
                        &vec![SymbolicExpression::atom_value(Value::UInt(reward_cycle))],
                        true,
                    )
                })
            })?
            .ok_or_else(|| Error::NoSuchBlockError)??
            .expect_u128();
        Ok(result)
    }

    /// Determine how many uSTX are stacked in a given reward cycle
    #[cfg(test)]
    pub fn test_get_total_ustx_stacked(
        &mut self,
        sortdb: &SortitionDB,
        stacks_block_id: &StacksBlockId,
        reward_cycle: u128,
    ) -> Result<u128, Error> {
        self.eval_boot_code_read_only(
            sortdb,
            stacks_block_id,
            "pox",
            &format!("(get-total-ustx-stacked u{})", reward_cycle),
        )
        .map(|value| value.expect_u128())
    }

    /// Is PoX active in the given reward cycle?
    pub fn is_pox_active(
        &mut self,
        sortdb: &SortitionDB,
        stacks_block_id: &StacksBlockId,
        reward_cycle: u128,
        pox_contract: &str,
    ) -> Result<bool, Error> {
        self.eval_boot_code_read_only(
            sortdb,
            stacks_block_id,
            pox_contract,
            &format!("(is-pox-active u{})", reward_cycle),
        )
        .map(|value| value.expect_bool())
    }

    /// Given a threshold and set of registered addresses, return a reward set where
    ///   every entry address has stacked more than the threshold, and addresses
    ///   are repeated floor(stacked_amt / threshold) times.
    /// If an address appears in `addresses` multiple times, then the address's associated amounts
    ///   are summed.
    pub fn make_reward_set(
        threshold: u128,
        mut addresses: Vec<(StacksAddress, u128)>,
    ) -> Vec<StacksAddress> {
        let mut reward_set = vec![];
        // the way that we sum addresses relies on sorting.
        addresses.sort_by_key(|k| k.0.bytes.0);
        while let Some((address, mut stacked_amt)) = addresses.pop() {
            // peak at the next address in the set, and see if we need to sum
            while addresses.last().map(|x| &x.0) == Some(&address) {
                let (_, additional_amt) = addresses
                    .pop()
                    .expect("BUG: first() returned some, but pop() is none.");
                stacked_amt = stacked_amt
                    .checked_add(additional_amt)
                    .expect("CORRUPTION: Stacker stacked > u128 max amount");
            }
            let slots_taken = u32::try_from(stacked_amt / threshold)
                .expect("CORRUPTION: Stacker claimed > u32::max() reward slots");
            info!(
                "Slots taken by {} = {}, on stacked_amt = {}, threshold = {}",
                &address.clone().to_b58(),
                slots_taken,
                stacked_amt,
                threshold
            );
            for _i in 0..slots_taken {
                test_debug!("Add to PoX reward set: {:?}", &address);
                reward_set.push(address.clone());
            }
        }
        info!("Reward set calculated"; "slots_occuppied" => reward_set.len());
        reward_set
    }

    pub fn get_threshold_from_participation(
        liquid_ustx: u128,
        participation: u128,
        reward_slots: u128,
    ) -> u128 {
        // set the lower limit on reward scaling at 25% of liquid_ustx
        //   (i.e., liquid_ustx / POX_MAXIMAL_SCALING)
        let scale_by = cmp::max(participation, liquid_ustx / POX_MAXIMAL_SCALING as u128);
        let threshold_precise = scale_by / reward_slots;
        // compute the threshold as nearest 10k > threshold_precise
        let ceil_amount = match threshold_precise % POX_THRESHOLD_STEPS_USTX {
            0 => 0,
            remainder => POX_THRESHOLD_STEPS_USTX - remainder,
        };
        let threshold = threshold_precise + ceil_amount;
        return threshold;
    }

    pub fn get_reward_threshold_and_participation(
        pox_settings: &PoxConstants,
        addresses: &[(StacksAddress, u128)],
        liquid_ustx: u128,
    ) -> (u128, u128) {
        let participation = addresses
            .iter()
            .fold(0, |agg, (_, stacked_amt)| agg + stacked_amt);

        assert!(
            participation <= liquid_ustx,
            "CORRUPTION: More stacking participation than liquid STX"
        );

        // set the lower limit on reward scaling at 25% of liquid_ustx
        //   (i.e., liquid_ustx / POX_MAXIMAL_SCALING)
        let scale_by = cmp::max(participation, liquid_ustx / POX_MAXIMAL_SCALING as u128);

        let reward_slots = pox_settings.reward_slots() as u128;
        let threshold_precise = scale_by / reward_slots;
        // compute the threshold as nearest 10k > threshold_precise
        let ceil_amount = match threshold_precise % POX_THRESHOLD_STEPS_USTX {
            0 => 0,
            remainder => POX_THRESHOLD_STEPS_USTX - remainder,
        };
        let threshold = threshold_precise + ceil_amount;
        info!(
            "PoX participation threshold is {}, from {} + {} ({})",
            threshold, threshold_precise, ceil_amount, scale_by,
        );
        (threshold, participation)
    }

    /// Each address will have at least (get-stacking-minimum) tokens.
    pub fn get_reward_addresses(
        &mut self,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        current_burn_height: u64,
        block_id: &StacksBlockId,
    ) -> Result<Vec<(StacksAddress, u128)>, Error> {
        let reward_cycle = burnchain
            .block_height_to_reward_cycle(current_burn_height)
            .ok_or(Error::PoxNoRewardCycle)?;

        let reward_cycle_start_height = burnchain.reward_cycle_to_block_height(reward_cycle);

        let pox_contract_name = burnchain
            .pox_constants
            .active_pox_contract(reward_cycle_start_height);

        if !self.is_pox_active(sortdb, block_id, reward_cycle as u128, pox_contract_name)? {
            debug!(
                "PoX was voted disabled in block {} (reward cycle {})",
                block_id, reward_cycle
            );
            return Ok(vec![]);
        }

        debug!("Using pox_contract = {}", pox_contract_name);

        // how many in this cycle?
        let num_addrs = self
            .eval_boot_code_read_only(
                sortdb,
                block_id,
                pox_contract_name,
                &format!("(get-reward-set-size u{})", reward_cycle),
            )?
            .expect_u128();

        debug!(
            "At block {:?} (reward cycle {}): {} PoX reward addresses",
            block_id, reward_cycle, num_addrs
        );

        let mut ret = vec![];
        for i in 0..num_addrs {
            // value should be (optional (tuple (pox-addr (tuple (...))) (total-ustx uint))).
            // Get the tuple.
            let tuple_data = self
                .eval_boot_code_read_only(
                    sortdb,
                    block_id,
                    pox_contract_name,
                    &format!("(get-reward-set-pox-address u{} u{})", reward_cycle, i),
                )?
                .expect_optional()
                .expect(&format!(
                    "FATAL: missing PoX address in slot {} out of {} in reward cycle {}",
                    i, num_addrs, reward_cycle
                ))
                .expect_tuple();

            let pox_addr_tuple = tuple_data
                .get("pox-addr")
                .expect(&format!("FATAL: no 'pox-addr' in return value from (get-reward-set-pox-address u{} u{})", reward_cycle, i))
                .to_owned()
                .expect_tuple();

            let (hash_mode, hash) = tuple_to_pox_addr(pox_addr_tuple);

            let total_ustx = tuple_data
                .get("total-ustx")
                .expect(&format!("FATAL: no 'total-ustx' in return value from (get-reward-set-pox-address u{} u{})", reward_cycle, i))
                .to_owned()
                .expect_u128();

            let version = match self.mainnet {
                true => hash_mode.to_version_mainnet(),
                false => hash_mode.to_version_testnet(),
            };

            debug!(
                "PoX reward address (for {} ustx): {}",
                total_ustx,
                &StacksAddress::new(version, hash)
            );
            ret.push((StacksAddress::new(version, hash), total_ustx));
        }

        Ok(ret)
    }
}

#[cfg(test)]
pub mod contract_tests;
#[cfg(test)]
pub mod pox_2_tests;

#[cfg(test)]
pub mod test {
    use std::collections::{HashMap, HashSet};
    use std::convert::From;
    use std::fs;

    use burnchains::Address;
    use burnchains::PublicKey;
    use chainstate::burn::db::sortdb::*;
    use chainstate::burn::db::*;
    use chainstate::burn::operations::BlockstackOperationType;
    use chainstate::burn::*;
    use chainstate::stacks::db::test::*;
    use chainstate::stacks::db::*;
    use chainstate::stacks::miner::test::*;
    use chainstate::stacks::miner::*;
    use chainstate::stacks::Error as chainstate_error;
    use chainstate::stacks::*;
    use core::*;
    use net::test::*;
    use util::hash::to_hex;
    use util::*;
    use vm::contracts::Contract;
    use vm::types::*;

    use crate::util::boot::{boot_code_id, boot_code_test_addr};
    use chainstate::stacks::C32_ADDRESS_VERSION_TESTNET_SINGLESIG;

    use super::*;

    #[test]
    fn make_reward_set_units() {
        let threshold = 1_000;
        let addresses = vec![
            (
                StacksAddress::from_string("STVK1K405H6SK9NKJAP32GHYHDJ98MMNP8Y6Z9N0").unwrap(),
                1500,
            ),
            (
                StacksAddress::from_string("ST76D2FMXZ7D2719PNE4N71KPSX84XCCNCMYC940").unwrap(),
                500,
            ),
            (
                StacksAddress::from_string("STVK1K405H6SK9NKJAP32GHYHDJ98MMNP8Y6Z9N0").unwrap(),
                1500,
            ),
            (
                StacksAddress::from_string("ST76D2FMXZ7D2719PNE4N71KPSX84XCCNCMYC940").unwrap(),
                400,
            ),
        ];
        assert_eq!(
            StacksChainState::make_reward_set(threshold, addresses).len(),
            3
        );
    }

    #[test]
    fn get_reward_threshold_units() {
        let test_pox_constants = PoxConstants::new(501, 1, 1, 1, 5, 5000, 10000, u32::max_value());
        // when the liquid amount = the threshold step,
        //   the threshold should always be the step size.
        let liquid = POX_THRESHOLD_STEPS_USTX;
        assert_eq!(
            StacksChainState::get_reward_threshold_and_participation(
                &test_pox_constants,
                &[],
                liquid
            )
            .0,
            POX_THRESHOLD_STEPS_USTX
        );
        assert_eq!(
            StacksChainState::get_reward_threshold_and_participation(
                &test_pox_constants,
                &[(rand_addr(), liquid)],
                liquid
            )
            .0,
            POX_THRESHOLD_STEPS_USTX
        );

        let liquid = 200_000_000 * MICROSTACKS_PER_STACKS as u128;
        // with zero participation, should scale to 25% of liquid
        assert_eq!(
            StacksChainState::get_reward_threshold_and_participation(
                &test_pox_constants,
                &[],
                liquid
            )
            .0,
            50_000 * MICROSTACKS_PER_STACKS as u128
        );
        // should be the same at 25% participation
        assert_eq!(
            StacksChainState::get_reward_threshold_and_participation(
                &test_pox_constants,
                &[(rand_addr(), liquid / 4)],
                liquid
            )
            .0,
            50_000 * MICROSTACKS_PER_STACKS as u128
        );
        // but not at 30% participation
        assert_eq!(
            StacksChainState::get_reward_threshold_and_participation(
                &test_pox_constants,
                &[
                    (rand_addr(), liquid / 4),
                    (rand_addr(), 10_000_000 * (MICROSTACKS_PER_STACKS as u128))
                ],
                liquid
            )
            .0,
            60_000 * MICROSTACKS_PER_STACKS as u128
        );

        // bump by just a little bit, should go to the next threshold step
        assert_eq!(
            StacksChainState::get_reward_threshold_and_participation(
                &test_pox_constants,
                &[
                    (rand_addr(), liquid / 4),
                    (rand_addr(), (MICROSTACKS_PER_STACKS as u128))
                ],
                liquid
            )
            .0,
            60_000 * MICROSTACKS_PER_STACKS as u128
        );

        // bump by just a little bit, should go to the next threshold step
        assert_eq!(
            StacksChainState::get_reward_threshold_and_participation(
                &test_pox_constants,
                &[(rand_addr(), liquid)],
                liquid
            )
            .0,
            200_000 * MICROSTACKS_PER_STACKS as u128
        );
    }

    fn rand_addr() -> StacksAddress {
        key_to_stacks_addr(&StacksPrivateKey::new())
    }

    pub fn key_to_stacks_addr(key: &StacksPrivateKey) -> StacksAddress {
        StacksAddress::from_public_keys(
            C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
            &AddressHashMode::SerializeP2PKH,
            1,
            &vec![StacksPublicKey::from_private(key)],
        )
        .unwrap()
    }

    pub fn instantiate_pox_peer<'a>(
        burnchain: &Burnchain,
        test_name: &str,
        port: u16,
    ) -> (TestPeer<'a>, Vec<StacksPrivateKey>) {
        instantiate_pox_peer_with_epoch(burnchain, test_name, port, None, None)
    }

    pub fn instantiate_pox_peer_with_epoch<'a>(
        burnchain: &Burnchain,
        test_name: &str,
        port: u16,
        epochs: Option<Vec<StacksEpoch>>,
        observer: Option<&'a TestEventObserver>,
    ) -> (TestPeer<'a>, Vec<StacksPrivateKey>) {
        let mut peer_config = TestPeerConfig::new(test_name, port, port + 1);
        peer_config.burnchain = burnchain.clone();
        peer_config.epochs = epochs;
        peer_config.setup_code = format!(
            "(contract-call? .pox set-burnchain-parameters u{} u{} u{} u{})",
            burnchain.first_block_height,
            burnchain.pox_constants.prepare_length,
            burnchain.pox_constants.reward_cycle_length,
            burnchain.pox_constants.pox_rejection_fraction
        );

        test_debug!("Setup code: '{}'", &peer_config.setup_code);

        let keys = [
            StacksPrivateKey::from_hex(
                "7e3ee1f2a0ae11b785a1f0e725a9b3ab0a5fd6cc057d43763b0a85f256fdec5d01",
            )
            .unwrap(),
            StacksPrivateKey::from_hex(
                "11d055ac8b0ab4f04c5eb5ea4b4def9c60ae338355d81c9411b27b4f49da2a8301",
            )
            .unwrap(),
            StacksPrivateKey::from_hex(
                "00eed368626b96e482944e02cc136979973367491ea923efb57c482933dd7c0b01",
            )
            .unwrap(),
            StacksPrivateKey::from_hex(
                "00380ff3c05350ee313f60f30313acb4b5fc21e50db4151bf0de4cd565eb823101",
            )
            .unwrap(),
        ];

        let addrs: Vec<StacksAddress> = keys.iter().map(|ref pk| key_to_stacks_addr(pk)).collect();

        let balances: Vec<(PrincipalData, u64)> = addrs
            .clone()
            .into_iter()
            .map(|addr| (addr.into(), (1024 * POX_THRESHOLD_STEPS_USTX) as u64))
            .collect();

        peer_config.initial_balances = balances;
        let peer = TestPeer::new_with_observer(peer_config, observer);

        (peer, keys.to_vec())
    }

    pub fn eval_at_tip(peer: &mut TestPeer, boot_contract: &str, expr: &str) -> Value {
        let sortdb = peer.sortdb.take().unwrap();
        let (consensus_hash, block_bhh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
        let stacks_block_id = StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);
        let iconn = sortdb.index_conn();
        let value = peer.chainstate().clarity_eval_read_only(
            &iconn,
            &stacks_block_id,
            &boot_code_id(boot_contract, false),
            expr,
        );
        peer.sortdb = Some(sortdb);
        value
    }

    fn contract_id(addr: &StacksAddress, name: &str) -> QualifiedContractIdentifier {
        QualifiedContractIdentifier::new(
            StandardPrincipalData::from(addr.clone()),
            ContractName::try_from(name.to_string()).unwrap(),
        )
    }

    fn eval_contract_at_tip(
        peer: &mut TestPeer,
        addr: &StacksAddress,
        name: &str,
        expr: &str,
    ) -> Value {
        let sortdb = peer.sortdb.take().unwrap();
        let (consensus_hash, block_bhh) =
            SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
        let stacks_block_id = StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);
        let iconn = sortdb.index_conn();
        let value = peer.chainstate().clarity_eval_read_only(
            &iconn,
            &stacks_block_id,
            &contract_id(addr, name),
            expr,
        );
        peer.sortdb = Some(sortdb);
        value
    }

    pub fn get_liquid_ustx(peer: &mut TestPeer) -> u128 {
        let value = eval_at_tip(peer, "pox", "stx-liquid-supply");
        if let Value::UInt(inner_uint) = value {
            return inner_uint;
        } else {
            panic!("stx-liquid-supply isn't a uint");
        }
    }

    pub fn get_balance(peer: &mut TestPeer, addr: &PrincipalData) -> u128 {
        let value = eval_at_tip(
            peer,
            "pox",
            &format!("(stx-get-balance '{})", addr.to_string()),
        );
        if let Value::UInt(balance) = value {
            return balance;
        } else {
            panic!("stx-get-balance isn't a uint");
        }
    }

    pub fn get_stacker_info(
        peer: &mut TestPeer,
        addr: &PrincipalData,
    ) -> Option<(u128, (AddressHashMode, Hash160), u128, u128)> {
        let value_opt = eval_at_tip(
            peer,
            "pox",
            &format!("(get-stacker-info '{})", addr.to_string()),
        );
        let data = if let Some(d) = value_opt.expect_optional() {
            d
        } else {
            return None;
        };

        let data = data.expect_tuple();

        let amount_ustx = data.get("amount-ustx").unwrap().to_owned().expect_u128();
        let pox_addr = tuple_to_pox_addr(data.get("pox-addr").unwrap().to_owned().expect_tuple());
        let lock_period = data.get("lock-period").unwrap().to_owned().expect_u128();
        let first_reward_cycle = data
            .get("first-reward-cycle")
            .unwrap()
            .to_owned()
            .expect_u128();
        Some((amount_ustx, pox_addr, lock_period, first_reward_cycle))
    }

    pub fn with_sortdb<F, R>(peer: &mut TestPeer, todo: F) -> R
    where
        F: FnOnce(&mut StacksChainState, &SortitionDB) -> R,
    {
        let sortdb = peer.sortdb.take().unwrap();
        let r = todo(peer.chainstate(), &sortdb);
        peer.sortdb = Some(sortdb);
        r
    }

    pub fn get_account(peer: &mut TestPeer, addr: &PrincipalData) -> StacksAccount {
        let account = with_sortdb(peer, |ref mut chainstate, ref mut sortdb| {
            let (consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
            let stacks_block_id =
                StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);
            chainstate
                .with_read_only_clarity_tx(&sortdb.index_conn(), &stacks_block_id, |clarity_tx| {
                    StacksChainState::get_account(clarity_tx, addr)
                })
                .unwrap()
        });
        account
    }

    fn get_contract(peer: &mut TestPeer, addr: &QualifiedContractIdentifier) -> Option<Contract> {
        let contract_opt = with_sortdb(peer, |ref mut chainstate, ref mut sortdb| {
            let (consensus_hash, block_bhh) =
                SortitionDB::get_canonical_stacks_chain_tip_hash(sortdb.conn()).unwrap();
            let stacks_block_id =
                StacksBlockHeader::make_index_block_hash(&consensus_hash, &block_bhh);
            chainstate
                .with_read_only_clarity_tx(&sortdb.index_conn(), &stacks_block_id, |clarity_tx| {
                    StacksChainState::get_contract(clarity_tx, addr).unwrap()
                })
                .unwrap()
        });
        contract_opt
    }

    fn make_pox_addr(addr_version: AddressHashMode, addr_bytes: Hash160) -> Value {
        Value::Tuple(
            TupleData::from_data(vec![
                (
                    ClarityName::try_from("version".to_owned()).unwrap(),
                    Value::buff_from_byte(addr_version as u8),
                ),
                (
                    ClarityName::try_from("hashbytes".to_owned()).unwrap(),
                    Value::Sequence(SequenceData::Buffer(BuffData {
                        data: addr_bytes.as_bytes().to_vec(),
                    })),
                ),
            ])
            .unwrap(),
        )
    }

    pub fn make_pox_lockup(
        key: &StacksPrivateKey,
        nonce: u64,
        amount: u128,
        addr_version: AddressHashMode,
        addr_bytes: Hash160,
        lock_period: u128,
        burn_ht: u64,
    ) -> StacksTransaction {
        // (define-public (stack-stx (amount-ustx uint)
        //                           (pox-addr (tuple (version (buff 1)) (hashbytes (buff 20))))
        //                           (lock-period uint))
        make_pox_contract_call(
            key,
            nonce,
            "stack-stx",
            vec![
                Value::UInt(amount),
                make_pox_addr(addr_version, addr_bytes),
                Value::UInt(burn_ht as u128),
                Value::UInt(lock_period),
            ],
        )
    }

    pub fn make_pox_2_lockup(
        key: &StacksPrivateKey,
        nonce: u64,
        amount: u128,
        addr_version: AddressHashMode,
        addr_bytes: Hash160,
        lock_period: u128,
        burn_ht: u64,
    ) -> StacksTransaction {
        // (define-public (stack-stx (amount-ustx uint)
        //                           (pox-addr (tuple (version (buff 1)) (hashbytes (buff 20))))
        //                           (lock-period uint))
        let payload = TransactionPayload::new_contract_call(
            boot_code_test_addr(),
            POX_2_NAME,
            "stack-stx",
            vec![
                Value::UInt(amount),
                make_pox_addr(addr_version, addr_bytes),
                Value::UInt(burn_ht as u128),
                Value::UInt(lock_period),
            ],
        )
        .unwrap();

        make_tx(key, nonce, 0, payload)
    }

    pub fn make_pox_2_extend(
        key: &StacksPrivateKey,
        nonce: u64,
        addr_version: AddressHashMode,
        addr_bytes: Hash160,
        lock_period: u128,
    ) -> StacksTransaction {
        // (define-public (stack-stx (amount-ustx uint)
        //                           (pox-addr (tuple (version (buff 1)) (hashbytes (buff 20))))
        //                           (lock-period uint))
        let payload = TransactionPayload::new_contract_call(
            boot_code_test_addr(),
            "pox-2",
            "stack-extend",
            vec![
                Value::UInt(lock_period),
                make_pox_addr(addr_version, addr_bytes),
            ],
        )
        .unwrap();

        make_tx(key, nonce, 0, payload)
    }

    fn make_tx(
        key: &StacksPrivateKey,
        nonce: u64,
        tx_fee: u64,
        payload: TransactionPayload,
    ) -> StacksTransaction {
        let auth = TransactionAuth::from_p2pkh(key).unwrap();
        let addr = auth.origin().address_testnet();
        let mut tx = StacksTransaction::new(TransactionVersion::Testnet, auth, payload);
        tx.chain_id = 0x80000000;
        tx.auth.set_origin_nonce(nonce);
        tx.set_post_condition_mode(TransactionPostConditionMode::Allow);
        tx.set_tx_fee(tx_fee);

        let mut tx_signer = StacksTransactionSigner::new(&tx);
        tx_signer.sign_origin(key).unwrap();
        tx_signer.get_tx().unwrap()
    }

    pub fn make_pox_contract_call(
        key: &StacksPrivateKey,
        nonce: u64,
        function_name: &str,
        args: Vec<Value>,
    ) -> StacksTransaction {
        let payload = TransactionPayload::new_contract_call(
            boot_code_test_addr(),
            "pox",
            function_name,
            args,
        )
        .unwrap();

        make_tx(key, nonce, 0, payload)
    }

    pub fn make_pox_2_contract_call(
        key: &StacksPrivateKey,
        nonce: u64,
        function_name: &str,
        args: Vec<Value>,
    ) -> StacksTransaction {
        let payload = TransactionPayload::new_contract_call(
            boot_code_test_addr(),
            POX_2_NAME,
            function_name,
            args,
        )
        .unwrap();

        make_tx(key, nonce, 0, payload)
    }

    // make a stream of invalid pox-lockup transactions
    fn make_invalid_pox_lockups(key: &StacksPrivateKey, mut nonce: u64) -> Vec<StacksTransaction> {
        let mut ret = vec![];

        let amount = 1;
        let lock_period = 1;
        let addr_bytes = Hash160([0u8; 20]);

        let bad_pox_addr_version = Value::Tuple(
            TupleData::from_data(vec![
                (
                    ClarityName::try_from("version".to_owned()).unwrap(),
                    Value::UInt(100),
                ),
                (
                    ClarityName::try_from("hashbytes".to_owned()).unwrap(),
                    Value::Sequence(SequenceData::Buffer(BuffData {
                        data: addr_bytes.as_bytes().to_vec(),
                    })),
                ),
            ])
            .unwrap(),
        );

        let generator = |amount, pox_addr, lock_period, nonce| {
            make_pox_contract_call(
                key,
                nonce,
                "stack-stx",
                vec![Value::UInt(amount), pox_addr, Value::UInt(lock_period)],
            )
        };

        let bad_pox_addr_tx = generator(amount, bad_pox_addr_version, lock_period, nonce);
        ret.push(bad_pox_addr_tx);
        nonce += 1;

        let bad_lock_period_short = generator(
            amount,
            make_pox_addr(AddressHashMode::SerializeP2PKH, addr_bytes.clone()),
            0,
            nonce,
        );
        ret.push(bad_lock_period_short);
        nonce += 1;

        let bad_lock_period_long = generator(
            amount,
            make_pox_addr(AddressHashMode::SerializeP2PKH, addr_bytes.clone()),
            13,
            nonce,
        );
        ret.push(bad_lock_period_long);
        nonce += 1;

        let bad_amount = generator(
            0,
            make_pox_addr(AddressHashMode::SerializeP2PKH, addr_bytes.clone()),
            1,
            nonce,
        );
        ret.push(bad_amount);

        ret
    }

    fn make_bare_contract(
        key: &StacksPrivateKey,
        nonce: u64,
        tx_fee: u64,
        name: &str,
        code: &str,
    ) -> StacksTransaction {
        let payload = TransactionPayload::new_smart_contract(name, code).unwrap();
        make_tx(key, nonce, tx_fee, payload)
    }

    fn make_token_transfer(
        key: &StacksPrivateKey,
        nonce: u64,
        tx_fee: u64,
        dest: PrincipalData,
        amount: u64,
    ) -> StacksTransaction {
        let payload = TransactionPayload::TokenTransfer(dest, amount, TokenTransferMemo([0u8; 34]));
        make_tx(key, nonce, tx_fee, payload)
    }

    fn make_pox_lockup_contract(
        key: &StacksPrivateKey,
        nonce: u64,
        name: &str,
    ) -> StacksTransaction {
        let contract = format!("
        (define-public (do-contract-lockup (amount-ustx uint) (pox-addr (tuple (version (buff 1)) (hashbytes (buff 20)))) (lock-period uint))
            (let (
                (this-contract (as-contract tx-sender))
            )
            (begin
                ;; take the stx from the tx-sender
                
                (unwrap-panic (stx-transfer? amount-ustx tx-sender this-contract))

                ;; this contract stacks the stx given to it
                (as-contract
                    (contract-call? '{}.pox stack-stx amount-ustx pox-addr burn-block-height lock-period))
            ))
        )

        ;; get back STX from this contract
        (define-public (withdraw-stx (amount-ustx uint))
            (let (
                (recipient tx-sender)
            )
            (begin
                (unwrap-panic
                    (as-contract
                        (stx-transfer? amount-ustx tx-sender recipient)))
                (ok true)
            ))
        )
        ", boot_code_test_addr());
        let contract_tx = make_bare_contract(key, nonce, 0, name, &contract);
        contract_tx
    }

    // call after make_pox_lockup_contract gets mined
    fn make_pox_lockup_contract_call(
        key: &StacksPrivateKey,
        nonce: u64,
        contract_addr: &StacksAddress,
        name: &str,
        amount: u128,
        addr_version: AddressHashMode,
        addr_bytes: Hash160,
        lock_period: u128,
    ) -> StacksTransaction {
        let payload = TransactionPayload::new_contract_call(
            contract_addr.clone(),
            name,
            "do-contract-lockup",
            vec![
                Value::UInt(amount),
                make_pox_addr(addr_version, addr_bytes),
                Value::UInt(lock_period),
            ],
        )
        .unwrap();
        make_tx(key, nonce, 0, payload)
    }

    // call after make_pox_lockup_contract gets mined
    fn make_pox_withdraw_stx_contract_call(
        key: &StacksPrivateKey,
        nonce: u64,
        contract_addr: &StacksAddress,
        name: &str,
        amount: u128,
    ) -> StacksTransaction {
        let payload = TransactionPayload::new_contract_call(
            contract_addr.clone(),
            name,
            "withdraw-stx",
            vec![Value::UInt(amount)],
        )
        .unwrap();
        make_tx(key, nonce, 0, payload)
    }

    fn make_pox_reject(key: &StacksPrivateKey, nonce: u64) -> StacksTransaction {
        // (define-public (reject-pox))
        make_pox_contract_call(key, nonce, "reject-pox", vec![])
    }

    pub fn get_reward_addresses_with_par_tip(
        state: &mut StacksChainState,
        burnchain: &Burnchain,
        sortdb: &SortitionDB,
        block_id: &StacksBlockId,
    ) -> Result<Vec<(StacksAddress, u128)>, Error> {
        let burn_block_height = get_par_burn_block_height(state, block_id);
        state
            .get_reward_addresses(burnchain, sortdb, burn_block_height, block_id)
            .and_then(|mut addrs| {
                addrs.sort_by_key(|k| k.0.bytes.0);
                Ok(addrs)
            })
    }

    pub fn get_parent_tip(
        parent_opt: &Option<&StacksBlock>,
        chainstate: &StacksChainState,
        sortdb: &SortitionDB,
    ) -> StacksHeaderInfo {
        let tip = SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).unwrap();
        let parent_tip = match parent_opt {
            None => StacksChainState::get_genesis_header_info(chainstate.db()).unwrap(),
            Some(block) => {
                let ic = sortdb.index_conn();
                let snapshot = SortitionDB::get_block_snapshot_for_winning_stacks_block(
                    &ic,
                    &tip.sortition_id,
                    &block.block_hash(),
                )
                .unwrap()
                .unwrap(); // succeeds because we don't fork
                StacksChainState::get_anchored_block_header_info(
                    chainstate.db(),
                    &snapshot.consensus_hash,
                    &snapshot.winning_stacks_block_hash,
                )
                .unwrap()
                .unwrap()
            }
        };
        parent_tip
    }

    #[test]
    fn test_liquid_ustx() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, keys) = instantiate_pox_peer(&burnchain, "test-liquid-ustx", 6000);

        let num_blocks = 10;
        let mut expected_liquid_ustx = 1024 * POX_THRESHOLD_STEPS_USTX * (keys.len() as u128);
        let mut missed_initial_blocks = 0;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);

                    if tip.total_burn > 0 && missed_initial_blocks == 0 {
                        eprintln!("Missed initial blocks: {}", missed_initial_blocks);
                        missed_initial_blocks = tip.block_height;
                    }

                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let block_txs = vec![coinbase_tx];

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (burn_ht, _, _) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let liquid_ustx = get_liquid_ustx(&mut peer);
            assert_eq!(liquid_ustx, expected_liquid_ustx);

            if tenure_id >= MINER_REWARD_MATURITY as usize {
                let block_reward = 1_000 * MICROSTACKS_PER_STACKS as u128;
                let expected_bonus = (missed_initial_blocks as u128 * block_reward)
                    / (INITIAL_MINING_BONUS_WINDOW as u128);
                // add mature coinbases
                expected_liquid_ustx += block_reward + expected_bonus;
            }
        }
    }

    #[test]
    fn test_lockups() {
        let mut peer_config = TestPeerConfig::new("test_lockups", 2000, 2001);
        let alice = StacksAddress::from_string("STVK1K405H6SK9NKJAP32GHYHDJ98MMNP8Y6Z9N0").unwrap();
        let bob = StacksAddress::from_string("ST76D2FMXZ7D2719PNE4N71KPSX84XCCNCMYC940").unwrap();
        peer_config.initial_lockups = vec![
            ChainstateAccountLockup::new(alice.into(), 1000, 1),
            ChainstateAccountLockup::new(bob, 1000, 1),
            ChainstateAccountLockup::new(alice, 1000, 2),
            ChainstateAccountLockup::new(bob, 1000, 3),
            ChainstateAccountLockup::new(alice, 1000, 4),
            ChainstateAccountLockup::new(bob, 1000, 4),
            ChainstateAccountLockup::new(bob, 1000, 5),
            ChainstateAccountLockup::new(alice, 1000, 6),
            ChainstateAccountLockup::new(alice, 1000, 7),
        ];
        let mut peer = TestPeer::new(peer_config);

        let num_blocks = 8;
        let mut missed_initial_blocks = 0;

        for tenure_id in 0..num_blocks {
            let alice_balance = get_balance(&mut peer, &alice.to_account_principal());
            let bob_balance = get_balance(&mut peer, &bob.to_account_principal());
            match tenure_id {
                0 => {
                    assert_eq!(alice_balance, 0);
                    assert_eq!(bob_balance, 0);
                }
                1 => {
                    assert_eq!(alice_balance, 1000);
                    assert_eq!(bob_balance, 1000);
                }
                2 => {
                    assert_eq!(alice_balance, 2000);
                    assert_eq!(bob_balance, 1000);
                }
                3 => {
                    assert_eq!(alice_balance, 2000);
                    assert_eq!(bob_balance, 2000);
                }
                4 => {
                    assert_eq!(alice_balance, 3000);
                    assert_eq!(bob_balance, 3000);
                }
                5 => {
                    assert_eq!(alice_balance, 3000);
                    assert_eq!(bob_balance, 4000);
                }
                6 => {
                    assert_eq!(alice_balance, 4000);
                    assert_eq!(bob_balance, 4000);
                }
                7 => {
                    assert_eq!(alice_balance, 5000);
                    assert_eq!(bob_balance, 4000);
                }
                _ => {
                    assert_eq!(alice_balance, 5000);
                    assert_eq!(bob_balance, 4000);
                }
            }
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);

                    if tip.total_burn > 0 && missed_initial_blocks == 0 {
                        eprintln!("Missed initial blocks: {}", missed_initial_blocks);
                        missed_initial_blocks = tip.block_height;
                    }

                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let block_txs = vec![coinbase_tx];

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (burn_ht, _, _) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);
        }
    }

    #[test]
    fn test_hook_special_contract_call() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 3;
        burnchain.pox_constants.prepare_length = 1;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-hook-special-contract-call", 6007);

        let num_blocks = 15;

        let alice = keys.pop().unwrap();

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(|ref mut miner, ref mut sortdb, ref mut chainstate, vrf_proof, ref parent_opt, ref parent_microblock_header_opt| {
                let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                let coinbase_tx = make_coinbase(miner, tenure_id);

                let mut block_txs = vec![
                    coinbase_tx
                ];

                if tenure_id == 1 {
                    let alice_lockup_1 = make_pox_lockup(&alice, 0, 512 * POX_THRESHOLD_STEPS_USTX, AddressHashMode::SerializeP2PKH, key_to_stacks_addr(&alice).bytes, 1, tip.block_height);
                    block_txs.push(alice_lockup_1);
                }
                if tenure_id == 2 {
                    let alice_test_tx = make_bare_contract(&alice, 1, 0, "nested-stacker", &format!(
                        "(define-public (nested-stack-stx)
                            (contract-call? '{}.pox stack-stx u5120000000000 (tuple (version 0x00) (hashbytes 0xffffffffffffffffffffffffffffffffffffffff)) burn-block-height u1))", boot_code_test_addr()));

                    block_txs.push(alice_test_tx);
                }
                if tenure_id == 8 {
                    // alice locks 512 * 10_000 * POX_THRESHOLD_STEPS_USTX uSTX through her contract
                    let cc_payload = TransactionPayload::new_contract_call(key_to_stacks_addr(&alice),
                                                                           "nested-stacker",
                                                                           "nested-stack-stx",
                                                                           vec![]).unwrap();
                    let tx = make_tx(&alice, 2, 0, cc_payload.clone());

                    block_txs.push(tx);

                    // the above tx _should_ error, because alice hasn't authorized that contract to stack
                    //   try again with auth -> deauth -> auth
                    let alice_contract: Value = contract_id(&key_to_stacks_addr(&alice), "nested-stacker").into();

                    let alice_allowance = make_pox_contract_call(&alice, 3, "allow-contract-caller", vec![alice_contract.clone(), Value::none()]);
                    let alice_disallowance = make_pox_contract_call(&alice, 4, "disallow-contract-caller", vec![alice_contract.clone()]);
                    block_txs.push(alice_allowance);
                    block_txs.push(alice_disallowance);

                    let tx = make_tx(&alice, 5, 0, cc_payload.clone());
                    block_txs.push(tx);

                    let alice_allowance = make_pox_contract_call(&alice, 6, "allow-contract-caller", vec![alice_contract.clone(), Value::none()]);
                    let tx = make_tx(&alice, 7, 0, cc_payload.clone()); // should be allowed!
                    block_txs.push(alice_allowance);
                    block_txs.push(tx);

                }

                let block_builder = StacksBlockBuilder::make_regtest_block_builder(&parent_tip, vrf_proof, tip.total_burn, microblock_pubkeyhash).unwrap();
                let (anchored_block, _size, _cost) = StacksBlockBuilder::make_anchored_block_from_txs(block_builder, chainstate, &sortdb.index_conn(), block_txs).unwrap();
                (anchored_block, vec![])
            });

            peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            // before/after alice's tokens lock
            if tenure_id == 0 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id == 1 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 512 * POX_THRESHOLD_STEPS_USTX);
            }
            // before/after alice's tokens unlock
            else if tenure_id == 4 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 512 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id == 5 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
            }
            // before/after contract lockup
            else if tenure_id == 7 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id == 8 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 512 * POX_THRESHOLD_STEPS_USTX);
            }
            // before/after contract-locked tokens unlock
            else if tenure_id == 13 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 512 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id == 14 {
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
            }
        }
    }

    #[test]
    fn test_liquid_ustx_burns() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) = instantiate_pox_peer(&burnchain, "test-liquid-ustx", 6026);

        let num_blocks = 10;
        let mut expected_liquid_ustx = 1024 * POX_THRESHOLD_STEPS_USTX * (keys.len() as u128);
        let mut missed_initial_blocks = 0;

        let alice = keys.pop().unwrap();

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);

                    if tip.total_burn > 0 && missed_initial_blocks == 0 {
                        eprintln!("Missed initial blocks: {}", missed_initial_blocks);
                        missed_initial_blocks = tip.block_height;
                    }

                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let burn_tx = make_bare_contract(
                        &alice,
                        tenure_id as u64,
                        0,
                        &format!("alice-burns-{}", &tenure_id),
                        "(stx-burn? u1 tx-sender)",
                    );

                    let block_txs = vec![coinbase_tx, burn_tx];

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let liquid_ustx = get_liquid_ustx(&mut peer);

            expected_liquid_ustx -= 1;
            assert_eq!(liquid_ustx, expected_liquid_ustx);

            if tenure_id >= MINER_REWARD_MATURITY as usize {
                let block_reward = 1_000 * MICROSTACKS_PER_STACKS as u128;
                let expected_bonus = (missed_initial_blocks as u128) * block_reward
                    / (INITIAL_MINING_BONUS_WINDOW as u128);
                // add mature coinbases
                expected_liquid_ustx += block_reward + expected_bonus;
            }
        }
    }

    pub fn get_par_burn_block_height(
        state: &mut StacksChainState,
        block_id: &StacksBlockId,
    ) -> u64 {
        let parent_block_id = StacksChainState::get_parent_block_id(state.db(), block_id)
            .unwrap()
            .unwrap();

        let parent_header_info =
            StacksChainState::get_stacks_block_header_info_by_index_block_hash(
                state.db(),
                &parent_block_id,
            )
            .unwrap()
            .unwrap();

        parent_header_info.burn_header_height as u64
    }

    #[test]
    fn test_pox_lockup_single_tx_sender() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-single-tx-sender", 6002);

        let num_blocks = 10;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();

        let mut alice_reward_cycle = 0;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let mut block_txs = vec![coinbase_tx];

                    if tenure_id == 1 {
                        // Alice locks up exactly 25% of the liquid STX supply, so this should succeed.
                        let alice_lockup = make_pox_lockup(
                            &alice,
                            0,
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&alice).bytes,
                            12,
                            tip.block_height,
                        );
                        block_txs.push(alice_lockup);
                    }

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops);
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // Alice has not locked up STX
                    let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(
                        alice_account.stx_balance.amount_unlocked(),
                        1024 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(alice_account.stx_balance.amount_locked(), 0);
                    assert_eq!(alice_account.stx_balance.unlock_height(), 0);
                }
                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                alice_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                eprintln!(
                    "\nalice reward cycle: {}\ncur reward cycle: {}\n",
                    alice_reward_cycle, cur_reward_cycle
                );
            } else {
                // Alice's address is locked as of the next reward cycle
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                // Alice has locked up STX no matter what
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 0);

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                let total_stacked = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.test_get_total_ustx_stacked(
                        sortdb,
                        &tip_index_block,
                        cur_reward_cycle,
                    )
                })
                .unwrap();

                eprintln!("\ntenure: {}\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\ntotal-stacked: {}\n", tenure_id, cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx, total_stacked);

                if cur_reward_cycle >= alice_reward_cycle {
                    // this will grow as more miner rewards are unlocked, so be wary
                    if tenure_id >= (MINER_REWARD_MATURITY + 1) as usize {
                        // miner rewards increased liquid supply, so less than 25% is locked.
                        // minimum participation decreases.
                        assert!(total_liquid_ustx > 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                        assert_eq!(min_ustx, total_liquid_ustx / 480);
                    } else {
                        // still at 25% or more locked
                        assert!(total_liquid_ustx <= 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                    }

                    let (amount_ustx, pox_addr, lock_period, first_reward_cycle) =
                        get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into()).unwrap();
                    eprintln!("\nAlice: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, first_reward_cycle);

                    // one reward address, and it's Alice's
                    // either way, there's a single reward address
                    assert_eq!(reward_addrs.len(), 1);
                    assert_eq!(
                        (reward_addrs[0].0).version,
                        AddressHashMode::SerializeP2PKH.to_version_testnet()
                    );
                    assert_eq!((reward_addrs[0].0).bytes, key_to_stacks_addr(&alice).bytes);
                    assert_eq!(reward_addrs[0].1, 1024 * POX_THRESHOLD_STEPS_USTX);

                    // Lock-up is consistent with stacker state
                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(
                        alice_account.stx_balance.amount_locked(),
                        1024 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.unlock_height() as u128,
                        (first_reward_cycle + lock_period)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );
                } else {
                    // no reward addresses
                    assert_eq!(reward_addrs.len(), 0);
                }
            }
        }
    }

    #[test]
    fn test_pox_lockup_single_tx_sender_100() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 4; // 4 reward slots
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;
        assert_eq!(burnchain.pox_constants.reward_slots(), 4);

        let (mut peer, keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-single-tx-sender-100", 6026);

        let num_blocks = 20;

        let mut lockup_reward_cycle = 0;
        let mut prepared = false;
        let mut rewarded = false;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let cur_reward_cycle = burnchain
                .block_height_to_reward_cycle(tip.block_height)
                .unwrap() as u128;

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let mut block_txs = vec![coinbase_tx];

                    if tenure_id == 1 {
                        // all peers lock at the same time
                        for key in keys.iter() {
                            let lockup = make_pox_lockup(
                                key,
                                0,
                                1024 * POX_THRESHOLD_STEPS_USTX,
                                AddressHashMode::SerializeP2PKH,
                                key_to_stacks_addr(key).bytes,
                                12,
                                tip.block_height,
                            );
                            block_txs.push(lockup);
                        }
                    }

                    let block_builder = StacksBlockBuilder::make_block_builder(
                        false,
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (burn_height, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            if burnchain.is_in_prepare_phase(burn_height) {
                // make sure we burn!
                for op in burn_ops.iter() {
                    if let BlockstackOperationType::LeaderBlockCommit(ref opdata) = &op {
                        eprintln!("prepare phase {}: {:?}", burn_height, opdata);
                        assert!(opdata.all_outputs_burn());
                        assert!(opdata.burn_fee > 0);

                        if tenure_id > 1 && cur_reward_cycle > lockup_reward_cycle {
                            prepared = true;
                        }
                    }
                }
            } else {
                // no burns -- 100% commitment
                for op in burn_ops.iter() {
                    if let BlockstackOperationType::LeaderBlockCommit(ref opdata) = &op {
                        eprintln!("reward phase {}: {:?}", burn_height, opdata);
                        if tenure_id > 1 && cur_reward_cycle > lockup_reward_cycle {
                            assert!(!opdata.all_outputs_burn());
                            rewarded = true;
                        } else {
                            // lockup hasn't happened yet
                            assert!(opdata.all_outputs_burn());
                        }

                        assert!(opdata.burn_fee > 0);
                    }
                }
            }

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // No locks have taken place
                    for key in keys.iter() {
                        // has not locked up STX
                        let balance = get_balance(&mut peer, &key_to_stacks_addr(&key).into());
                        assert_eq!(balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                        let account = get_account(&mut peer, &key_to_stacks_addr(&key).into());
                        assert_eq!(
                            account.stx_balance.amount_unlocked(),
                            1024 * POX_THRESHOLD_STEPS_USTX
                        );
                        assert_eq!(account.stx_balance.amount_locked(), 0);
                        assert_eq!(account.stx_balance.unlock_height(), 0);
                    }
                }
                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when tokens get stacked
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                lockup_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                eprintln!(
                    "\nlockup reward cycle: {}\ncur reward cycle: {}\n",
                    lockup_reward_cycle, cur_reward_cycle
                );
            } else {
                // all addresses are locked as of the next reward cycle
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                // all keys locked up STX no matter what
                for key in keys.iter() {
                    let balance = get_balance(&mut peer, &key_to_stacks_addr(key).into());
                    assert_eq!(balance, 0);
                }

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                let total_stacked = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.test_get_total_ustx_stacked(
                        sortdb,
                        &tip_index_block,
                        cur_reward_cycle,
                    )
                })
                .unwrap();

                eprintln!("\ntenure: {}\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\ntotal-stacked: {}\n", tenure_id, cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx, total_stacked);

                if cur_reward_cycle >= lockup_reward_cycle {
                    // this will grow as more miner rewards are unlocked, so be wary
                    if tenure_id >= (MINER_REWARD_MATURITY + 1) as usize {
                        // miner rewards increased liquid supply, so less than 25% is locked.
                        // minimum participation decreases.
                        assert!(total_liquid_ustx > 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                        assert_eq!(min_ustx, total_liquid_ustx / 480);
                    } else {
                        // still at 25% or more locked
                        assert!(total_liquid_ustx <= 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                    }

                    assert_eq!(reward_addrs.len(), 4);
                    let mut all_addrbytes = HashSet::new();
                    for key in keys.iter() {
                        all_addrbytes.insert(key_to_stacks_addr(&key).bytes);
                    }

                    for key in keys.iter() {
                        let (amount_ustx, pox_addr, lock_period, first_reward_cycle) =
                            get_stacker_info(&mut peer, &key_to_stacks_addr(&key).into()).unwrap();
                        eprintln!("\n{}: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", key.to_hex(), amount_ustx, lock_period, &pox_addr, first_reward_cycle);

                        assert_eq!(
                            (reward_addrs[0].0).version,
                            AddressHashMode::SerializeP2PKH.to_version_testnet()
                        );
                        assert!(all_addrbytes.contains(&key_to_stacks_addr(&key).bytes));
                        all_addrbytes.remove(&key_to_stacks_addr(&key).bytes);
                        assert_eq!(reward_addrs[0].1, 1024 * POX_THRESHOLD_STEPS_USTX);

                        // Lock-up is consistent with stacker state
                        let account = get_account(&mut peer, &key_to_stacks_addr(&key).into());
                        assert_eq!(account.stx_balance.amount_unlocked(), 0);
                        assert_eq!(
                            account.stx_balance.amount_locked(),
                            1024 * POX_THRESHOLD_STEPS_USTX
                        );
                        assert_eq!(
                            account.stx_balance.unlock_height() as u128,
                            (first_reward_cycle + lock_period)
                                * (burnchain.pox_constants.reward_cycle_length as u128)
                                + (burnchain.first_block_height as u128)
                        );
                    }

                    assert_eq!(all_addrbytes.len(), 0);
                } else {
                    // no reward addresses
                    assert_eq!(reward_addrs.len(), 0);
                }
            }
        }
        assert!(prepared && rewarded);
    }

    #[test]
    fn test_pox_lockup_contract() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-contract", 6018);

        let num_blocks = 10;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();

        let mut alice_reward_cycle = 0;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let mut block_txs = vec![coinbase_tx];

                    if tenure_id == 1 {
                        // make a contract, and have the contract do the stacking
                        let bob_contract = make_pox_lockup_contract(&bob, 0, "do-lockup");
                        block_txs.push(bob_contract);

                        let alice_stack = make_pox_lockup_contract_call(
                            &alice,
                            0,
                            &key_to_stacks_addr(&bob),
                            "do-lockup",
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&alice).bytes,
                            1,
                        );
                        block_txs.push(alice_stack);
                    }

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // Alice has not locked up STX
                    let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
                }
                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                alice_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                eprintln!(
                    "\nalice reward cycle: {}\ncur reward cycle: {}\n",
                    alice_reward_cycle, cur_reward_cycle
                );
            } else {
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                // Alice's tokens got sent to the contract, so her balance is 0
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 0);

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                let total_stacked = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.test_get_total_ustx_stacked(
                        sortdb,
                        &tip_index_block,
                        cur_reward_cycle,
                    )
                })
                .unwrap();

                eprintln!("\ntenure: {}\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\ntotal-stacked: {}\n", tenure_id, cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx, total_stacked);

                if cur_reward_cycle >= alice_reward_cycle {
                    // alice's tokens are locked for only one reward cycle
                    if cur_reward_cycle == alice_reward_cycle {
                        // this will grow as more miner rewards are unlocked, so be wary
                        if tenure_id >= (MINER_REWARD_MATURITY + 1) as usize {
                            // height at which earliest miner rewards mature.
                            // miner rewards increased liquid supply, so less than 25% is locked.
                            // minimum participation decreases.
                            assert!(total_liquid_ustx > 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                            assert_eq!(min_ustx, total_liquid_ustx / 480);
                        } else {
                            // still at 25% or more locked
                            assert!(total_liquid_ustx <= 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                        }

                        // Alice is _not_ a stacker -- Bob's contract is!
                        let alice_info =
                            get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into());
                        assert!(alice_info.is_none());

                        // Bob is _not_ a stacker either.
                        let bob_info =
                            get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into());
                        assert!(bob_info.is_none());

                        // Bob's contract is a stacker
                        let (amount_ustx, pox_addr, lock_period, first_reward_cycle) =
                            get_stacker_info(
                                &mut peer,
                                &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                            )
                            .unwrap();
                        eprintln!("\nContract: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, first_reward_cycle);

                        // should be consistent with the API call
                        assert_eq!(lock_period, 1);
                        assert_eq!(first_reward_cycle, alice_reward_cycle);
                        assert_eq!(amount_ustx, 1024 * POX_THRESHOLD_STEPS_USTX);

                        // one reward address, and it's Alice's
                        // either way, there's a single reward address
                        assert_eq!(reward_addrs.len(), 1);
                        assert_eq!(
                            (reward_addrs[0].0).version,
                            AddressHashMode::SerializeP2PKH.to_version_testnet()
                        );
                        assert_eq!((reward_addrs[0].0).bytes, key_to_stacks_addr(&alice).bytes);
                        assert_eq!(reward_addrs[0].1, 1024 * POX_THRESHOLD_STEPS_USTX);

                        // contract's address's tokens are locked
                        let contract_balance = get_balance(
                            &mut peer,
                            &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                        );
                        assert_eq!(contract_balance, 0);

                        // Lock-up is consistent with stacker state
                        let contract_account = get_account(
                            &mut peer,
                            &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                        );
                        assert_eq!(contract_account.stx_balance.amount_unlocked(), 0);
                        assert_eq!(
                            contract_account.stx_balance.amount_locked(),
                            1024 * POX_THRESHOLD_STEPS_USTX
                        );
                        assert_eq!(
                            contract_account.stx_balance.unlock_height() as u128,
                            (first_reward_cycle + lock_period)
                                * (burnchain.pox_constants.reward_cycle_length as u128)
                                + (burnchain.first_block_height as u128)
                        );
                    } else {
                        // no longer locked
                        let contract_balance = get_balance(
                            &mut peer,
                            &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                        );
                        assert_eq!(contract_balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                        assert_eq!(reward_addrs.len(), 0);

                        // Lock-up is lazy -- state has not been updated
                        let contract_account = get_account(
                            &mut peer,
                            &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                        );
                        assert_eq!(contract_account.stx_balance.amount_unlocked(), 0);
                        assert_eq!(
                            contract_account.stx_balance.amount_locked(),
                            1024 * POX_THRESHOLD_STEPS_USTX
                        );
                        assert_eq!(
                            contract_account.stx_balance.unlock_height() as u128,
                            (alice_reward_cycle + 1)
                                * (burnchain.pox_constants.reward_cycle_length as u128)
                                + (burnchain.first_block_height as u128)
                        );
                    }
                } else {
                    // no reward addresses
                    assert_eq!(reward_addrs.len(), 0);
                }
            }
        }
    }

    #[test]
    fn test_pox_lockup_multi_tx_sender() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-multi-tx-sender", 6004);

        let num_blocks = 10;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();

        let mut first_reward_cycle = 0;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let mut block_txs = vec![coinbase_tx];

                    if tenure_id == 1 {
                        // Alice locks up exactly 25% of the liquid STX supply, so this should succeed.
                        let alice_lockup = make_pox_lockup(
                            &alice,
                            0,
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&alice).bytes,
                            12,
                            tip.block_height,
                        );
                        block_txs.push(alice_lockup);

                        // Bob locks up 20% of the liquid STX supply, so this should succeed
                        let bob_lockup = make_pox_lockup(
                            &bob,
                            0,
                            (4 * 1024 * POX_THRESHOLD_STEPS_USTX) / 5,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&bob).bytes,
                            12,
                            tip.block_height,
                        );
                        block_txs.push(bob_lockup);
                    }

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // Alice has not locked up STX
                    let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                    // Bob has not locked up STX
                    let bob_balance = get_balance(&mut peer, &key_to_stacks_addr(&bob).into());
                    assert_eq!(bob_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
                }

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                first_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                eprintln!(
                    "\nalice reward cycle: {}\ncur reward cycle: {}\n",
                    first_reward_cycle, cur_reward_cycle
                );
            } else {
                // Alice's and Bob's addresses are locked as of the next reward cycle
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                // Alice and Bob have locked up STX no matter what
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 0);

                let bob_balance = get_balance(&mut peer, &key_to_stacks_addr(&bob).into());
                assert_eq!(
                    bob_balance,
                    1024 * POX_THRESHOLD_STEPS_USTX - (4 * 1024 * POX_THRESHOLD_STEPS_USTX) / 5
                );

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();

                eprintln!(
                    "\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\n",
                    cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx
                );

                if cur_reward_cycle >= first_reward_cycle {
                    // this will grow as more miner rewards are unlocked, so be wary
                    if tenure_id >= (MINER_REWARD_MATURITY + 1) as usize {
                        // miner rewards increased liquid supply, so less than 25% is locked.
                        // minimum participation decreases.
                        assert!(total_liquid_ustx > 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                    } else {
                        // still at 25% or more locked
                        assert!(total_liquid_ustx <= 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                    }

                    // well over 25% locked, so this is always true
                    assert_eq!(min_ustx, total_liquid_ustx / 480);

                    // two reward addresses, and they're Alice's and Bob's.
                    // They are present in sorted order
                    assert_eq!(reward_addrs.len(), 2);
                    assert_eq!(
                        (reward_addrs[1].0).version,
                        AddressHashMode::SerializeP2PKH.to_version_testnet()
                    );
                    assert_eq!((reward_addrs[1].0).bytes, key_to_stacks_addr(&alice).bytes);
                    assert_eq!(reward_addrs[1].1, 1024 * POX_THRESHOLD_STEPS_USTX);

                    assert_eq!(
                        (reward_addrs[0].0).version,
                        AddressHashMode::SerializeP2PKH.to_version_testnet()
                    );
                    assert_eq!((reward_addrs[0].0).bytes, key_to_stacks_addr(&bob).bytes);
                    assert_eq!(reward_addrs[0].1, (4 * 1024 * POX_THRESHOLD_STEPS_USTX) / 5);
                } else {
                    // no reward addresses
                    assert_eq!(reward_addrs.len(), 0);
                }
            }
        }
    }

    #[test]
    fn test_pox_lockup_no_double_stacking() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-no-double-stacking", 6006);

        let num_blocks = 3;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();

        let mut first_reward_cycle = 0;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(|ref mut miner, ref mut sortdb, ref mut chainstate, vrf_proof, ref parent_opt, ref parent_microblock_header_opt| {
                let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                let coinbase_tx = make_coinbase(miner, tenure_id);

                let mut block_txs = vec![
                    coinbase_tx
                ];

                if tenure_id == 1 {
                    // Alice locks up exactly 12.5% of the liquid STX supply, twice.
                    // Only the first one succeeds.
                    let alice_lockup_1 = make_pox_lockup(&alice, 0, 512 * POX_THRESHOLD_STEPS_USTX, AddressHashMode::SerializeP2PKH, key_to_stacks_addr(&alice).bytes, 12, tip.block_height);
                    block_txs.push(alice_lockup_1);

                    // will be rejected
                    let alice_lockup_2 = make_pox_lockup(&alice, 1, 512 * POX_THRESHOLD_STEPS_USTX, AddressHashMode::SerializeP2PKH, key_to_stacks_addr(&alice).bytes, 12, tip.block_height);
                    block_txs.push(alice_lockup_2);

                    // let's make some allowances for contract-calls through smart contracts
                    //   so that the tests in tenure_id == 3 don't just fail on permission checks
                    let alice_test = contract_id(&key_to_stacks_addr(&alice), "alice-test").into();
                    let alice_allowance = make_pox_contract_call(&alice, 2, "allow-contract-caller", vec![alice_test, Value::none()]);

                    let bob_test = contract_id(&key_to_stacks_addr(&bob), "bob-test").into();
                    let bob_allowance = make_pox_contract_call(&bob, 0, "allow-contract-caller", vec![bob_test, Value::none()]);

                    let charlie_test = contract_id(&key_to_stacks_addr(&charlie), "charlie-test").into();
                    let charlie_allowance = make_pox_contract_call(&charlie, 0, "allow-contract-caller", vec![charlie_test, Value::none()]);

                    block_txs.push(alice_allowance);
                    block_txs.push(bob_allowance);
                    block_txs.push(charlie_allowance);
                }
                if tenure_id == 2 {
                    // should pass -- there's no problem with Bob adding more stacking power to Alice's PoX address
                    let bob_test_tx = make_bare_contract(&bob, 1, 0, "bob-test", &format!(
                        "(define-data-var test-run bool false)
                         (define-data-var test-result int -1)
                         (let ((result
                                (contract-call? '{}.pox stack-stx u10240000000000 (tuple (version 0x00) (hashbytes 0xae1593226f85e49a7eaff5b633ff687695438cc9)) burn-block-height u12)))
                              (var-set test-result
                                       (match result ok_value -1 err_value err_value))
                              (var-set test-run true))
                        ", boot_code_test_addr().to_string()));

                    block_txs.push(bob_test_tx);

                    // should fail -- Alice has already stacked.
                    //    expect err 3
                    let alice_test_tx = make_bare_contract(&alice, 3, 0, "alice-test", &format!(
                        "(define-data-var test-run bool false)
                         (define-data-var test-result int -1)
                         (let ((result
                                (contract-call? '{}.pox stack-stx u512000000 (tuple (version 0x00) (hashbytes 0xffffffffffffffffffffffffffffffffffffffff)) burn-block-height u12)))
                              (var-set test-result
                                       (match result ok_value -1 err_value err_value))
                              (var-set test-run true))
                        ", boot_code_test_addr().to_string()));

                    block_txs.push(alice_test_tx);

                    // should fail -- Charlie doesn't have enough uSTX
                    //     expect err 1
                    let charlie_test_tx = make_bare_contract(&charlie, 1, 0, "charlie-test", &format!(
                        "(define-data-var test-run bool false)
                         (define-data-var test-result int -1)
                         (let ((result
                                (contract-call? '{}.pox stack-stx u10240000000001 (tuple (version 0x00) (hashbytes 0xfefefefefefefefefefefefefefefefefefefefe)) burn-block-height u12)))
                              (var-set test-result
                                       (match result ok_value -1 err_value err_value))
                              (var-set test-run true))
                        ", boot_code_test_addr().to_string()));

                    block_txs.push(charlie_test_tx);
                }

                let block_builder = StacksBlockBuilder::make_regtest_block_builder(&parent_tip, vrf_proof, tip.total_burn, microblock_pubkeyhash).unwrap();
                let (anchored_block, _size, _cost) = StacksBlockBuilder::make_anchored_block_from_txs(block_builder, chainstate, &sortdb.index_conn(), block_txs).unwrap();
                (anchored_block, vec![])
            });

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );

            if tenure_id == 0 {
                // Alice has not locked up half of her STX
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id == 1 {
                // only half locked
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 512 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id > 1 {
                // only half locked, still
                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                assert_eq!(alice_balance, 512 * POX_THRESHOLD_STEPS_USTX);
            }

            if tenure_id <= 1 {
                // no reward addresses
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);

                first_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                eprintln!(
                    "\nalice reward cycle: {}\ncur reward cycle: {}\n",
                    first_reward_cycle, cur_reward_cycle
                );
            } else if tenure_id == 2 {
                let alice_test_result = eval_contract_at_tip(
                    &mut peer,
                    &key_to_stacks_addr(&alice),
                    "alice-test",
                    "(var-get test-run)",
                );
                let bob_test_result = eval_contract_at_tip(
                    &mut peer,
                    &key_to_stacks_addr(&bob),
                    "bob-test",
                    "(var-get test-run)",
                );
                let charlie_test_result = eval_contract_at_tip(
                    &mut peer,
                    &key_to_stacks_addr(&charlie),
                    "charlie-test",
                    "(var-get test-run)",
                );

                assert!(alice_test_result.expect_bool());
                assert!(bob_test_result.expect_bool());
                assert!(charlie_test_result.expect_bool());

                let alice_test_result = eval_contract_at_tip(
                    &mut peer,
                    &key_to_stacks_addr(&alice),
                    "alice-test",
                    "(var-get test-result)",
                );
                let bob_test_result = eval_contract_at_tip(
                    &mut peer,
                    &key_to_stacks_addr(&bob),
                    "bob-test",
                    "(var-get test-result)",
                );
                let charlie_test_result = eval_contract_at_tip(
                    &mut peer,
                    &key_to_stacks_addr(&charlie),
                    "charlie-test",
                    "(var-get test-result)",
                );

                eprintln!(
                    "\nalice: {:?}, bob: {:?}, charlie: {:?}\n",
                    &alice_test_result, &bob_test_result, &charlie_test_result
                );

                assert_eq!(bob_test_result, Value::Int(-1));
                assert_eq!(alice_test_result, Value::Int(3));
                assert_eq!(charlie_test_result, Value::Int(1));
            }
        }
    }

    #[test]
    fn test_pox_lockup_single_tx_sender_unlock() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-single-tx-sender-unlock", 6012);

        let num_blocks = 2;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();

        let mut alice_reward_cycle = 0;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let mut block_txs = vec![coinbase_tx];

                    if tenure_id == 1 {
                        // Alice locks up exactly 25% of the liquid STX supply, so this should succeed.
                        let alice_lockup = make_pox_lockup(
                            &alice,
                            0,
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&alice).bytes,
                            1,
                            tip.block_height,
                        );
                        block_txs.push(alice_lockup);
                    }

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // Alice has not locked up STX
                    let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
                }

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                alice_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                eprintln!(
                    "\nalice reward cycle: {}\ncur reward cycle: {}\n",
                    alice_reward_cycle, cur_reward_cycle
                );
            } else {
                // Alice's address is locked as of the next reward cycle
                let tip_burn_block_height =
                    get_par_burn_block_height(peer.chainstate(), &tip_index_block);
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                let total_stacked = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.test_get_total_ustx_stacked(
                        sortdb,
                        &tip_index_block,
                        cur_reward_cycle,
                    )
                })
                .unwrap();

                eprintln!("\ntenure: {}\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\ntotal-stacked: {}\n", tenure_id, cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx, total_stacked);

                if cur_reward_cycle >= alice_reward_cycle {
                    // this will grow as more miner rewards are unlocked, so be wary
                    if tenure_id >= (MINER_REWARD_MATURITY + 1) as usize {
                        // miner rewards increased liquid supply, so less than 25% is locked.
                        // minimum participation decreases.
                        assert!(total_liquid_ustx > 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                        assert_eq!(min_ustx, total_liquid_ustx / 480);
                    }

                    if cur_reward_cycle == alice_reward_cycle {
                        let (amount_ustx, pox_addr, lock_period, first_reward_cycle) =
                            get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into())
                                .unwrap();
                        eprintln!("\nAlice: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, first_reward_cycle);

                        assert_eq!(first_reward_cycle, alice_reward_cycle);
                        assert_eq!(lock_period, 1);

                        // one reward address, and it's Alice's
                        // either way, there's a single reward address
                        assert_eq!(reward_addrs.len(), 1);
                        assert_eq!(
                            (reward_addrs[0].0).version,
                            AddressHashMode::SerializeP2PKH.to_version_testnet()
                        );
                        assert_eq!((reward_addrs[0].0).bytes, key_to_stacks_addr(&alice).bytes);
                        assert_eq!(reward_addrs[0].1, 1024 * POX_THRESHOLD_STEPS_USTX);

                        // All of Alice's tokens are locked
                        assert_eq!(alice_balance, 0);

                        // Lock-up is consistent with stacker state
                        let alice_account =
                            get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                        assert_eq!(alice_account.stx_balance.amount_unlocked(), 0);
                        assert_eq!(
                            alice_account.stx_balance.amount_locked(),
                            1024 * POX_THRESHOLD_STEPS_USTX
                        );
                        assert_eq!(
                            alice_account.stx_balance.unlock_height() as u128,
                            (first_reward_cycle + lock_period)
                                * (burnchain.pox_constants.reward_cycle_length as u128)
                                + (burnchain.first_block_height as u128)
                        );
                    } else {
                        // unlock should have happened
                        assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                        // alice shouldn't be a stacker
                        let info = get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into());
                        assert!(
                            get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into())
                                .is_none()
                        );

                        // empty reward cycle
                        assert_eq!(reward_addrs.len(), 0);

                        // min STX is reset
                        assert_eq!(min_ustx, total_liquid_ustx / 480);

                        // Unlock is lazy
                        let alice_account =
                            get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                        assert_eq!(alice_account.stx_balance.amount_unlocked(), 0);
                        assert_eq!(
                            alice_account.stx_balance.amount_locked(),
                            1024 * POX_THRESHOLD_STEPS_USTX
                        );
                        assert_eq!(
                            alice_account.stx_balance.unlock_height() as u128,
                            (alice_reward_cycle + 1)
                                * (burnchain.pox_constants.reward_cycle_length as u128)
                                + (burnchain.first_block_height as u128)
                        );
                    }
                } else {
                    // no reward addresses
                    assert_eq!(reward_addrs.len(), 0);
                }
            }
        }
    }

    #[test]
    fn test_pox_lockup_unlock_relock() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-unlock-relock", 6014);

        let num_blocks = 25;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();
        let danielle = keys.pop().unwrap();

        let mut first_reward_cycle = 0;
        let mut second_reward_cycle = 0;

        let mut test_before_first_reward_cycle = false;
        let mut test_in_first_reward_cycle = false;
        let mut test_between_reward_cycles = false;
        let mut test_in_second_reward_cycle = false;
        let mut test_after_second_reward_cycle = false;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let mut block_txs = vec![coinbase_tx];

                    if tenure_id == 1 {
                        // Alice locks up exactly 25% of the liquid STX supply, so this should succeed.
                        let alice_lockup = make_pox_lockup(
                            &alice,
                            0,
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&alice).bytes,
                            1,
                            tip.block_height,
                        );
                        block_txs.push(alice_lockup);

                        // Bob creates a locking contract
                        let bob_contract = make_pox_lockup_contract(&bob, 0, "do-lockup");
                        block_txs.push(bob_contract);

                        let charlie_stack = make_pox_lockup_contract_call(
                            &charlie,
                            0,
                            &key_to_stacks_addr(&bob),
                            "do-lockup",
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&charlie).bytes,
                            1,
                        );
                        block_txs.push(charlie_stack);
                    } else if tenure_id == 10 {
                        let charlie_withdraw = make_pox_withdraw_stx_contract_call(
                            &charlie,
                            1,
                            &key_to_stacks_addr(&bob),
                            "do-lockup",
                            1024 * POX_THRESHOLD_STEPS_USTX,
                        );
                        block_txs.push(charlie_withdraw);
                    } else if tenure_id == 11 {
                        // Alice locks up half of her tokens
                        let alice_lockup = make_pox_lockup(
                            &alice,
                            1,
                            512 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&alice).bytes,
                            1,
                            tip.block_height,
                        );
                        block_txs.push(alice_lockup);

                        // Charlie locks up half of his tokens
                        let charlie_stack = make_pox_lockup_contract_call(
                            &charlie,
                            2,
                            &key_to_stacks_addr(&bob),
                            "do-lockup",
                            512 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&charlie).bytes,
                            1,
                        );
                        block_txs.push(charlie_stack);
                    }

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );
            let tip_burn_block_height =
                get_par_burn_block_height(peer.chainstate(), &tip_index_block);
            let cur_reward_cycle = burnchain
                .block_height_to_reward_cycle(tip_burn_block_height)
                .unwrap() as u128;

            let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());
            let charlie_contract_balance = get_balance(
                &mut peer,
                &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
            );
            let charlie_balance = get_balance(&mut peer, &key_to_stacks_addr(&charlie).into());

            let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                get_reward_addresses_with_par_tip(chainstate, &burnchain, sortdb, &tip_index_block)
            })
            .unwrap();
            let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                chainstate.get_stacking_minimum(sortdb, &tip_index_block)
            })
            .unwrap();
            let total_stacked = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                chainstate.test_get_total_ustx_stacked(sortdb, &tip_index_block, cur_reward_cycle)
            })
            .unwrap();

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // Alice has not locked up STX
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                    // Charlie's contract has not locked up STX
                    assert_eq!(charlie_contract_balance, 0);
                }

                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                first_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                eprintln!(
                    "\nfirst reward cycle: {}\ncur reward cycle: {}\n",
                    first_reward_cycle, cur_reward_cycle
                );

                assert!(first_reward_cycle > cur_reward_cycle);
                test_before_first_reward_cycle = true;
            } else if tenure_id == 10 {
                // Alice has unlocked
                assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                // Charlie's contract was unlocked and wiped
                assert_eq!(charlie_contract_balance, 0);

                // Charlie's balance
                assert_eq!(charlie_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id == 11 {
                // should have just re-locked
                // stacking minimum should be minimum, since we haven't
                // locked up 25% of the tokens yet
                let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    chainstate.get_stacking_minimum(sortdb, &tip_index_block)
                })
                .unwrap();
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                second_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                assert!(second_reward_cycle > cur_reward_cycle);
                eprintln!(
                    "\nsecond reward cycle: {}\ncur reward cycle: {}\n",
                    second_reward_cycle, cur_reward_cycle
                );
            }

            eprintln!("\ntenure: {}\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\ntotal-stacked: {}\n", tenure_id, cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx, total_stacked);

            // this will grow as more miner rewards are unlocked, so be wary
            if tenure_id >= (MINER_REWARD_MATURITY + 1) as usize {
                // miner rewards increased liquid supply, so less than 25% is locked.
                // minimum participation decreases.
                assert!(total_liquid_ustx > 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                assert_eq!(min_ustx, total_liquid_ustx / 480);
            } else if tenure_id >= 1 && cur_reward_cycle < first_reward_cycle {
                // still at 25% or more locked
                assert!(total_liquid_ustx <= 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
            } else if tenure_id < 1 {
                // nothing locked yet
                assert_eq!(min_ustx, total_liquid_ustx / 480);
            }

            if first_reward_cycle > 0 && second_reward_cycle == 0 {
                if cur_reward_cycle == first_reward_cycle {
                    test_in_first_reward_cycle = true;

                    // in Alice's first reward cycle
                    let (amount_ustx, pox_addr, lock_period, first_pox_reward_cycle) =
                        get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into()).unwrap();
                    eprintln!("\nAlice: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, first_reward_cycle);

                    assert_eq!(first_reward_cycle, first_reward_cycle);
                    assert_eq!(lock_period, 1);

                    // in Charlie's first reward cycle
                    let (amount_ustx, pox_addr, lock_period, first_pox_reward_cycle) =
                        get_stacker_info(
                            &mut peer,
                            &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                        )
                        .unwrap();
                    eprintln!("\nCharlie: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, first_reward_cycle);

                    assert_eq!(first_reward_cycle, first_pox_reward_cycle);
                    assert_eq!(lock_period, 1);

                    // two reward address, and it's Alice's and Charlie's in sorted order
                    assert_eq!(reward_addrs.len(), 2);
                    assert_eq!(
                        (reward_addrs[1].0).version,
                        AddressHashMode::SerializeP2PKH.to_version_testnet()
                    );
                    assert_eq!((reward_addrs[1].0).bytes, key_to_stacks_addr(&alice).bytes);
                    assert_eq!(reward_addrs[1].1, 1024 * POX_THRESHOLD_STEPS_USTX);

                    assert_eq!(
                        (reward_addrs[0].0).version,
                        AddressHashMode::SerializeP2PKH.to_version_testnet()
                    );
                    assert_eq!(
                        (reward_addrs[0].0).bytes,
                        key_to_stacks_addr(&charlie).bytes
                    );
                    assert_eq!(reward_addrs[0].1, 1024 * POX_THRESHOLD_STEPS_USTX);

                    // All of Alice's and Charlie's tokens are locked
                    assert_eq!(alice_balance, 0);
                    assert_eq!(charlie_contract_balance, 0);

                    // Lock-up is consistent with stacker state
                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(
                        alice_account.stx_balance.amount_locked(),
                        1024 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.unlock_height() as u128,
                        (first_reward_cycle + lock_period)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );

                    // Lock-up is consistent with stacker state
                    let charlie_account = get_account(
                        &mut peer,
                        &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                    );
                    assert_eq!(charlie_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(
                        charlie_account.stx_balance.amount_locked(),
                        1024 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        charlie_account.stx_balance.unlock_height() as u128,
                        (first_reward_cycle + lock_period)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );
                } else if cur_reward_cycle > first_reward_cycle {
                    test_between_reward_cycles = true;

                    // After Alice's first reward cycle, but before her second.
                    // unlock should have happened
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
                    assert_eq!(charlie_contract_balance, 0);

                    // alice shouldn't be a stacker
                    assert!(
                        get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into()).is_none()
                    );
                    assert!(get_stacker_info(
                        &mut peer,
                        &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into()
                    )
                    .is_none());

                    // empty reward cycle
                    assert_eq!(reward_addrs.len(), 0);

                    // min STX is reset
                    assert_eq!(min_ustx, total_liquid_ustx / 480);

                    // Unlock is lazy
                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(
                        alice_account.stx_balance.amount_locked(),
                        1024 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.unlock_height() as u128,
                        (first_reward_cycle + 1)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );

                    // Unlock is lazy
                    let charlie_account = get_account(
                        &mut peer,
                        &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                    );
                    assert_eq!(charlie_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(charlie_account.stx_balance.amount_locked(), 0);
                    assert_eq!(charlie_account.stx_balance.unlock_height() as u128, 0);
                }
            } else if second_reward_cycle > 0 {
                if cur_reward_cycle == second_reward_cycle {
                    test_in_second_reward_cycle = true;

                    // in Alice's second reward cycle
                    let (amount_ustx, pox_addr, lock_period, first_pox_reward_cycle) =
                        get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into()).unwrap();
                    eprintln!("\nAlice: {} uSTX stacked for {} cycle(s); addr is {:?}; second reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, second_reward_cycle);

                    assert_eq!(first_pox_reward_cycle, second_reward_cycle);
                    assert_eq!(lock_period, 1);

                    // in Charlie's second reward cycle
                    let (amount_ustx, pox_addr, lock_period, first_pox_reward_cycle) =
                        get_stacker_info(
                            &mut peer,
                            &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                        )
                        .unwrap();
                    eprintln!("\nCharlie: {} uSTX stacked for {} cycle(s); addr is {:?}; second reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, second_reward_cycle);

                    assert_eq!(first_pox_reward_cycle, second_reward_cycle);
                    assert_eq!(lock_period, 1);

                    // one reward address, and it's Alice's
                    // either way, there's a single reward address
                    assert_eq!(reward_addrs.len(), 2);
                    assert_eq!(
                        (reward_addrs[1].0).version,
                        AddressHashMode::SerializeP2PKH.to_version_testnet()
                    );
                    assert_eq!((reward_addrs[1].0).bytes, key_to_stacks_addr(&alice).bytes);
                    assert_eq!(reward_addrs[1].1, 512 * POX_THRESHOLD_STEPS_USTX);

                    assert_eq!(
                        (reward_addrs[0].0).version,
                        AddressHashMode::SerializeP2PKH.to_version_testnet()
                    );
                    assert_eq!(
                        (reward_addrs[0].0).bytes,
                        key_to_stacks_addr(&charlie).bytes
                    );
                    assert_eq!(reward_addrs[0].1, 512 * POX_THRESHOLD_STEPS_USTX);

                    // Half of Alice's tokens are locked
                    assert_eq!(alice_balance, 512 * POX_THRESHOLD_STEPS_USTX);
                    assert_eq!(charlie_contract_balance, 0);
                    assert_eq!(charlie_balance, 512 * POX_THRESHOLD_STEPS_USTX);

                    // Lock-up is consistent with stacker state
                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(
                        alice_account.stx_balance.amount_unlocked(),
                        512 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.amount_locked(),
                        512 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.unlock_height() as u128,
                        (second_reward_cycle + lock_period)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );

                    // Lock-up is consistent with stacker state
                    let charlie_account = get_account(
                        &mut peer,
                        &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                    );
                    assert_eq!(charlie_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(
                        charlie_account.stx_balance.amount_locked(),
                        512 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        charlie_account.stx_balance.unlock_height() as u128,
                        (second_reward_cycle + lock_period)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );
                } else if cur_reward_cycle > second_reward_cycle {
                    test_after_second_reward_cycle = true;

                    // After Alice's second reward cycle
                    // unlock should have happened
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);
                    assert_eq!(charlie_contract_balance, 512 * POX_THRESHOLD_STEPS_USTX);
                    assert_eq!(charlie_balance, 512 * POX_THRESHOLD_STEPS_USTX);

                    // alice and charlie shouldn't be stackers
                    assert!(
                        get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into()).is_none()
                    );
                    assert!(get_stacker_info(
                        &mut peer,
                        &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into()
                    )
                    .is_none());

                    // empty reward cycle
                    assert_eq!(reward_addrs.len(), 0);

                    // min STX is reset
                    assert_eq!(min_ustx, total_liquid_ustx / 480);

                    // Unlock is lazy
                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(
                        alice_account.stx_balance.amount_unlocked(),
                        512 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.amount_locked(),
                        512 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.unlock_height() as u128,
                        (second_reward_cycle + 1)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );

                    // Unlock is lazy
                    let charlie_account = get_account(
                        &mut peer,
                        &make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
                    );
                    assert_eq!(charlie_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(
                        charlie_account.stx_balance.amount_locked(),
                        512 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        charlie_account.stx_balance.unlock_height() as u128,
                        (second_reward_cycle + 1)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );
                }
            }
        }

        assert!(test_before_first_reward_cycle);
        assert!(test_in_first_reward_cycle);
        assert!(test_between_reward_cycles);
        assert!(test_in_second_reward_cycle);
        assert!(test_after_second_reward_cycle);
    }

    #[test]
    fn test_pox_lockup_unlock_on_spend() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;

        let (mut peer, mut keys) =
            instantiate_pox_peer(&burnchain, "test-pox-lockup-unlock-on-spend", 6016);

        let num_blocks = 20;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();
        let danielle = keys.pop().unwrap();

        let mut reward_cycle = 0;

        let mut test_before_first_reward_cycle = false;
        let mut test_in_first_reward_cycle = false;
        let mut test_between_reward_cycles = false;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(
                |ref mut miner,
                 ref mut sortdb,
                 ref mut chainstate,
                 vrf_proof,
                 ref parent_opt,
                 ref parent_microblock_header_opt| {
                    let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                    let coinbase_tx = make_coinbase(miner, tenure_id);

                    let mut block_txs = vec![coinbase_tx];

                    if tenure_id == 1 {
                        // everyone locks up all of their tokens
                        let alice_lockup = make_pox_lockup(
                            &alice,
                            0,
                            512 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&alice).bytes,
                            1,
                            tip.block_height,
                        );
                        block_txs.push(alice_lockup);

                        let bob_lockup = make_pox_lockup(
                            &bob,
                            0,
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&bob).bytes,
                            1,
                            tip.block_height,
                        );
                        block_txs.push(bob_lockup);

                        let charlie_lockup = make_pox_lockup(
                            &charlie,
                            0,
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&charlie).bytes,
                            1,
                            tip.block_height,
                        );
                        block_txs.push(charlie_lockup);

                        let danielle_lockup = make_pox_lockup(
                            &danielle,
                            0,
                            1024 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2PKH,
                            key_to_stacks_addr(&danielle).bytes,
                            1,
                            tip.block_height,
                        );
                        block_txs.push(danielle_lockup);

                        let bob_contract = make_pox_lockup_contract(&bob, 1, "do-lockup");
                        block_txs.push(bob_contract);

                        let alice_stack = make_pox_lockup_contract_call(
                            &alice,
                            1,
                            &key_to_stacks_addr(&bob),
                            "do-lockup",
                            512 * POX_THRESHOLD_STEPS_USTX,
                            AddressHashMode::SerializeP2SH,
                            key_to_stacks_addr(&alice).bytes,
                            1,
                        );
                        block_txs.push(alice_stack);
                    } else if tenure_id >= 2 && tenure_id <= 8 {
                        // try to spend tokens -- they should all fail with short-return
                        let alice_spend = make_bare_contract(
                            &alice,
                            2,
                            0,
                            "alice-try-spend",
                            &format!(
                                "(begin (unwrap! (stx-transfer? u1 tx-sender '{}) (err 1)))",
                                &key_to_stacks_addr(&danielle)
                            ),
                        );
                        block_txs.push(alice_spend);
                    } else if tenure_id == 11 {
                        // Alice sends a transaction with a non-zero fee
                        let alice_tx = make_bare_contract(
                            &alice,
                            3,
                            1,
                            "alice-test",
                            "(begin (print \"hello alice\"))",
                        );
                        block_txs.push(alice_tx);

                        // Bob sends a STX-transfer transaction
                        let bob_tx =
                            make_token_transfer(&bob, 2, 0, key_to_stacks_addr(&alice).into(), 1);
                        block_txs.push(bob_tx);

                        // Charlie runs a contract that transfers his STX tokens
                        let charlie_tx = make_bare_contract(
                            &charlie,
                            1,
                            0,
                            "charlie-test",
                            &format!(
                                "(begin (unwrap-panic (stx-transfer? u1 tx-sender '{})))",
                                &key_to_stacks_addr(&alice)
                            ),
                        );
                        block_txs.push(charlie_tx);

                        // Danielle burns some STX
                        let danielle_tx = make_bare_contract(
                            &danielle,
                            1,
                            0,
                            "danielle-test",
                            "(begin (stx-burn? u1 tx-sender))",
                        );
                        block_txs.push(danielle_tx);

                        // Alice gets some of her STX back
                        let alice_withdraw_tx = make_pox_withdraw_stx_contract_call(
                            &alice,
                            4,
                            &key_to_stacks_addr(&bob),
                            "do-lockup",
                            1,
                        );
                        block_txs.push(alice_withdraw_tx);
                    }

                    let block_builder = StacksBlockBuilder::make_regtest_block_builder(
                        &parent_tip,
                        vrf_proof,
                        tip.total_burn,
                        microblock_pubkeyhash,
                    )
                    .unwrap();
                    let (anchored_block, _size, _cost) =
                        StacksBlockBuilder::make_anchored_block_from_txs(
                            block_builder,
                            chainstate,
                            &sortdb.index_conn(),
                            block_txs,
                        )
                        .unwrap();
                    (anchored_block, vec![])
                },
            );

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );
            let tip_burn_block_height =
                get_par_burn_block_height(peer.chainstate(), &tip_index_block);

            let cur_reward_cycle = burnchain
                .block_height_to_reward_cycle(tip_burn_block_height)
                .unwrap() as u128;

            let stacker_addrs: Vec<PrincipalData> = vec![
                key_to_stacks_addr(&alice).into(),
                key_to_stacks_addr(&bob).into(),
                key_to_stacks_addr(&charlie).into(),
                key_to_stacks_addr(&danielle).into(),
                make_contract_id(&key_to_stacks_addr(&bob), "do-lockup").into(),
            ];

            let expected_pox_addrs: Vec<(u8, Hash160)> = vec![
                (
                    AddressHashMode::SerializeP2PKH.to_version_testnet(),
                    key_to_stacks_addr(&alice).bytes,
                ),
                (
                    AddressHashMode::SerializeP2PKH.to_version_testnet(),
                    key_to_stacks_addr(&bob).bytes,
                ),
                (
                    AddressHashMode::SerializeP2PKH.to_version_testnet(),
                    key_to_stacks_addr(&charlie).bytes,
                ),
                (
                    AddressHashMode::SerializeP2PKH.to_version_testnet(),
                    key_to_stacks_addr(&danielle).bytes,
                ),
                (
                    AddressHashMode::SerializeP2SH.to_version_testnet(),
                    key_to_stacks_addr(&alice).bytes,
                ),
            ];

            let balances: Vec<u128> = stacker_addrs
                .iter()
                .map(|principal| get_balance(&mut peer, principal))
                .collect();

            let balances_before_stacking: Vec<u128> = vec![
                1024 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                0,
            ];

            let balances_during_stacking: Vec<u128> = vec![0, 0, 0, 0, 0];

            let balances_stacked: Vec<u128> = vec![
                512 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                512 * POX_THRESHOLD_STEPS_USTX,
            ];

            let balances_after_stacking: Vec<u128> = vec![
                512 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                1024 * POX_THRESHOLD_STEPS_USTX,
                512 * POX_THRESHOLD_STEPS_USTX,
            ];

            let balances_after_spending: Vec<u128> = vec![
                512 * POX_THRESHOLD_STEPS_USTX + 2,
                1024 * POX_THRESHOLD_STEPS_USTX - 1,
                1024 * POX_THRESHOLD_STEPS_USTX - 1,
                1024 * POX_THRESHOLD_STEPS_USTX - 1,
                512 * POX_THRESHOLD_STEPS_USTX - 1,
            ];

            let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                chainstate.get_stacking_minimum(sortdb, &tip_index_block)
            })
            .unwrap();
            let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                get_reward_addresses_with_par_tip(chainstate, &burnchain, sortdb, &tip_index_block)
            })
            .unwrap();
            let total_stacked = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                chainstate.test_get_total_ustx_stacked(sortdb, &tip_index_block, cur_reward_cycle)
            })
            .unwrap();

            eprintln!("\ntenure: {}\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\ntotal-stacked: {}\n", tenure_id, cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx, total_stacked);

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // no one has locked
                    for (balance, expected_balance) in
                        balances.iter().zip(balances_before_stacking.iter())
                    {
                        assert_eq!(balance, expected_balance);
                    }
                }
                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                    get_reward_addresses_with_par_tip(
                        chainstate,
                        &burnchain,
                        sortdb,
                        &tip_index_block,
                    )
                })
                .unwrap();
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                eprintln!(
                    "first reward cycle: {}\ncur reward cycle: {}\n",
                    reward_cycle, cur_reward_cycle
                );

                assert!(reward_cycle > cur_reward_cycle);
                test_before_first_reward_cycle = true;
            } else if tenure_id >= 2 && tenure_id <= 8 {
                // alice did _NOT_ spend
                assert!(get_contract(
                    &mut peer,
                    &make_contract_id(&key_to_stacks_addr(&alice), "alice-try-spend").into()
                )
                .is_none());
            }

            if reward_cycle > 0 {
                if cur_reward_cycle == reward_cycle {
                    test_in_first_reward_cycle = true;

                    // in reward cycle
                    assert_eq!(reward_addrs.len(), expected_pox_addrs.len());

                    // in sorted order
                    let mut sorted_expected_pox_info: Vec<_> = expected_pox_addrs
                        .iter()
                        .zip(balances_stacked.iter())
                        .collect();
                    sorted_expected_pox_info.sort_by_key(|(pox_addr, _)| (pox_addr.1).0);

                    // in stacker order
                    for (i, (pox_addr, expected_stacked)) in
                        sorted_expected_pox_info.iter().enumerate()
                    {
                        assert_eq!((reward_addrs[i].0).version, pox_addr.0);
                        assert_eq!((reward_addrs[i].0).bytes, pox_addr.1);
                        assert_eq!(reward_addrs[i].1, **expected_stacked);
                    }

                    // all stackers are present
                    for addr in stacker_addrs.iter() {
                        let (amount_ustx, pox_addr, lock_period, pox_reward_cycle) =
                            get_stacker_info(&mut peer, addr).unwrap();
                        eprintln!("\naddr {}: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", addr, amount_ustx, lock_period, &pox_addr, reward_cycle);

                        assert_eq!(pox_reward_cycle, reward_cycle);
                        assert_eq!(lock_period, 1);
                    }

                    // all tokens locked
                    for (balance, expected_balance) in
                        balances.iter().zip(balances_during_stacking.iter())
                    {
                        assert_eq!(balance, expected_balance);
                    }

                    // Lock-up is consistent with stacker state
                    for (addr, expected_balance) in
                        stacker_addrs.iter().zip(balances_stacked.iter())
                    {
                        let account = get_account(&mut peer, addr);
                        assert_eq!(account.stx_balance.amount_unlocked(), 0);
                        assert_eq!(account.stx_balance.amount_locked(), *expected_balance);
                        assert_eq!(
                            account.stx_balance.unlock_height() as u128,
                            (reward_cycle + 1)
                                * (burnchain.pox_constants.reward_cycle_length as u128)
                                + (burnchain.first_block_height as u128)
                        );
                    }
                } else if cur_reward_cycle > reward_cycle {
                    test_between_reward_cycles = true;

                    if tenure_id < 11 {
                        // all balances should have been restored
                        for (balance, expected_balance) in
                            balances.iter().zip(balances_after_stacking.iter())
                        {
                            assert_eq!(balance, expected_balance);
                        }
                    } else {
                        // some balances reduced, but none are zero
                        for (balance, expected_balance) in
                            balances.iter().zip(balances_after_spending.iter())
                        {
                            assert_eq!(balance, expected_balance);
                        }
                    }

                    // no one's a stacker
                    for addr in stacker_addrs.iter() {
                        assert!(get_stacker_info(&mut peer, addr).is_none());
                    }

                    // empty reward cycle
                    assert_eq!(reward_addrs.len(), 0);

                    // min STX is reset
                    assert_eq!(min_ustx, total_liquid_ustx / 480);
                }
            }

            if tenure_id >= 11 {
                // all balances are restored
                for (addr, expected_balance) in
                    stacker_addrs.iter().zip(balances_after_spending.iter())
                {
                    let account = get_account(&mut peer, addr);
                    assert_eq!(account.stx_balance.amount_unlocked(), *expected_balance);
                    assert_eq!(account.stx_balance.amount_locked(), 0);
                    assert_eq!(account.stx_balance.unlock_height(), 0);
                }
            } else if cur_reward_cycle >= reward_cycle {
                // not unlocked, but unlock is lazy
                for (addr, (expected_locked, expected_balance)) in stacker_addrs
                    .iter()
                    .zip(balances_stacked.iter().zip(balances_during_stacking.iter()))
                {
                    let account = get_account(&mut peer, addr);
                    assert_eq!(account.stx_balance.amount_unlocked(), *expected_balance);
                    assert_eq!(account.stx_balance.amount_locked(), *expected_locked);
                    assert_eq!(
                        account.stx_balance.unlock_height() as u128,
                        (reward_cycle + 1) * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );
                }
            }
        }

        assert!(test_before_first_reward_cycle);
        assert!(test_in_first_reward_cycle);
        assert!(test_between_reward_cycles);
    }

    #[test]
    fn test_pox_lockup_reject() {
        let mut burnchain = Burnchain::default_unittest(0, &BurnchainHeaderHash::zero());
        burnchain.pox_constants.reward_cycle_length = 5;
        burnchain.pox_constants.prepare_length = 2;
        burnchain.pox_constants.anchor_threshold = 1;
        // used to be set to 25, but test at 5 here, because the increased coinbase
        //   and, to a lesser extent, the initial block bonus altered the relative fraction
        //   owned by charlie.
        burnchain.pox_constants.pox_rejection_fraction = 5;

        let (mut peer, mut keys) = instantiate_pox_peer(&burnchain, "test-pox-lockup-reject", 6024);

        let num_blocks = 15;

        let alice = keys.pop().unwrap();
        let bob = keys.pop().unwrap();
        let charlie = keys.pop().unwrap();

        let mut alice_reward_cycle = 0;

        for tenure_id in 0..num_blocks {
            let microblock_privkey = StacksPrivateKey::new();
            let microblock_pubkeyhash =
                Hash160::from_node_public_key(&StacksPublicKey::from_private(&microblock_privkey));
            let tip =
                SortitionDB::get_canonical_burn_chain_tip(&peer.sortdb.as_ref().unwrap().conn())
                    .unwrap();

            let (burn_ops, stacks_block, microblocks) = peer.make_tenure(|ref mut miner, ref mut sortdb, ref mut chainstate, vrf_proof, ref parent_opt, ref parent_microblock_header_opt| {
                let parent_tip = get_parent_tip(parent_opt, chainstate, sortdb);
                let coinbase_tx = make_coinbase(miner, tenure_id);

                let mut block_txs = vec![
                    coinbase_tx
                ];

                if tenure_id == 1 {
                    // Alice locks up exactly 25% of the liquid STX supply, so this should succeed.
                    let alice_lockup = make_pox_lockup(&alice, 0, 1024 * POX_THRESHOLD_STEPS_USTX, AddressHashMode::SerializeP2PKH, key_to_stacks_addr(&alice).bytes, 12, tip.block_height);
                    block_txs.push(alice_lockup);

                    // Bob rejects with exactly 25% of the liquid STX supply (shouldn't affect
                    // anything).
                    let bob_reject = make_pox_reject(&bob, 0);
                    block_txs.push(bob_reject);
                } else if tenure_id == 2 {
                    // Charlie rejects
                    // this _should_ be included in the block
                    let charlie_reject = make_pox_reject(&charlie, 0);
                    block_txs.push(charlie_reject);

                    // allowance for the contract-caller
                    // this _should_ be included in the block
                    let charlie_contract: Value = contract_id(&key_to_stacks_addr(&charlie), "charlie-try-stack").into();
                    let charlie_allowance = make_pox_contract_call(&charlie, 1, "allow-contract-caller",
                                                                   vec![charlie_contract, Value::none()]);
                    block_txs.push(charlie_allowance);

                    // Charlie tries to stack, but it should fail.
                    // Specifically, (stack-stx) should fail with (err 17).
                    let charlie_stack = make_bare_contract(&charlie, 2, 0, "charlie-try-stack",
                        &format!(
                            "(define-data-var test-passed bool false)
                             (var-set test-passed (is-eq
                               (err 17)
                               (print (contract-call? '{}.pox stack-stx u10240000000000 {{ version: 0x01, hashbytes: 0x1111111111111111111111111111111111111111 }} burn-block-height u1))))",
                               boot_code_test_addr()));

                    block_txs.push(charlie_stack);

                    // Alice tries to reject, but it should fail.
                    // Specifically, (reject-pox) should fail with (err 3) since Alice already
                    // stacked.
                    // If it's the case, then this tx will NOT be mined
                    let alice_reject = make_bare_contract(&alice, 1, 0, "alice-try-reject",
                        &format!(
                            "(define-data-var test-passed bool false)
                             (var-set test-passed (is-eq
                               (err 3)
                               (print (contract-call? '{}.pox reject-pox))))",
                               boot_code_test_addr()));

                    block_txs.push(alice_reject);

                    // Charlie tries to reject again, but it should fail.
                    // Specifically, (reject-pox) should fail with (err 17).
                    let charlie_reject = make_bare_contract(&charlie, 3, 0, "charlie-try-reject",
                        &format!(
                            "(define-data-var test-passed bool false)
                             (var-set test-passed (is-eq
                               (err 17)
                               (print (contract-call? '{}.pox reject-pox))))",
                               boot_code_test_addr()));

                    block_txs.push(charlie_reject);
                }

                let block_builder = StacksBlockBuilder::make_regtest_block_builder(&parent_tip, vrf_proof, tip.total_burn, microblock_pubkeyhash).unwrap();
                let (anchored_block, _size, _cost) = StacksBlockBuilder::make_anchored_block_from_txs(block_builder, chainstate, &sortdb.index_conn(), block_txs).unwrap();

                if tenure_id == 2 {
                    // block should be all the transactions
                    assert_eq!(anchored_block.txs.len(), 6);
                }

                (anchored_block, vec![])
            });

            let (_, _, consensus_hash) = peer.next_burnchain_block(burn_ops.clone());
            peer.process_stacks_epoch_at_tip(&stacks_block, &microblocks);

            let total_liquid_ustx = get_liquid_ustx(&mut peer);
            let tip_index_block = StacksBlockHeader::make_index_block_hash(
                &consensus_hash,
                &stacks_block.block_hash(),
            );
            let tip_burn_block_height =
                get_par_burn_block_height(peer.chainstate(), &tip_index_block);

            let cur_reward_cycle = burnchain
                .block_height_to_reward_cycle(tip_burn_block_height)
                .unwrap() as u128;
            let alice_balance = get_balance(&mut peer, &key_to_stacks_addr(&alice).into());

            let min_ustx = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                chainstate.get_stacking_minimum(sortdb, &tip_index_block)
            })
            .unwrap();
            let reward_addrs = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                get_reward_addresses_with_par_tip(chainstate, &burnchain, sortdb, &tip_index_block)
            })
            .unwrap();
            let total_stacked = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                chainstate.test_get_total_ustx_stacked(sortdb, &tip_index_block, cur_reward_cycle)
            })
            .unwrap();
            let total_stacked_next = with_sortdb(&mut peer, |ref mut chainstate, ref sortdb| {
                chainstate.test_get_total_ustx_stacked(
                    sortdb,
                    &tip_index_block,
                    cur_reward_cycle + 1,
                )
            })
            .unwrap();

            eprintln!("\ntenure: {}\nreward cycle: {}\nmin-uSTX: {}\naddrs: {:?}\ntotal_liquid_ustx: {}\ntotal-stacked: {}\ntotal-stacked next: {}\n", 
                      tenure_id, cur_reward_cycle, min_ustx, &reward_addrs, total_liquid_ustx, total_stacked, total_stacked_next);

            if tenure_id <= 1 {
                if tenure_id < 1 {
                    // Alice has not locked up STX
                    assert_eq!(alice_balance, 1024 * POX_THRESHOLD_STEPS_USTX);

                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(
                        alice_account.stx_balance.amount_unlocked(),
                        1024 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(alice_account.stx_balance.amount_locked(), 0);
                    assert_eq!(alice_account.stx_balance.unlock_height(), 0);
                }

                assert_eq!(min_ustx, total_liquid_ustx / 480);

                // no reward addresses
                assert_eq!(reward_addrs.len(), 0);

                // record the first reward cycle when Alice's tokens get stacked
                alice_reward_cycle = 1 + burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;
                let cur_reward_cycle = burnchain
                    .block_height_to_reward_cycle(tip_burn_block_height)
                    .unwrap() as u128;

                eprintln!(
                    "\nalice reward cycle: {}\ncur reward cycle: {}\n",
                    alice_reward_cycle, cur_reward_cycle
                );
            } else {
                if tenure_id == 2 {
                    // charlie's contract did NOT materialize
                    let result = eval_contract_at_tip(
                        &mut peer,
                        &key_to_stacks_addr(&charlie),
                        "charlie-try-stack",
                        "(var-get test-passed)",
                    )
                    .expect_bool();
                    assert!(result, "charlie-try-stack test should be `true`");
                    let result = eval_contract_at_tip(
                        &mut peer,
                        &key_to_stacks_addr(&charlie),
                        "charlie-try-reject",
                        "(var-get test-passed)",
                    )
                    .expect_bool();
                    assert!(result, "charlie-try-reject test should be `true`");
                    let result = eval_contract_at_tip(
                        &mut peer,
                        &key_to_stacks_addr(&alice),
                        "alice-try-reject",
                        "(var-get test-passed)",
                    )
                    .expect_bool();
                    assert!(result, "alice-try-reject test should be `true`");
                }

                // Alice's address is locked as of the next reward cycle
                // Alice has locked up STX no matter what
                assert_eq!(alice_balance, 0);

                if cur_reward_cycle >= alice_reward_cycle {
                    // this will grow as more miner rewards are unlocked, so be wary
                    if tenure_id >= (MINER_REWARD_MATURITY + 1) as usize {
                        // miner rewards increased liquid supply, so less than 25% is locked.
                        // minimum participation decreases.
                        assert!(total_liquid_ustx > 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                        assert_eq!(min_ustx, total_liquid_ustx / 480);
                    } else {
                        // still at 25% or more locked
                        assert!(total_liquid_ustx <= 4 * 1024 * POX_THRESHOLD_STEPS_USTX);
                    }

                    let (amount_ustx, pox_addr, lock_period, first_reward_cycle) =
                        get_stacker_info(&mut peer, &key_to_stacks_addr(&alice).into()).unwrap();
                    eprintln!("\nAlice: {} uSTX stacked for {} cycle(s); addr is {:?}; first reward cycle is {}\n", amount_ustx, lock_period, &pox_addr, first_reward_cycle);

                    if cur_reward_cycle == alice_reward_cycle {
                        assert_eq!(
                            reward_addrs.len(),
                            0,
                            "charlie rejected in this cycle, so no reward address"
                        );
                    } else {
                        // charlie didn't reject this cycle, so Alice's reward address should be
                        // present
                        assert_eq!(reward_addrs.len(), 1);
                        assert_eq!(
                            (reward_addrs[0].0).version,
                            AddressHashMode::SerializeP2PKH.to_version_testnet()
                        );
                        assert_eq!((reward_addrs[0].0).bytes, key_to_stacks_addr(&alice).bytes);
                        assert_eq!(reward_addrs[0].1, 1024 * POX_THRESHOLD_STEPS_USTX);
                    }

                    // Lock-up is consistent with stacker state
                    let alice_account = get_account(&mut peer, &key_to_stacks_addr(&alice).into());
                    assert_eq!(alice_account.stx_balance.amount_unlocked(), 0);
                    assert_eq!(
                        alice_account.stx_balance.amount_locked(),
                        1024 * POX_THRESHOLD_STEPS_USTX
                    );
                    assert_eq!(
                        alice_account.stx_balance.unlock_height() as u128,
                        (first_reward_cycle + lock_period)
                            * (burnchain.pox_constants.reward_cycle_length as u128)
                            + (burnchain.first_block_height as u128)
                    );
                } else {
                    // no reward addresses
                    assert_eq!(reward_addrs.len(), 0);
                }
            }
        }
    }

    // TODO: need Stacking-rejection with a BTC address -- contract name in OP_RETURN? (NEXT)
}
