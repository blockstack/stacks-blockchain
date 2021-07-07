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

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::convert::TryInto;
use std::fmt;
use std::mem::replace;

use vm::ast;
use vm::ast::ContractAST;
use vm::callables::{DefinedFunction, FunctionIdentifier};
use vm::contracts::Contract;
use vm::costs::{
    cost_functions, runtime_cost, ClarityCostFunctionReference, CostErrors, CostTracker,
    ExecutionCost, LimitedCostTracker,
};
use vm::database::{
    ClarityDatabase, DataMapMetadata, DataVariableMetadata, FungibleTokenMetadata,
    NonFungibleTokenMetadata,
};
use vm::errors::{CheckErrors, InterpreterError, InterpreterResult as Result, RuntimeErrorType};
use vm::functions::handle_contract_call_special_cases;
use vm::representations::{ClarityName, ContractName, SymbolicExpression};
use vm::stx_transfer_consolidated;
use vm::types::signatures::FunctionSignature;
use vm::types::{
    AssetIdentifier, PrincipalData, QualifiedContractIdentifier, TraitIdentifier, TypeSignature,
    Value,
};
use vm::{eval, is_reserved};

use chainstate::stacks::db::StacksChainState;
use chainstate::stacks::events::*;
use chainstate::stacks::Error as ChainstateError;

use crate::types::chainstate::StacksBlockId;
use crate::types::chainstate::StacksMicroblockHeader;

use serde::Serialize;
use vm::costs::cost_functions::ClarityCostFunction;

use vm::coverage::CoverageReporter;

pub const MAX_CONTEXT_DEPTH: u16 = 256;

// TODO:
//    hide the environment's instance variables.
//     we don't want many of these changing after instantiation.
pub struct Environment<'a, 'b> {
    pub global_context: &'a mut GlobalContext<'b>,
    pub contract_context: &'a ContractContext,
    pub call_stack: &'a mut CallStack,
    pub sender: Option<PrincipalData>,
    pub caller: Option<PrincipalData>,
}

pub struct OwnedEnvironment<'a> {
    context: GlobalContext<'a>,
    default_contract: ContractContext,
    call_stack: CallStack,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AssetMapEntry {
    STX(u128),
    Burn(u128),
    Token(u128),
    Asset(Vec<Value>),
}

/**
The AssetMap is used to track which assets have been transfered from whom
during the execution of a transaction.
*/
#[derive(Debug, Clone)]
pub struct AssetMap {
    stx_map: HashMap<PrincipalData, u128>,
    burn_map: HashMap<PrincipalData, u128>,
    token_map: HashMap<PrincipalData, HashMap<AssetIdentifier, u128>>,
    asset_map: HashMap<PrincipalData, HashMap<AssetIdentifier, Vec<Value>>>,
}

impl AssetMap {
    pub fn to_json(&self) -> serde_json::Value {
        let stx: serde_json::map::Map<_, _> = self
            .stx_map
            .iter()
            .map(|(principal, amount)| {
                (
                    format!("{}", principal),
                    serde_json::value::Value::String(format!("{}", amount)),
                )
            })
            .collect();

        let burns: serde_json::map::Map<_, _> = self
            .burn_map
            .iter()
            .map(|(principal, amount)| {
                (
                    format!("{}", principal),
                    serde_json::value::Value::String(format!("{}", amount)),
                )
            })
            .collect();

        let tokens: serde_json::map::Map<_, _> = self
            .token_map
            .iter()
            .map(|(principal, token_map)| {
                let token_json: serde_json::map::Map<_, _> = token_map
                    .iter()
                    .map(|(asset_id, amount)| {
                        (
                            format!("{}", asset_id),
                            serde_json::value::Value::String(format!("{}", amount)),
                        )
                    })
                    .collect();

                (
                    format!("{}", principal),
                    serde_json::value::Value::Object(token_json),
                )
            })
            .collect();

        let assets: serde_json::map::Map<_, _> = self
            .asset_map
            .iter()
            .map(|(principal, nft_map)| {
                let nft_json: serde_json::map::Map<_, _> = nft_map
                    .iter()
                    .map(|(asset_id, nft_values)| {
                        let nft_array = nft_values
                            .iter()
                            .map(|nft_value| {
                                serde_json::value::Value::String(format!("{}", nft_value))
                            })
                            .collect();

                        (
                            format!("{}", asset_id),
                            serde_json::value::Value::Array(nft_array),
                        )
                    })
                    .collect();

                (
                    format!("{}", principal),
                    serde_json::value::Value::Object(nft_json),
                )
            })
            .collect();

        json!({
            "stx": stx,
            "burns": burns,
            "tokens": tokens,
            "assets": assets
        })
    }
}

#[derive(Debug, Clone)]
pub struct EventBatch {
    pub events: Vec<StacksTransactionEvent>,
}

/** GlobalContext represents the outermost context for a single transaction's
     execution. It tracks an asset changes that occurred during the
     processing of the transaction, whether or not the current context is read_only,
     and is responsible for committing/rolling-back transactions as they error or
     abort.
*/
pub struct GlobalContext<'a> {
    asset_maps: Vec<AssetMap>,
    pub event_batches: Vec<EventBatch>,
    pub database: ClarityDatabase<'a>,
    read_only: Vec<bool>,
    pub cost_track: LimitedCostTracker,
    pub mainnet: bool,
    pub coverage_reporting: Option<CoverageReporter>,
}

#[derive(Serialize, Deserialize, Clone)]
pub struct ContractContext {
    pub contract_identifier: QualifiedContractIdentifier,
    pub variables: HashMap<ClarityName, Value>,
    pub functions: HashMap<ClarityName, DefinedFunction>,
    pub defined_traits: HashMap<ClarityName, BTreeMap<ClarityName, FunctionSignature>>,
    pub implemented_traits: HashSet<TraitIdentifier>,
    // tracks the names of NFTs, FTs, Maps, and Data Vars.
    //  used for ensuring that they never are defined twice.
    pub persisted_names: HashSet<ClarityName>,
    // track metadata for contract defined storage
    pub meta_data_map: HashMap<ClarityName, DataMapMetadata>,
    pub meta_data_var: HashMap<ClarityName, DataVariableMetadata>,
    pub meta_nft: HashMap<ClarityName, NonFungibleTokenMetadata>,
    pub meta_ft: HashMap<ClarityName, FungibleTokenMetadata>,
    pub data_size: u64,
}

pub struct LocalContext<'a> {
    pub function_context: Option<&'a LocalContext<'a>>,
    pub parent: Option<&'a LocalContext<'a>>,
    pub variables: HashMap<ClarityName, Value>,
    pub callable_contracts: HashMap<ClarityName, (QualifiedContractIdentifier, TraitIdentifier)>,
    depth: u16,
}

pub struct CallStack {
    stack: Vec<FunctionIdentifier>,
    set: HashSet<FunctionIdentifier>,
    apply_depth: usize,
}

pub type StackTrace = Vec<FunctionIdentifier>;

pub const TRANSIENT_CONTRACT_NAME: &str = "__transient";

impl AssetMap {
    pub fn new() -> AssetMap {
        AssetMap {
            stx_map: HashMap::new(),
            burn_map: HashMap::new(),
            token_map: HashMap::new(),
            asset_map: HashMap::new(),
        }
    }

    // This will get the next amount for a (principal, stx) entry in the stx table.
    fn get_next_stx_amount(&self, principal: &PrincipalData, amount: u128) -> Result<u128> {
        let current_amount = self.stx_map.get(principal).unwrap_or(&0);
        current_amount
            .checked_add(amount)
            .ok_or(RuntimeErrorType::ArithmeticOverflow.into())
    }

    // This will get the next amount for a (principal, stx) entry in the burn table.
    fn get_next_stx_burn_amount(&self, principal: &PrincipalData, amount: u128) -> Result<u128> {
        let current_amount = self.burn_map.get(principal).unwrap_or(&0);
        current_amount
            .checked_add(amount)
            .ok_or(RuntimeErrorType::ArithmeticOverflow.into())
    }

    // This will get the next amount for a (principal, asset) entry in the asset table.
    fn get_next_amount(
        &self,
        principal: &PrincipalData,
        asset: &AssetIdentifier,
        amount: u128,
    ) -> Result<u128> {
        let current_amount = match self.token_map.get(principal) {
            Some(principal_map) => *principal_map.get(&asset).unwrap_or(&0),
            None => 0,
        };

        current_amount
            .checked_add(amount)
            .ok_or(RuntimeErrorType::ArithmeticOverflow.into())
    }

    pub fn add_stx_transfer(&mut self, principal: &PrincipalData, amount: u128) -> Result<()> {
        let next_amount = self.get_next_stx_amount(principal, amount)?;
        self.stx_map.insert(principal.clone(), next_amount);

        Ok(())
    }

    pub fn add_stx_burn(&mut self, principal: &PrincipalData, amount: u128) -> Result<()> {
        let next_amount = self.get_next_stx_burn_amount(principal, amount)?;
        self.burn_map.insert(principal.clone(), next_amount);

        Ok(())
    }

    pub fn add_asset_transfer(
        &mut self,
        principal: &PrincipalData,
        asset: AssetIdentifier,
        transfered: Value,
    ) {
        if !self.asset_map.contains_key(principal) {
            self.asset_map.insert(principal.clone(), HashMap::new());
        }

        let principal_map = self.asset_map.get_mut(principal).unwrap(); // should always exist, because of checked insert above.

        if principal_map.contains_key(&asset) {
            principal_map.get_mut(&asset).unwrap().push(transfered);
        } else {
            principal_map.insert(asset, vec![transfered]);
        }
    }

    pub fn add_token_transfer(
        &mut self,
        principal: &PrincipalData,
        asset: AssetIdentifier,
        amount: u128,
    ) -> Result<()> {
        let next_amount = self.get_next_amount(principal, &asset, amount)?;

        if !self.token_map.contains_key(principal) {
            self.token_map.insert(principal.clone(), HashMap::new());
        }

        let principal_map = self.token_map.get_mut(principal).unwrap(); // should always exist, because of checked insert above.

        principal_map.insert(asset, next_amount);

        Ok(())
    }

    // This will add any asset transfer data from other to self,
    //   aborting _all_ changes in the event of an error, leaving self unchanged
    pub fn commit_other(&mut self, mut other: AssetMap) -> Result<()> {
        let mut to_add = Vec::new();
        let mut stx_to_add = Vec::new();
        let mut stx_burn_to_add = Vec::new();

        for (principal, mut principal_map) in other.token_map.drain() {
            for (asset, amount) in principal_map.drain() {
                let next_amount = self.get_next_amount(&principal, &asset, amount)?;
                to_add.push((principal.clone(), asset, next_amount));
            }
        }

        for (principal, stx_amount) in other.stx_map.drain() {
            let next_amount = self.get_next_stx_amount(&principal, stx_amount)?;
            stx_to_add.push((principal.clone(), next_amount));
        }

        for (principal, stx_burn_amount) in other.burn_map.drain() {
            let next_amount = self.get_next_stx_burn_amount(&principal, stx_burn_amount)?;
            stx_burn_to_add.push((principal.clone(), next_amount));
        }

        // After this point, this function will not fail.
        for (principal, mut principal_map) in other.asset_map.drain() {
            for (asset, mut transfers) in principal_map.drain() {
                if !self.asset_map.contains_key(&principal) {
                    self.asset_map.insert(principal.clone(), HashMap::new());
                }

                let landing_map = self.asset_map.get_mut(&principal).unwrap(); // should always exist, because of checked insert above.
                if landing_map.contains_key(&asset) {
                    let landing_vec = landing_map.get_mut(&asset).unwrap();
                    landing_vec.append(&mut transfers);
                } else {
                    landing_map.insert(asset, transfers);
                }
            }
        }

        for (principal, stx_amount) in stx_to_add.drain(..) {
            self.stx_map.insert(principal, stx_amount);
        }

        for (principal, stx_burn_amount) in stx_burn_to_add.drain(..) {
            self.burn_map.insert(principal, stx_burn_amount);
        }

        for (principal, asset, amount) in to_add.drain(..) {
            if !self.token_map.contains_key(&principal) {
                self.token_map.insert(principal.clone(), HashMap::new());
            }

            let principal_map = self.token_map.get_mut(&principal).unwrap(); // should always exist, because of checked insert above.
            principal_map.insert(asset, amount);
        }

        Ok(())
    }

    pub fn to_table(mut self) -> HashMap<PrincipalData, HashMap<AssetIdentifier, AssetMapEntry>> {
        let mut map = HashMap::new();
        for (principal, mut principal_map) in self.token_map.drain() {
            let mut output_map = HashMap::new();
            for (asset, amount) in principal_map.drain() {
                output_map.insert(asset, AssetMapEntry::Token(amount));
            }
            map.insert(principal, output_map);
        }

        for (principal, stx_amount) in self.stx_map.drain() {
            let output_map = if map.contains_key(&principal) {
                map.get_mut(&principal).unwrap()
            } else {
                map.insert(principal.clone(), HashMap::new());
                map.get_mut(&principal).unwrap()
            };
            output_map.insert(
                AssetIdentifier::STX(),
                AssetMapEntry::STX(stx_amount as u128),
            );
        }

        for (principal, stx_burned_amount) in self.burn_map.drain() {
            let output_map = if map.contains_key(&principal) {
                map.get_mut(&principal).unwrap()
            } else {
                map.insert(principal.clone(), HashMap::new());
                map.get_mut(&principal).unwrap()
            };
            output_map.insert(
                AssetIdentifier::STX_burned(),
                AssetMapEntry::Burn(stx_burned_amount as u128),
            );
        }

        for (principal, mut principal_map) in self.asset_map.drain() {
            let output_map = if map.contains_key(&principal) {
                map.get_mut(&principal).unwrap()
            } else {
                map.insert(principal.clone(), HashMap::new());
                map.get_mut(&principal).unwrap()
            };

            for (asset, transfers) in principal_map.drain() {
                output_map.insert(asset, AssetMapEntry::Asset(transfers));
            }
        }

        return map;
    }

    pub fn get_stx(&self, principal: &PrincipalData) -> Option<u128> {
        match self.stx_map.get(principal) {
            Some(value) => Some(*value),
            None => None,
        }
    }

    pub fn get_stx_burned(&self, principal: &PrincipalData) -> Option<u128> {
        match self.burn_map.get(principal) {
            Some(value) => Some(*value),
            None => None,
        }
    }

    pub fn get_stx_burned_total(&self) -> u128 {
        let mut total: u128 = 0;
        for principal in self.burn_map.keys() {
            total = total
                .checked_add(*self.burn_map.get(principal).unwrap_or(&0u128))
                .expect("BURN OVERFLOW");
        }
        total
    }

    pub fn get_fungible_tokens(
        &self,
        principal: &PrincipalData,
        asset_identifier: &AssetIdentifier,
    ) -> Option<u128> {
        match self.token_map.get(principal) {
            Some(ref assets) => match assets.get(asset_identifier) {
                Some(value) => Some(*value),
                None => None,
            },
            None => None,
        }
    }

    pub fn get_nonfungible_tokens(
        &self,
        principal: &PrincipalData,
        asset_identifier: &AssetIdentifier,
    ) -> Option<&Vec<Value>> {
        match self.asset_map.get(principal) {
            Some(ref assets) => match assets.get(asset_identifier) {
                Some(values) => Some(values),
                None => None,
            },
            None => None,
        }
    }
}

impl fmt::Display for AssetMap {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for (principal, principal_map) in self.token_map.iter() {
            for (asset, amount) in principal_map.iter() {
                write!(f, "{} spent {} {}\n", principal, amount, asset)?;
            }
        }
        for (principal, principal_map) in self.asset_map.iter() {
            for (asset, transfer) in principal_map.iter() {
                write!(f, "{} transfered [", principal)?;
                for t in transfer {
                    write!(f, "{}, ", t)?;
                }
                write!(f, "] {}\n", asset)?;
            }
        }
        for (principal, stx_amount) in self.stx_map.iter() {
            write!(f, "{} spent {} microSTX\n", principal, stx_amount)?;
        }
        for (principal, stx_burn_amount) in self.burn_map.iter() {
            write!(f, "{} burned {} microSTX\n", principal, stx_burn_amount)?;
        }
        write!(f, "]")
    }
}

impl EventBatch {
    pub fn new() -> EventBatch {
        EventBatch { events: vec![] }
    }
}

impl<'a> OwnedEnvironment<'a> {
    #[cfg(test)]
    pub fn new(database: ClarityDatabase<'a>) -> OwnedEnvironment<'a> {
        OwnedEnvironment {
            context: GlobalContext::new(false, database, LimitedCostTracker::new_free()),
            default_contract: ContractContext::new(QualifiedContractIdentifier::transient()),
            call_stack: CallStack::new(),
        }
    }

    #[cfg(test)]
    pub fn new_max_limit(mut database: ClarityDatabase<'a>) -> OwnedEnvironment<'a> {
        let cost_track = LimitedCostTracker::new_max_limit(&mut database)
            .expect("FAIL: problem instantiating cost tracking");

        OwnedEnvironment {
            context: GlobalContext::new(false, database, cost_track),
            default_contract: ContractContext::new(QualifiedContractIdentifier::transient()),
            call_stack: CallStack::new(),
        }
    }

    pub fn set_coverage_reporter(&mut self, reporter: CoverageReporter) {
        self.context.coverage_reporting = Some(reporter)
    }

    pub fn take_coverage_reporter(&mut self) -> Option<CoverageReporter> {
        self.context.coverage_reporting.take()
    }

    pub fn new_free(mainnet: bool, database: ClarityDatabase<'a>) -> OwnedEnvironment<'a> {
        OwnedEnvironment {
            context: GlobalContext::new(mainnet, database, LimitedCostTracker::new_free()),
            default_contract: ContractContext::new(QualifiedContractIdentifier::transient()),
            call_stack: CallStack::new(),
        }
    }

    pub fn new_cost_limited(
        mainnet: bool,
        database: ClarityDatabase<'a>,
        cost_tracker: LimitedCostTracker,
    ) -> OwnedEnvironment<'a> {
        OwnedEnvironment {
            context: GlobalContext::new(mainnet, database, cost_tracker),
            default_contract: ContractContext::new(QualifiedContractIdentifier::transient()),
            call_stack: CallStack::new(),
        }
    }

    pub fn get_exec_environment<'b>(
        &'b mut self,
        sender: Option<PrincipalData>,
    ) -> Environment<'b, 'a> {
        Environment::new(
            &mut self.context,
            &self.default_contract,
            &mut self.call_stack,
            sender.clone(),
            sender,
        )
    }

    pub fn execute_in_env<F, A, E>(
        &mut self,
        sender: PrincipalData,
        f: F,
    ) -> std::result::Result<(A, AssetMap, Vec<StacksTransactionEvent>), E>
    where
        E: From<::vm::errors::Error>,
        F: FnOnce(&mut Environment) -> std::result::Result<A, E>,
    {
        assert!(self.context.is_top_level());
        self.begin();

        let result = {
            let mut exec_env = self.get_exec_environment(Some(sender));
            f(&mut exec_env)
        };

        match result {
            Ok(return_value) => {
                let (asset_map, event_batch) = self.commit()?;
                Ok((return_value, asset_map, event_batch.events))
            }
            Err(e) => {
                self.context.roll_back();
                Err(e)
            }
        }
    }

    pub fn initialize_contract(
        &mut self,
        contract_identifier: QualifiedContractIdentifier,
        contract_content: &str,
    ) -> Result<((), AssetMap, Vec<StacksTransactionEvent>)> {
        self.execute_in_env(contract_identifier.issuer.clone().into(), |exec_env| {
            exec_env.initialize_contract(contract_identifier, contract_content)
        })
    }

    pub fn initialize_contract_from_ast(
        &mut self,
        contract_identifier: QualifiedContractIdentifier,
        contract_content: &ContractAST,
        contract_string: &str,
    ) -> Result<((), AssetMap, Vec<StacksTransactionEvent>)> {
        self.execute_in_env(contract_identifier.issuer.clone().into(), |exec_env| {
            exec_env.initialize_contract_from_ast(
                contract_identifier,
                contract_content,
                contract_string,
            )
        })
    }

    pub fn execute_transaction(
        &mut self,
        sender: PrincipalData,
        contract_identifier: QualifiedContractIdentifier,
        tx_name: &str,
        args: &[SymbolicExpression],
    ) -> Result<(Value, AssetMap, Vec<StacksTransactionEvent>)> {
        self.execute_in_env(sender, |exec_env| {
            exec_env.execute_contract(&contract_identifier, tx_name, args, false)
        })
    }

    pub fn stx_transfer(
        &mut self,
        from: &PrincipalData,
        to: &PrincipalData,
        amount: u128,
    ) -> Result<(Value, AssetMap, Vec<StacksTransactionEvent>)> {
        self.execute_in_env(from.clone(), |exec_env| {
            exec_env.stx_transfer(from, to, amount)
        })
    }

    pub fn handle_poison_microblock(
        &mut self,
        sender: &PrincipalData,
        mblock_hdr_1: &StacksMicroblockHeader,
        mblock_hdr_2: &StacksMicroblockHeader,
    ) -> std::result::Result<(Value, AssetMap, Vec<StacksTransactionEvent>), ChainstateError> {
        self.execute_in_env(sender.clone(), |exec_env| {
            exec_env.handle_poison_microblock(mblock_hdr_1, mblock_hdr_2)
        })
    }

    #[cfg(test)]
    pub fn stx_faucet(&mut self, recipient: &PrincipalData, amount: u128) {
        self.execute_in_env::<_, _, ()>(recipient.clone(), |env| {
            let mut snapshot = env
                .global_context
                .database
                .get_stx_balance_snapshot(&recipient);

            let mut balance = snapshot.balance().clone();
            balance.amount_unlocked += amount;
            snapshot.set_balance(balance);
            snapshot.save();

            env.global_context
                .database
                .increment_ustx_liquid_supply(amount)
                .unwrap();
            Ok(())
        })
        .unwrap();
    }

    #[cfg(test)]
    pub fn eval_raw(
        &mut self,
        program: &str,
    ) -> Result<(Value, AssetMap, Vec<StacksTransactionEvent>)> {
        self.execute_in_env(
            QualifiedContractIdentifier::transient().issuer.into(),
            |exec_env| exec_env.eval_raw(program),
        )
    }

    pub fn eval_read_only(
        &mut self,
        contract: &QualifiedContractIdentifier,
        program: &str,
    ) -> Result<(Value, AssetMap, Vec<StacksTransactionEvent>)> {
        self.execute_in_env(
            QualifiedContractIdentifier::transient().issuer.into(),
            |exec_env| exec_env.eval_read_only(contract, program),
        )
    }

    pub fn begin(&mut self) {
        self.context.begin();
    }

    pub fn commit(&mut self) -> Result<(AssetMap, EventBatch)> {
        let (asset_map, event_batch) = self.context.commit()?;
        let asset_map = asset_map.ok_or(InterpreterError::FailedToConstructAssetTable)?;
        let event_batch = event_batch.ok_or(InterpreterError::FailedToConstructEventBatch)?;

        Ok((asset_map, event_batch))
    }

    pub fn get_cost_total(&self) -> ExecutionCost {
        self.context.cost_track.get_total()
    }

    /// Destroys this environment, returning ownership of its database reference.
    ///  If the context wasn't top-level (i.e., it had uncommitted data), return None,
    ///   because the database is not guaranteed to be in a sane state.
    pub fn destruct(self) -> Option<(ClarityDatabase<'a>, LimitedCostTracker)> {
        self.context.destruct()
    }
}

impl CostTracker for Environment<'_, '_> {
    fn compute_cost(
        &mut self,
        cost_function: ClarityCostFunction,
        input: &[u64],
    ) -> std::result::Result<ExecutionCost, CostErrors> {
        self.global_context
            .cost_track
            .compute_cost(cost_function, input)
    }
    fn add_cost(&mut self, cost: ExecutionCost) -> std::result::Result<(), CostErrors> {
        self.global_context.cost_track.add_cost(cost)
    }
    fn add_memory(&mut self, memory: u64) -> std::result::Result<(), CostErrors> {
        self.global_context.cost_track.add_memory(memory)
    }
    fn drop_memory(&mut self, memory: u64) {
        self.global_context.cost_track.drop_memory(memory)
    }
    fn reset_memory(&mut self) {
        self.global_context.cost_track.reset_memory()
    }
    fn short_circuit_contract_call(
        &mut self,
        contract: &QualifiedContractIdentifier,
        function: &ClarityName,
        input: &[u64],
    ) -> std::result::Result<bool, CostErrors> {
        self.global_context
            .cost_track
            .short_circuit_contract_call(contract, function, input)
    }
}

impl CostTracker for GlobalContext<'_> {
    fn compute_cost(
        &mut self,
        cost_function: ClarityCostFunction,
        input: &[u64],
    ) -> std::result::Result<ExecutionCost, CostErrors> {
        self.cost_track.compute_cost(cost_function, input)
    }

    fn add_cost(&mut self, cost: ExecutionCost) -> std::result::Result<(), CostErrors> {
        self.cost_track.add_cost(cost)
    }
    fn add_memory(&mut self, memory: u64) -> std::result::Result<(), CostErrors> {
        self.cost_track.add_memory(memory)
    }
    fn drop_memory(&mut self, memory: u64) {
        self.cost_track.drop_memory(memory)
    }
    fn reset_memory(&mut self) {
        self.cost_track.reset_memory()
    }
    fn short_circuit_contract_call(
        &mut self,
        contract: &QualifiedContractIdentifier,
        function: &ClarityName,
        input: &[u64],
    ) -> std::result::Result<bool, CostErrors> {
        self.cost_track
            .short_circuit_contract_call(contract, function, input)
    }
}

impl<'a, 'b> Environment<'a, 'b> {
    // Environments pack a reference to the global context (which is basically the db),
    //   the current contract context, a call stack, and the current sender.
    // Essentially, the point of the Environment struct is to prevent all the eval functions
    //   from including all of these items in their method signatures individually. Because
    //   these different contexts can be mixed and matched (i.e., in a contract-call, you change
    //   contract context), a single "invocation" will end up creating multiple environment
    //   objects as context changes occur.
    pub fn new(
        global_context: &'a mut GlobalContext<'b>,
        contract_context: &'a ContractContext,
        call_stack: &'a mut CallStack,
        sender: Option<PrincipalData>,
        caller: Option<PrincipalData>,
    ) -> Environment<'a, 'b> {
        Environment {
            global_context,
            contract_context,
            call_stack,
            sender,
            caller,
        }
    }

    pub fn nest_as_principal<'c>(&'c mut self, sender: PrincipalData) -> Environment<'c, 'b> {
        Environment::new(
            self.global_context,
            self.contract_context,
            self.call_stack,
            Some(sender.clone()),
            Some(sender),
        )
    }

    pub fn nest_with_caller<'c>(&'c mut self, caller: PrincipalData) -> Environment<'c, 'b> {
        Environment::new(
            self.global_context,
            self.contract_context,
            self.call_stack,
            self.sender.clone(),
            Some(caller),
        )
    }

    pub fn eval_read_only(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        program: &str,
    ) -> Result<Value> {
        let parsed = ast::build_ast(contract_identifier, program, self)?.expressions;

        if parsed.len() < 1 {
            return Err(RuntimeErrorType::ParseError(
                "Expected a program of at least length 1".to_string(),
            )
            .into());
        }

        self.global_context.begin();

        let contract = self
            .global_context
            .database
            .get_contract(contract_identifier)?;

        let result = {
            let mut nested_env = Environment::new(
                &mut self.global_context,
                &contract.contract_context,
                self.call_stack,
                self.sender.clone(),
                self.caller.clone(),
            );
            let local_context = LocalContext::new();
            eval(&parsed[0], &mut nested_env, &local_context)
        };

        self.global_context.roll_back();

        result
    }

    pub fn eval_raw(&mut self, program: &str) -> Result<Value> {
        let contract_id = QualifiedContractIdentifier::transient();

        let parsed = ast::build_ast(&contract_id, program, self)?.expressions;
        if parsed.len() < 1 {
            return Err(RuntimeErrorType::ParseError(
                "Expected a program of at least length 1".to_string(),
            )
            .into());
        }
        let local_context = LocalContext::new();
        let result = { eval(&parsed[0], self, &local_context) };
        result
    }

    /// Used only for contract-call! cost short-circuiting. Once the short-circuited cost
    ///  has been evaluated and assessed, the contract-call! itself is executed "for free".
    pub fn run_free<F, A>(&mut self, to_run: F) -> A
    where
        F: FnOnce(&mut Environment) -> A,
    {
        let original_tracker = replace(
            &mut self.global_context.cost_track,
            LimitedCostTracker::new_free(),
        );
        // note: it is important that this method not return until original_tracker has been
        //  restored. DO NOT use the try syntax (?).
        let result = to_run(self);
        self.global_context.cost_track = original_tracker;
        result
    }

    pub fn execute_contract(
        &mut self,
        contract_identifier: &QualifiedContractIdentifier,
        tx_name: &str,
        args: &[SymbolicExpression],
        read_only: bool,
    ) -> Result<Value> {
        let contract_size = self
            .global_context
            .database
            .get_contract_size(contract_identifier)?;
        runtime_cost(ClarityCostFunction::LoadContract, self, contract_size)?;

        self.global_context.add_memory(contract_size)?;

        finally_drop_memory!(self.global_context, contract_size; {
            let contract = self.global_context.database.get_contract(contract_identifier)?;

            let func = contract.contract_context.lookup_function(tx_name)
                .ok_or_else(|| { CheckErrors::UndefinedFunction(tx_name.to_string()) })?;
            if !func.is_public() {
                return Err(CheckErrors::NoSuchPublicFunction(contract_identifier.to_string(), tx_name.to_string()).into());
            } else if read_only && !func.is_read_only() {
                return Err(CheckErrors::PublicFunctionNotReadOnly(contract_identifier.to_string(), tx_name.to_string()).into());
            }

            let args: Result<Vec<Value>> = args.iter()
                .map(|arg| {
                    let value = arg.match_atom_value()
                        .ok_or_else(|| InterpreterError::InterpreterError(format!("Passed non-value expression to exec_tx on {}!",
                                                                                  tx_name)))?;
                    Ok(value.clone())
                })
                .collect();

            let args = args?;

            let func_identifier = func.get_identifier();
            if self.call_stack.contains(&func_identifier) {
                return Err(CheckErrors::CircularReference(vec![func_identifier.to_string()]).into())
            }
            self.call_stack.insert(&func_identifier, true);
            let res = self.execute_function_as_transaction(&func, &args, Some(&contract.contract_context));
            self.call_stack.remove(&func_identifier, true)?;

            match res {
                Ok(value) => {
                    handle_contract_call_special_cases(&mut self.global_context, self.sender.as_ref(), contract_identifier, tx_name, &value)?;
                    Ok(value)
                },
                Err(e) => Err(e)
            }
        })
    }

    pub fn execute_function_as_transaction(
        &mut self,
        function: &DefinedFunction,
        args: &[Value],
        next_contract_context: Option<&ContractContext>,
    ) -> Result<Value> {
        let make_read_only = function.is_read_only();

        if make_read_only {
            self.global_context.begin_read_only();
        } else {
            self.global_context.begin();
        }

        let next_contract_context = next_contract_context.unwrap_or(self.contract_context);

        let result = {
            let mut nested_env = Environment::new(
                &mut self.global_context,
                next_contract_context,
                self.call_stack,
                self.sender.clone(),
                self.caller.clone(),
            );

            function.execute_apply(args, &mut nested_env)
        };

        if make_read_only {
            self.global_context.roll_back();
            result
        } else {
            self.global_context.handle_tx_result(result)
        }
    }

    pub fn evaluate_at_block(
        &mut self,
        bhh: StacksBlockId,
        closure: &SymbolicExpression,
        local: &LocalContext,
    ) -> Result<Value> {
        self.global_context.begin_read_only();

        let result = self
            .global_context
            .database
            .set_block_hash(bhh, false)
            .and_then(|prior_bhh| {
                let result = eval(closure, self, local);
                self.global_context
                    .database
                    .set_block_hash(prior_bhh, true)
                    .expect(
                    "ERROR: Failed to restore prior active block after time-shifted evaluation.",
                );
                result
            });

        self.global_context.roll_back();

        result
    }

    pub fn initialize_contract(
        &mut self,
        contract_identifier: QualifiedContractIdentifier,
        contract_content: &str,
    ) -> Result<()> {
        let contract_ast = ast::build_ast(&contract_identifier, contract_content, self)?;
        self.initialize_contract_from_ast(contract_identifier, &contract_ast, &contract_content)
    }

    pub fn initialize_contract_from_ast(
        &mut self,
        contract_identifier: QualifiedContractIdentifier,
        contract_content: &ContractAST,
        contract_string: &str,
    ) -> Result<()> {
        self.global_context.begin();

        // wrap in a closure so that `?` can be caught and the global_context can roll_back()
        //  before returning.
        let result = (|| {
            runtime_cost(
                ClarityCostFunction::ContractStorage,
                self,
                contract_string.len(),
            )?;

            if self
                .global_context
                .database
                .has_contract(&contract_identifier)
            {
                return Err(
                    CheckErrors::ContractAlreadyExists(contract_identifier.to_string()).into(),
                );
            }

            // first, store the contract _content hash_ in the data store.
            //    this is necessary before creating and accessing metadata fields in the data store,
            //      --or-- storing any analysis metadata in the data store.
            self.global_context
                .database
                .insert_contract_hash(&contract_identifier, contract_string)?;
            let memory_use = contract_string.len() as u64;
            self.add_memory(memory_use)?;

            let result = Contract::initialize_from_ast(
                contract_identifier.clone(),
                contract_content,
                &mut self.global_context,
            );
            self.drop_memory(memory_use);
            result
        })();

        match result {
            Ok(contract) => {
                let data_size = contract.contract_context.data_size;
                self.global_context
                    .database
                    .insert_contract(&contract_identifier, contract);
                self.global_context
                    .database
                    .set_contract_data_size(&contract_identifier, data_size)?;

                self.global_context.commit()?;
                Ok(())
            }
            Err(e) => {
                self.global_context.roll_back();
                Err(e)
            }
        }
    }

    /// Top-level STX-transfer, invoked by TokenTransfer transactions.
    /// Only commits if the inner stx_transfer_consolidated() returns an (ok true) value.
    /// Rolls back if it returns an (err ..) value, or if the method itself fails for some reason
    /// (miners should never build blocks that spend non-existent STX in a top-level token-transfer)
    pub fn stx_transfer(
        &mut self,
        from: &PrincipalData,
        to: &PrincipalData,
        amount: u128,
    ) -> Result<Value> {
        self.global_context.begin();
        let result = stx_transfer_consolidated(self, from, to, amount);
        match result {
            Ok(value) => match value.clone().expect_result() {
                Ok(_) => {
                    self.global_context.commit()?;
                    Ok(value)
                }
                Err(_) => {
                    self.global_context.roll_back();
                    Err(InterpreterError::InsufficientBalance.into())
                }
            },
            Err(e) => {
                self.global_context.roll_back();
                Err(e)
            }
        }
    }

    /// Top-level poison-microblock handler
    pub fn handle_poison_microblock(
        &mut self,
        mblock_header_1: &StacksMicroblockHeader,
        mblock_header_2: &StacksMicroblockHeader,
    ) -> std::result::Result<Value, ChainstateError> {
        self.global_context.begin();
        let result =
            StacksChainState::handle_poison_microblock(self, mblock_header_1, mblock_header_2);
        match result {
            Ok(ret) => {
                self.global_context.commit()?;
                Ok(ret)
            }
            Err(e) => {
                self.global_context.roll_back();
                Err(e)
            }
        }
    }

    pub fn register_print_event(&mut self, value: Value) -> Result<()> {
        let print_event = SmartContractEventData {
            key: (
                self.contract_context.contract_identifier.clone(),
                "print".to_string(),
            ),
            value,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch
                .events
                .push(StacksTransactionEvent::SmartContractEvent(print_event));
        }
        Ok(())
    }

    pub fn register_stx_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        amount: u128,
    ) -> Result<()> {
        let event_data = STXTransferEventData {
            sender,
            recipient,
            amount,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(StacksTransactionEvent::STXEvent(
                STXEventType::STXTransferEvent(event_data),
            ));
        }
        Ok(())
    }

    pub fn register_stx_burn_event(&mut self, sender: PrincipalData, amount: u128) -> Result<()> {
        let event_data = STXBurnEventData { sender, amount };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(StacksTransactionEvent::STXEvent(
                STXEventType::STXBurnEvent(event_data),
            ));
        }
        Ok(())
    }

    pub fn register_nft_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<()> {
        let event_data = NFTTransferEventData {
            sender,
            recipient,
            asset_identifier,
            value,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(StacksTransactionEvent::NFTEvent(
                NFTEventType::NFTTransferEvent(event_data),
            ));
        }
        Ok(())
    }

    pub fn register_nft_mint_event(
        &mut self,
        recipient: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<()> {
        let event_data = NFTMintEventData {
            recipient,
            asset_identifier,
            value,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(StacksTransactionEvent::NFTEvent(
                NFTEventType::NFTMintEvent(event_data),
            ));
        }
        Ok(())
    }

    pub fn register_nft_burn_event(
        &mut self,
        sender: PrincipalData,
        value: Value,
        asset_identifier: AssetIdentifier,
    ) -> Result<()> {
        let event_data = NFTBurnEventData {
            sender,
            asset_identifier,
            value,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(StacksTransactionEvent::NFTEvent(
                NFTEventType::NFTBurnEvent(event_data),
            ));
        }
        Ok(())
    }

    pub fn register_ft_transfer_event(
        &mut self,
        sender: PrincipalData,
        recipient: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<()> {
        let event_data = FTTransferEventData {
            sender,
            recipient,
            asset_identifier,
            amount,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch.events.push(StacksTransactionEvent::FTEvent(
                FTEventType::FTTransferEvent(event_data),
            ));
        }
        Ok(())
    }

    pub fn register_ft_mint_event(
        &mut self,
        recipient: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<()> {
        let event_data = FTMintEventData {
            recipient,
            asset_identifier,
            amount,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch
                .events
                .push(StacksTransactionEvent::FTEvent(FTEventType::FTMintEvent(
                    event_data,
                )));
        }
        Ok(())
    }

    pub fn register_ft_burn_event(
        &mut self,
        sender: PrincipalData,
        amount: u128,
        asset_identifier: AssetIdentifier,
    ) -> Result<()> {
        let event_data = FTBurnEventData {
            sender,
            asset_identifier,
            amount,
        };

        if let Some(batch) = self.global_context.event_batches.last_mut() {
            batch
                .events
                .push(StacksTransactionEvent::FTEvent(FTEventType::FTBurnEvent(
                    event_data,
                )));
        }
        Ok(())
    }
}

impl<'a> GlobalContext<'a> {
    // Instantiate a new Global Context
    pub fn new(
        mainnet: bool,
        database: ClarityDatabase,
        cost_track: LimitedCostTracker,
    ) -> GlobalContext {
        GlobalContext {
            database,
            cost_track,
            read_only: Vec::new(),
            asset_maps: Vec::new(),
            event_batches: Vec::new(),
            mainnet,
            coverage_reporting: None,
        }
    }

    pub fn is_top_level(&self) -> bool {
        self.asset_maps.len() == 0
    }

    fn get_asset_map(&mut self) -> &mut AssetMap {
        self.asset_maps
            .last_mut()
            .expect("Failed to obtain asset map")
    }

    pub fn log_asset_transfer(
        &mut self,
        sender: &PrincipalData,
        contract_identifier: &QualifiedContractIdentifier,
        asset_name: &ClarityName,
        transfered: Value,
    ) {
        let asset_identifier = AssetIdentifier {
            contract_identifier: contract_identifier.clone(),
            asset_name: asset_name.clone(),
        };
        self.get_asset_map()
            .add_asset_transfer(sender, asset_identifier, transfered)
    }

    pub fn log_token_transfer(
        &mut self,
        sender: &PrincipalData,
        contract_identifier: &QualifiedContractIdentifier,
        asset_name: &ClarityName,
        transfered: u128,
    ) -> Result<()> {
        let asset_identifier = AssetIdentifier {
            contract_identifier: contract_identifier.clone(),
            asset_name: asset_name.clone(),
        };
        self.get_asset_map()
            .add_token_transfer(sender, asset_identifier, transfered)
    }

    pub fn log_stx_transfer(&mut self, sender: &PrincipalData, transfered: u128) -> Result<()> {
        self.get_asset_map().add_stx_transfer(sender, transfered)
    }

    pub fn log_stx_burn(&mut self, sender: &PrincipalData, transfered: u128) -> Result<()> {
        self.get_asset_map().add_stx_burn(sender, transfered)
    }

    pub fn execute<F, T>(&mut self, f: F) -> Result<T>
    where
        F: FnOnce(&mut Self) -> Result<T>,
    {
        self.begin();
        let result = f(self).or_else(|e| {
            self.roll_back();
            Err(e)
        })?;
        self.commit()?;
        Ok(result)
    }

    pub fn is_read_only(&self) -> bool {
        // top level context defaults to writable.
        self.read_only.last().cloned().unwrap_or(false)
    }

    pub fn begin(&mut self) {
        self.asset_maps.push(AssetMap::new());
        self.event_batches.push(EventBatch::new());
        self.database.begin();
        let read_only = self.is_read_only();
        self.read_only.push(read_only);
    }

    pub fn begin_read_only(&mut self) {
        self.asset_maps.push(AssetMap::new());
        self.event_batches.push(EventBatch::new());
        self.database.begin();
        self.read_only.push(true);
    }

    pub fn commit(&mut self) -> Result<(Option<AssetMap>, Option<EventBatch>)> {
        trace!("Calling commit");
        self.read_only.pop();
        let asset_map = self
            .asset_maps
            .pop()
            .expect("ERROR: Committed non-nested context.");
        let mut event_batch = self
            .event_batches
            .pop()
            .expect("ERROR: Committed non-nested context.");

        let out_map = match self.asset_maps.last_mut() {
            Some(tail_back) => {
                if let Err(e) = tail_back.commit_other(asset_map) {
                    self.database.roll_back();
                    return Err(e);
                }
                None
            }
            None => Some(asset_map),
        };

        let out_batch = match self.event_batches.last_mut() {
            Some(tail_back) => {
                tail_back.events.append(&mut event_batch.events);
                None
            }
            None => Some(event_batch),
        };

        self.database.commit();
        Ok((out_map, out_batch))
    }

    pub fn roll_back(&mut self) {
        let popped = self.asset_maps.pop();
        assert!(popped.is_some());
        let popped = self.read_only.pop();
        assert!(popped.is_some());
        let popped = self.event_batches.pop();
        assert!(popped.is_some());

        self.database.roll_back();
    }

    pub fn handle_tx_result(&mut self, result: Result<Value>) -> Result<Value> {
        if let Ok(result) = result {
            if let Value::Response(data) = result {
                if data.committed {
                    self.commit()?;
                } else {
                    self.roll_back();
                }
                Ok(Value::Response(data))
            } else {
                Err(
                    CheckErrors::PublicFunctionMustReturnResponse(TypeSignature::type_of(&result))
                        .into(),
                )
            }
        } else {
            self.roll_back();
            result
        }
    }

    /// Destroys this context, returning ownership of its database reference.
    ///  If the context wasn't top-level (i.e., it had uncommitted data), return None,
    ///   because the database is not guaranteed to be in a sane state.
    pub fn destruct(self) -> Option<(ClarityDatabase<'a>, LimitedCostTracker)> {
        if self.is_top_level() {
            Some((self.database, self.cost_track))
        } else {
            None
        }
    }
}

impl ContractContext {
    pub fn new(contract_identifier: QualifiedContractIdentifier) -> Self {
        Self {
            contract_identifier,
            variables: HashMap::new(),
            functions: HashMap::new(),
            defined_traits: HashMap::new(),
            implemented_traits: HashSet::new(),
            persisted_names: HashSet::new(),
            data_size: 0,
            meta_data_map: HashMap::new(),
            meta_data_var: HashMap::new(),
            meta_nft: HashMap::new(),
            meta_ft: HashMap::new(),
        }
    }

    pub fn lookup_variable(&self, name: &str) -> Option<&Value> {
        self.variables.get(name)
    }

    pub fn lookup_function(&self, name: &str) -> Option<DefinedFunction> {
        self.functions.get(name).cloned()
    }

    pub fn lookup_trait_definition(
        &self,
        name: &str,
    ) -> Option<BTreeMap<ClarityName, FunctionSignature>> {
        self.defined_traits.get(name).cloned()
    }

    pub fn is_explicitly_implementing_trait(&self, trait_identifier: &TraitIdentifier) -> bool {
        self.implemented_traits.contains(trait_identifier)
    }

    pub fn is_name_used(&self, name: &str) -> bool {
        is_reserved(name)
            || self.variables.contains_key(name)
            || self.functions.contains_key(name)
            || self.persisted_names.contains(name)
            || self.defined_traits.contains_key(name)
    }
}

impl<'a> LocalContext<'a> {
    pub fn new() -> LocalContext<'a> {
        LocalContext {
            function_context: Option::None,
            parent: Option::None,
            callable_contracts: HashMap::new(),
            variables: HashMap::new(),
            depth: 0,
        }
    }

    pub fn depth(&self) -> u16 {
        self.depth
    }

    pub fn function_context(&self) -> &LocalContext {
        match self.function_context {
            Some(context) => context,
            None => self,
        }
    }

    pub fn extend(&'a self) -> Result<LocalContext<'a>> {
        if self.depth >= MAX_CONTEXT_DEPTH {
            Err(RuntimeErrorType::MaxContextDepthReached.into())
        } else {
            Ok(LocalContext {
                function_context: Some(self.function_context()),
                parent: Some(self),
                callable_contracts: HashMap::new(),
                variables: HashMap::new(),
                depth: self.depth + 1,
            })
        }
    }

    pub fn lookup_variable(&self, name: &str) -> Option<&Value> {
        match self.variables.get(name) {
            Some(value) => Some(value),
            None => match self.parent {
                Some(parent) => parent.lookup_variable(name),
                None => None,
            },
        }
    }

    pub fn lookup_callable_contract(
        &self,
        name: &str,
    ) -> Option<&(QualifiedContractIdentifier, TraitIdentifier)> {
        self.function_context().callable_contracts.get(name)
    }
}

impl CallStack {
    pub fn new() -> CallStack {
        CallStack {
            stack: Vec::new(),
            set: HashSet::new(),
            apply_depth: 0,
        }
    }

    pub fn depth(&self) -> usize {
        self.stack.len() + self.apply_depth
    }

    pub fn contains(&self, function: &FunctionIdentifier) -> bool {
        self.set.contains(function)
    }

    pub fn insert(&mut self, function: &FunctionIdentifier, track: bool) {
        self.stack.push(function.clone());
        if track {
            self.set.insert(function.clone());
        }
    }

    pub fn incr_apply_depth(&mut self) {
        self.apply_depth += 1;
    }

    pub fn decr_apply_depth(&mut self) {
        self.apply_depth -= 1;
    }

    pub fn remove(&mut self, function: &FunctionIdentifier, tracked: bool) -> Result<()> {
        if let Some(removed) = self.stack.pop() {
            if removed != *function {
                return Err(InterpreterError::InterpreterError(
                    "Tried to remove item from empty call stack.".to_string(),
                )
                .into());
            }
            if tracked && !self.set.remove(&function) {
                panic!("Tried to remove tracked function from call stack, but could not find in current context.")
            }
            Ok(())
        } else {
            return Err(InterpreterError::InterpreterError(
                "Tried to remove item from empty call stack.".to_string(),
            )
            .into());
        }
    }

    #[cfg(feature = "developer-mode")]
    pub fn make_stack_trace(&self) -> StackTrace {
        self.stack.clone()
    }

    #[cfg(not(feature = "developer-mode"))]
    pub fn make_stack_trace(&self) -> StackTrace {
        Vec::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_asset_map_abort() {
        let a_contract_id = QualifiedContractIdentifier::local("a").unwrap();
        let b_contract_id = QualifiedContractIdentifier::local("b").unwrap();

        let p1 = PrincipalData::Contract(a_contract_id.clone());
        let p2 = PrincipalData::Contract(b_contract_id.clone());

        let t1 = AssetIdentifier {
            contract_identifier: a_contract_id.clone(),
            asset_name: "a".into(),
        };
        let _t2 = AssetIdentifier {
            contract_identifier: b_contract_id.clone(),
            asset_name: "a".into(),
        };

        let mut am1 = AssetMap::new();
        let mut am2 = AssetMap::new();

        am1.add_token_transfer(&p1, t1.clone(), 1).unwrap();
        am1.add_token_transfer(&p2, t1.clone(), u128::max_value())
            .unwrap();
        am2.add_token_transfer(&p1, t1.clone(), 1).unwrap();
        am2.add_token_transfer(&p2, t1.clone(), 1).unwrap();

        am1.commit_other(am2).unwrap_err();

        let table = am1.to_table();

        assert_eq!(table[&p2][&t1], AssetMapEntry::Token(u128::max_value()));
        assert_eq!(table[&p1][&t1], AssetMapEntry::Token(1));
    }

    #[test]
    fn test_asset_map_combinations() {
        let a_contract_id = QualifiedContractIdentifier::local("a").unwrap();
        let b_contract_id = QualifiedContractIdentifier::local("b").unwrap();
        let c_contract_id = QualifiedContractIdentifier::local("c").unwrap();
        let d_contract_id = QualifiedContractIdentifier::local("d").unwrap();
        let e_contract_id = QualifiedContractIdentifier::local("e").unwrap();
        let f_contract_id = QualifiedContractIdentifier::local("f").unwrap();
        let g_contract_id = QualifiedContractIdentifier::local("g").unwrap();

        let p1 = PrincipalData::Contract(a_contract_id.clone());
        let p2 = PrincipalData::Contract(b_contract_id.clone());
        let p3 = PrincipalData::Contract(c_contract_id.clone());
        let _p4 = PrincipalData::Contract(d_contract_id.clone());
        let _p5 = PrincipalData::Contract(e_contract_id.clone());
        let _p6 = PrincipalData::Contract(f_contract_id.clone());
        let _p7 = PrincipalData::Contract(g_contract_id.clone());

        let t1 = AssetIdentifier {
            contract_identifier: a_contract_id.clone(),
            asset_name: "a".into(),
        };
        let t2 = AssetIdentifier {
            contract_identifier: b_contract_id.clone(),
            asset_name: "a".into(),
        };
        let t3 = AssetIdentifier {
            contract_identifier: c_contract_id.clone(),
            asset_name: "a".into(),
        };
        let t4 = AssetIdentifier {
            contract_identifier: d_contract_id.clone(),
            asset_name: "a".into(),
        };
        let t5 = AssetIdentifier {
            contract_identifier: e_contract_id.clone(),
            asset_name: "a".into(),
        };
        let t6 = AssetIdentifier::STX();
        let t7 = AssetIdentifier::STX_burned();

        let mut am1 = AssetMap::new();
        let mut am2 = AssetMap::new();

        am1.add_token_transfer(&p1, t1.clone(), 10).unwrap();
        am2.add_token_transfer(&p1, t1.clone(), 15).unwrap();

        am1.add_stx_transfer(&p1, 20).unwrap();
        am2.add_stx_transfer(&p2, 25).unwrap();

        am1.add_stx_burn(&p1, 30).unwrap();
        am2.add_stx_burn(&p2, 35).unwrap();

        // test merging in a token that _didn't_ have an entry in the parent
        am2.add_token_transfer(&p1, t4.clone(), 1).unwrap();

        // test merging in a principal that _didn't_ have an entry in the parent
        am2.add_token_transfer(&p2, t2.clone(), 10).unwrap();
        am2.add_token_transfer(&p2, t2.clone(), 1).unwrap();

        // test merging in a principal that _didn't_ have an entry in the parent
        am2.add_asset_transfer(&p3, t3.clone(), Value::Int(10));

        // test merging in an asset that _didn't_ have an entry in the parent
        am1.add_asset_transfer(&p1, t5.clone(), Value::Int(0));
        am2.add_asset_transfer(&p1, t3.clone(), Value::Int(1));
        am2.add_asset_transfer(&p1, t3.clone(), Value::Int(0));

        // test merging in an asset that _does_ have an entry in the parent
        am1.add_asset_transfer(&p2, t3.clone(), Value::Int(2));
        am1.add_asset_transfer(&p2, t3.clone(), Value::Int(5));
        am2.add_asset_transfer(&p2, t3.clone(), Value::Int(3));
        am2.add_asset_transfer(&p2, t3.clone(), Value::Int(4));

        // test merging in STX transfers
        am1.add_stx_transfer(&p1, 21).unwrap();
        am2.add_stx_transfer(&p2, 26).unwrap();

        // test merging in STX burns
        am1.add_stx_burn(&p1, 31).unwrap();
        am2.add_stx_burn(&p2, 36).unwrap();

        am1.commit_other(am2).unwrap();

        let table = am1.to_table();

        // 3 Principals
        assert_eq!(table.len(), 3);

        assert_eq!(table[&p1][&t1], AssetMapEntry::Token(25));
        assert_eq!(table[&p1][&t4], AssetMapEntry::Token(1));

        assert_eq!(table[&p2][&t2], AssetMapEntry::Token(11));

        assert_eq!(
            table[&p2][&t3],
            AssetMapEntry::Asset(vec![
                Value::Int(2),
                Value::Int(5),
                Value::Int(3),
                Value::Int(4)
            ])
        );

        assert_eq!(
            table[&p1][&t3],
            AssetMapEntry::Asset(vec![Value::Int(1), Value::Int(0)])
        );
        assert_eq!(table[&p1][&t5], AssetMapEntry::Asset(vec![Value::Int(0)]));

        assert_eq!(table[&p3][&t3], AssetMapEntry::Asset(vec![Value::Int(10)]));

        assert_eq!(table[&p1][&t6], AssetMapEntry::STX(20 + 21));
        assert_eq!(table[&p2][&t6], AssetMapEntry::STX(25 + 26));

        assert_eq!(table[&p1][&t7], AssetMapEntry::Burn(30 + 31));
        assert_eq!(table[&p2][&t7], AssetMapEntry::Burn(35 + 36));
    }
}
