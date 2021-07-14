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

use std::cmp;
use std::convert::{TryFrom, TryInto};
use vm::costs::cost_functions::ClarityCostFunction;
use vm::costs::{CostTracker, MemoryConsumer};

use vm::contexts::{Environment, GlobalContext};
use vm::errors::Error;
use vm::errors::{CheckErrors, InterpreterError, InterpreterResult as Result, RuntimeErrorType};
use vm::representations::{ClarityName, SymbolicExpression, SymbolicExpressionType};
use vm::types::{
    BuffData, OptionalData, PrincipalData, QualifiedContractIdentifier, SequenceData, TupleData,
    TypeSignature, Value,
};

use crate::chainstate::stacks::boot::POX_1_NAME;
use crate::chainstate::stacks::boot::POX_2_NAME;
use crate::types::chainstate::StacksMicroblockHeader;
use crate::util::boot::boot_code_id;
use chainstate::stacks::db::StacksChainState;
use chainstate::stacks::events::{STXEventType, STXLockEventData, StacksTransactionEvent};
use chainstate::stacks::Error as ChainstateError;

use util::hash::Hash160;

use crate::vm::costs::runtime_cost;

fn parse_pox_stacking_result(
    result: &Value,
) -> std::result::Result<(PrincipalData, u128, u64), i128> {
    match result.clone().expect_result() {
        Ok(res) => {
            // should have gotten back (ok (tuple (stacker principal) (lock-amount uint) (unlock-burn-height uint)))
            let tuple_data = res.expect_tuple();
            let stacker = tuple_data
                .get("stacker")
                .expect(&format!("FATAL: no 'stacker'"))
                .to_owned()
                .expect_principal();

            let lock_amount = tuple_data
                .get("lock-amount")
                .expect(&format!("FATAL: no 'lock-amount'"))
                .to_owned()
                .expect_u128();

            let unlock_burn_height = tuple_data
                .get("unlock-burn-height")
                .expect(&format!("FATAL: no 'unlock-burn-height'"))
                .to_owned()
                .expect_u128()
                .try_into()
                .expect("FATAL: 'unlock-burn-height' overflow");

            Ok((stacker, lock_amount, unlock_burn_height))
        }
        Err(e) => Err(e.expect_i128()),
    }
}

fn parse_pox_extend_result(result: &Value) -> std::result::Result<(PrincipalData, u64), i128> {
    match result.clone().expect_result() {
        Ok(res) => {
            // should have gotten back (ok { stacker: principal, unlock-burn-height: uint })
            let tuple_data = res.expect_tuple();
            let stacker = tuple_data
                .get("stacker")
                .expect(&format!("FATAL: no 'stacker'"))
                .to_owned()
                .expect_principal();

            let unlock_burn_height = tuple_data
                .get("unlock-burn-height")
                .expect(&format!("FATAL: no 'unlock-burn-height'"))
                .to_owned()
                .expect_u128()
                .try_into()
                .expect("FATAL: 'unlock-burn-height' overflow");

            Ok((stacker, unlock_burn_height))
        }
        Err(e) => Err(e.expect_i128()),
    }
}

/// Handle special cases when calling into the PoX API contract
fn handle_pox_v1_api_contract_call(
    global_context: &mut GlobalContext,
    _sender_opt: Option<&PrincipalData>,
    function_name: &str,
    value: &Value,
) -> Result<()> {
    if function_name == "stack-stx" || function_name == "delegate-stack-stx" {
        debug!(
            "Handle special-case contract-call to {:?} {} (which returned {:?})",
            boot_code_id(POX_1_NAME, global_context.mainnet),
            function_name,
            value
        );

        // applying a pox lock at this point is equivalent to evaluating a transfer
        runtime_cost(
            ClarityCostFunction::StxTransfer,
            &mut global_context.cost_track,
            1,
        )?;

        match parse_pox_stacking_result(value) {
            Ok((stacker, locked_amount, unlock_height)) => {
                // in most cases, if this fails, then there's a bug in the contract (since it already does
                // the necessary checks), but with v2 introduction, that's no longer true -- if someone
                // locks on PoX v2, and then tries to lock again in PoX v1, that's not captured by the v1
                // contract.
                match StacksChainState::pox_lock_v1(
                    &mut global_context.database,
                    &stacker,
                    locked_amount,
                    unlock_height as u64,
                ) {
                    Ok(_) => {
                        if let Some(batch) = global_context.event_batches.last_mut() {
                            batch.events.push(StacksTransactionEvent::STXEvent(
                                STXEventType::STXLockEvent(STXLockEventData {
                                    locked_amount,
                                    unlock_height,
                                    locked_address: stacker,
                                }),
                            ));
                        }
                    }
                    Err(ChainstateError::DefunctPoxContract) => {
                        return Err(Error::Runtime(RuntimeErrorType::DefunctPoxContract, None))
                    }
                    Err(e) => {
                        panic!(
                            "FATAL: failed to lock {} from {} until {}: '{:?}'",
                            locked_amount, stacker, unlock_height, &e
                        );
                    }
                }

                return Ok(());
            }
            Err(_) => {
                // nothing to do -- the function failed
                return Ok(());
            }
        }
    }
    // nothing to do
    Ok(())
}

/// Handle special cases when calling into the PoX API contract
fn handle_pox_v2_api_contract_call(
    global_context: &mut GlobalContext,
    _sender_opt: Option<&PrincipalData>,
    function_name: &str,
    value: &Value,
) -> Result<()> {
    if function_name == "stack-stx" || function_name == "delegate-stack-stx" {
        debug!(
            "Handle special-case contract-call to {:?} {} (which returned {:?})",
            boot_code_id(POX_2_NAME, global_context.mainnet),
            function_name,
            value
        );
        // applying a pox lock at this point is equivalent to evaluating a transfer
        runtime_cost(
            ClarityCostFunction::StxTransfer,
            &mut global_context.cost_track,
            1,
        )?;

        match parse_pox_stacking_result(value) {
            Ok((stacker, locked_amount, unlock_height)) => {
                match StacksChainState::pox_lock_v2(
                    &mut global_context.database,
                    &stacker,
                    locked_amount,
                    unlock_height as u64,
                ) {
                    Ok(_) => {
                        if let Some(batch) = global_context.event_batches.last_mut() {
                            batch.events.push(StacksTransactionEvent::STXEvent(
                                STXEventType::STXLockEvent(STXLockEventData {
                                    locked_amount,
                                    unlock_height,
                                    locked_address: stacker,
                                }),
                            ));
                        }
                    }
                    Err(ChainstateError::DefunctPoxContract) => {
                        return Err(Error::Runtime(RuntimeErrorType::DefunctPoxContract, None))
                    }
                    Err(e) => {
                        panic!(
                            "FATAL: failed to lock {} from {} until {}: '{:?}'",
                            locked_amount, stacker, unlock_height, &e
                        );
                    }
                }

                return Ok(());
            }
            Err(_) => {
                // nothing to do -- the function failed
                return Ok(());
            }
        }
    } else if function_name == "stack-extend" || function_name == "delegate-stack-extend" {
        // applying a pox lock at this point is equivalent to evaluating a transfer
        debug!(
            "Handle special-case contract-call to {:?} {} (which returned {:?})",
            boot_code_id("pox-2", global_context.mainnet),
            function_name,
            value
        );

        runtime_cost(
            ClarityCostFunction::StxTransfer,
            &mut global_context.cost_track,
            1,
        )?;

        if let Ok((stacker, unlock_height)) = parse_pox_extend_result(value) {
            match StacksChainState::pox_lock_extend_v2(
                &mut global_context.database,
                &stacker,
                unlock_height as u64,
            ) {
                Ok(locked_amount) => {
                    if let Some(batch) = global_context.event_batches.last_mut() {
                        batch.events.push(StacksTransactionEvent::STXEvent(
                            STXEventType::STXLockEvent(STXLockEventData {
                                locked_amount,
                                unlock_height,
                                locked_address: stacker,
                            }),
                        ));
                    }
                }
                Err(ChainstateError::DefunctPoxContract) => {
                    return Err(Error::Runtime(RuntimeErrorType::DefunctPoxContract, None))
                }
                Err(e) => {
                    panic!(
                        "FATAL: failed to extend lock from {} until {}: '{:?}'",
                        stacker, unlock_height, &e
                    );
                }
            }

            return Ok(());
        } else {
            // nothing to do -- the function failed
            return Ok(());
        }
    }
    // nothing to do
    Ok(())
}

/// Handle special cases of contract-calls -- namely, those into PoX that should lock up STX
pub fn handle_contract_call_special_cases(
    global_context: &mut GlobalContext,
    sender: Option<&PrincipalData>,
    _sponsor: Option<&PrincipalData>,
    contract_id: &QualifiedContractIdentifier,
    function_name: &str,
    result: &Value,
) -> Result<()> {
    if *contract_id == boot_code_id(POX_1_NAME, global_context.mainnet) {
        if global_context.database.get_v1_unlock_height()
            <= global_context.database.get_current_burnchain_block_height()
        {
            warn!("PoX-1 Lock attempted on an account after v1 unlock height";
                  "v1_unlock_ht" => global_context.database.get_v1_unlock_height(),
                  "current_burn_ht" => global_context.database.get_current_burnchain_block_height(),
            );
            return Err(Error::Runtime(RuntimeErrorType::DefunctPoxContract, None));
        }
        return handle_pox_v1_api_contract_call(global_context, sender, function_name, result);
    } else if *contract_id == boot_code_id(POX_2_NAME, global_context.mainnet) {
        return handle_pox_v2_api_contract_call(global_context, sender, function_name, result);
    }

    // TODO: insert more special cases here, as needed
    Ok(())
}
