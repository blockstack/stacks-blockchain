use std::convert::{TryFrom, TryInto};

use vm::functions::tuples;
use vm::functions::tuples::TupleDefinitionType::{Implicit, Explicit};

use vm::types::{Value, OptionalData, BuffData, PrincipalData, BlockInfoProperty, TypeSignature, BUFF_32};
use vm::representations::{SymbolicExpression, SymbolicExpressionType};
use vm::errors::{CheckErrors, InterpreterError, RuntimeErrorType, InterpreterResult as Result,
                 check_argument_count, check_arguments_at_least};
use vm::{eval, LocalContext, Environment};
use vm::callables::{DefineType};
use chainstate::burn::{BlockHeaderHash};

pub fn special_contract_call(args: &[SymbolicExpression],
                             env: &mut Environment,
                             context: &LocalContext) -> Result<Value> {
    check_arguments_at_least(2, args)?;

    let function_name = args[1].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;
    let rest_args: Vec<_> = {
        let rest_args = &args[2..];
        let rest_args: Result<Vec<_>> = rest_args.iter().map(|x| { eval(x, env, context) }).collect();
        let mut rest_args = rest_args?;
        rest_args.drain(..).map(|x| { SymbolicExpression::atom_value(x) }).collect()
    };

    let (contract_identifier, type_returns_constraint) = match &args[0].expr {
        SymbolicExpressionType::LiteralValue(Value::Principal(PrincipalData::Contract(ref contract_identifier))) => {
            // Static dispatch
            (contract_identifier, None)
        },
        SymbolicExpressionType::Atom(contract_ref) => {
            // Dynamic dispatch
            match context.callable_contracts.get(contract_ref) {
                Some((ref contract_identifier, trait_identifier)) => {
                    // Ensure that contract-call is used for inter-contract calls only 
                    if *contract_identifier == env.contract_context.contract_identifier {
                        return Err(CheckErrors::CircularReference(vec![contract_identifier.name.to_string()]).into());
                    }
                    
                    let contract_to_check = env.global_context.database.get_contract(contract_identifier)
                        .map_err(|_e| CheckErrors::NoSuchContract(contract_identifier.to_string()))?;
                    let contract_context_to_check = contract_to_check.contract_context;

                    // Attempt to short circuit the dynamic dispatch checks:
                    // If the contract is explicitely implementing the trait with `impl-trait`,
                    // then we can simply rely on the analysis performed at publish time.
                    if contract_context_to_check.is_explicitly_implementing_trait(&trait_identifier) {
                        (contract_identifier, None)
                    } else {
                        let trait_name = trait_identifier.name.to_string();

                        // Retrieve, from the trait definition, the expected method signature
                        let contract_defining_trait = env.global_context.database.get_contract(&trait_identifier.contract_identifier)
                            .map_err(|_e| CheckErrors::NoSuchContract(trait_identifier.contract_identifier.to_string()))?;
                        let contract_context_defining_trait = contract_defining_trait.contract_context;

                        // Retrieve the function that will be invoked
                        let function_to_check = contract_context_to_check.lookup_function(function_name)
                            .ok_or(CheckErrors::BadTraitImplementation(trait_name.clone(), function_name.to_string()))?;
                        
                        // Check read/write compatibility
                        if env.global_context.is_read_only() {
                            return Err(CheckErrors::TraitBasedContractCallInReadOnly.into());
                        }
                        
                        // Check visibility
                        if function_to_check.define_type == DefineType::Private {
                            return Err(CheckErrors::NoSuchPublicFunction(contract_identifier.to_string(), function_name.to_string()).into());
                        }

                        function_to_check.check_trait_expectations(&contract_context_defining_trait, &trait_identifier)?;

                        // Retrieve the expected method signature
                        let constraining_trait = contract_context_defining_trait.lookup_trait_definition(&trait_name)
                            .ok_or(CheckErrors::TraitReferenceUnknown(trait_name.clone()))?;
                        let expected_sig = constraining_trait.get(function_name)
                            .ok_or(CheckErrors::TraitMethodUnknown(trait_name.clone(), function_name.to_string()))?;
                        (contract_identifier, Some(expected_sig.returns.clone()))
                    }
                },
                _ => return Err(CheckErrors::ContractCallExpectName.into())
            }
        },
        _ => return Err(CheckErrors::ContractCallExpectName.into())
    };

    let contract_principal = Value::Principal(PrincipalData::Contract(
        env.contract_context.contract_identifier.clone()));
    let mut nested_env = env.nest_with_caller(contract_principal);

    let result = nested_env.execute_contract(&contract_identifier, 
                                             function_name, 
                                             &rest_args)?;
    
    // Ensure that the expected type from the trait spec admits
    // the type of the value returned by the dynamic dispatch.
    if let Some(returns_type_signature) = type_returns_constraint {
        let actual_returns = TypeSignature::type_of(&result);
        if !returns_type_signature.admits_type(&actual_returns) {
            return Err(CheckErrors::ReturnTypesMustMatch(returns_type_signature.clone(), actual_returns.clone()).into())
        }
    }
    Ok(result)
}

pub fn special_fetch_variable(args: &[SymbolicExpression],
                              env: &mut Environment,
                              _context: &LocalContext) -> Result<Value> {
    check_argument_count(1, args)?;

    let var_name = args[0].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    env.global_context.database.lookup_variable(&env.contract_context.contract_identifier, var_name)
}

pub fn special_set_variable(args: &[SymbolicExpression],
                            env: &mut Environment,
                            context: &LocalContext) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into())
    }

    check_argument_count(2, args)?;

    let value = eval(&args[1], env, &context)?;

    let var_name = args[0].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    env.global_context.database.set_variable(&env.contract_context.contract_identifier, var_name, value)
}

pub fn special_fetch_entry(args: &[SymbolicExpression],
                           env: &mut Environment,
                           context: &LocalContext) -> Result<Value> {
    check_argument_count(2, args)?;

    let map_name = args[0].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    let key = match tuples::get_definition_type_of_tuple_argument(&args[1]) {
        Implicit(ref expr) => tuples::tuple_cons(expr, env, context)?,
        Explicit => eval(&args[1], env, &context)?
    };

    env.global_context.database.fetch_entry(&env.contract_context.contract_identifier, map_name, &key)
}

pub fn special_at_block(args: &[SymbolicExpression],
                        env: &mut Environment,
                        context: &LocalContext) -> Result<Value> {
    check_argument_count(2, args)?;

    let bhh = match eval(&args[0], env, &context)? {
        Value::Buffer(BuffData { data }) => {
            if data.len() != 32 {
                return Err(RuntimeErrorType::BadBlockHash(data).into())
            } else {
                BlockHeaderHash::from(data.as_slice())
            }
        },
        x => return Err(CheckErrors::TypeValueError(BUFF_32.clone(), x).into())
    };

    env.evaluate_at_block(bhh, &args[1], context)
}

pub fn special_fetch_contract_entry(args: &[SymbolicExpression],
                                    env: &mut Environment,
                                    context: &LocalContext) -> Result<Value> {
    check_argument_count(3, args)?;

    let contract_identifier = match args[0].expr {
        SymbolicExpressionType::LiteralValue(Value::Principal(PrincipalData::Contract(ref contract_identifier))) => contract_identifier,
        _ => return Err(CheckErrors::ContractCallExpectName.into())
    };

    let map_name = args[1].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    let key = match tuples::get_definition_type_of_tuple_argument(&args[2]) {
        Implicit(ref expr) => tuples::tuple_cons(expr, env, context)?,
        Explicit => eval(&args[2], env, &context)?
    };

    env.global_context.database.fetch_entry(&contract_identifier, map_name, &key)
}

pub fn special_set_entry(args: &[SymbolicExpression],
                         env: &mut Environment,
                         context: &LocalContext) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into())
    }

    check_argument_count(3, args)?;

    let key = match tuples::get_definition_type_of_tuple_argument(&args[1]) {
        Implicit(ref expr) => tuples::tuple_cons(expr, env, context)?,
        Explicit => eval(&args[1], env, &context)?
    };

    let value = match tuples::get_definition_type_of_tuple_argument(&args[2]) {
        Implicit(ref expr) => tuples::tuple_cons(expr, env, context)?,
        Explicit => eval(&args[2], env, &context)?
    };

    let map_name = args[0].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    env.global_context.database.set_entry(&env.contract_context.contract_identifier, map_name, key, value)
}

pub fn special_insert_entry(args: &[SymbolicExpression],
                            env: &mut Environment,
                            context: &LocalContext) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into())
    }

    check_argument_count(3, args)?;
    
    let key = match tuples::get_definition_type_of_tuple_argument(&args[1]) {
        Implicit(ref expr) => tuples::tuple_cons(expr, env, context)?,
        Explicit => eval(&args[1], env, &context)?
    };

    let value = match tuples::get_definition_type_of_tuple_argument(&args[2]) {
        Implicit(ref expr) => tuples::tuple_cons(expr, env, context)?,
        Explicit => eval(&args[2], env, &context)?
    };

    let map_name = args[0].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    env.global_context.database.insert_entry(&env.contract_context.contract_identifier, map_name, key, value)
}

pub fn special_delete_entry(args: &[SymbolicExpression],
                            env: &mut Environment,
                            context: &LocalContext) -> Result<Value> {
    if env.global_context.is_read_only() {
        return Err(CheckErrors::WriteAttemptedInReadOnly.into())
    }
 
    check_argument_count(2, args)?;

    let key = match tuples::get_definition_type_of_tuple_argument(&args[1]) {
        Implicit(ref expr) => tuples::tuple_cons(expr, env, context)?,
        Explicit => eval(&args[1], env, &context)?
    };

    let map_name = args[0].match_atom()
        .ok_or(CheckErrors::ExpectedName)?;

    env.global_context.database.delete_entry(&env.contract_context.contract_identifier, map_name, &key)
}

pub fn special_get_block_info(args: &[SymbolicExpression], 
                              env: &mut Environment, 
                              context: &LocalContext) -> Result<Value> {

    // (get-block-info? property-name block-height-int)

    check_argument_count(2, args)?;

    // Handle the block property name input arg.
    let property_name = args[0].match_atom()
        .ok_or(CheckErrors::GetBlockInfoExpectPropertyName)?;

    let block_info_prop = BlockInfoProperty::lookup_by_name(property_name)
        .ok_or(CheckErrors::GetBlockInfoExpectPropertyName)?;

    // Handle the block-height input arg clause.
    let height_eval = eval(&args[1], env, context)?;
    let height_value = match height_eval {
        Value::UInt(result) => Ok(result),
        x => Err(CheckErrors::TypeValueError(TypeSignature::UIntType, x))
    }?;

    let height_value = match u32::try_from(height_value) {
        Ok(result) => result,
        _ => return Ok(Value::none())
    };

    let current_block_height = env.global_context.database.get_current_block_height();
    if height_value >= current_block_height {
        return Ok(Value::none())
    }

    let result = match block_info_prop {
        BlockInfoProperty::Time => {
            let block_time = env.global_context.database.get_block_time(height_value);
            Value::UInt(block_time as u128)
        },
        BlockInfoProperty::VrfSeed => {
            let vrf_seed = env.global_context.database.get_block_vrf_seed(height_value);
            Value::Buffer(BuffData { data: vrf_seed.as_bytes().to_vec() })
        },
        BlockInfoProperty::HeaderHash => {
            let header_hash = env.global_context.database.get_block_header_hash(height_value);
            Value::Buffer(BuffData { data: header_hash.as_bytes().to_vec() })
        },
        BlockInfoProperty::BurnchainHeaderHash => {
            let burnchain_header_hash = env.global_context.database.get_burnchain_block_header_hash(height_value);
            Value::Buffer(BuffData { data: burnchain_header_hash.as_bytes().to_vec() })
        },
        BlockInfoProperty::IdentityHeaderHash => {
            let id_header_hash = env.global_context.database.get_index_block_header_hash(height_value);
            Value::Buffer(BuffData { data: id_header_hash.as_bytes().to_vec() })            
        },
        BlockInfoProperty::MinerAddress => {
            let miner_address = env.global_context.database.get_miner_address(height_value);
            Value::from(miner_address)
        },
    };
    
    Ok(Value::some(result))
}
