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

use super::{
    check_argument_count, check_arguments_at_least, no_type, TypeChecker, TypeResult, TypingContext,
};
use std::convert::TryFrom;
use vm::analysis::errors::{CheckError, CheckErrors, CheckResult};
use vm::errors::{Error as InterpError, RuntimeErrorType};
use vm::functions::{handle_binding_list, NativeFunctions};
use vm::types::{
    BlockInfoProperty, FixedFunction, FunctionArg, FunctionSignature, FunctionType, PrincipalData,
    TupleTypeSignature, TypeSignature, Value, BUFF_20, BUFF_32, BUFF_33, BUFF_64, BUFF_65,
    MAX_VALUE_SIZE,
};
use vm::{ClarityName, SymbolicExpression, SymbolicExpressionType};

use vm::costs::cost_functions::ClarityCostFunction;
use vm::costs::{analysis_typecheck_cost, cost_functions, runtime_cost, CostOverflowingMath};

mod assets;
mod maps;
mod options;
mod sequences;

pub enum TypedNativeFunction {
    Special(SpecialNativeFunction),
    Simple(SimpleNativeFunction),
}

pub struct SpecialNativeFunction(
    &'static dyn Fn(&mut TypeChecker, &[SymbolicExpression], &TypingContext) -> TypeResult,
);
pub struct SimpleNativeFunction(pub FunctionType);

fn check_special_list_cons(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    let typed_args = checker.type_check_all(args, context)?;
    for type_arg in typed_args.iter() {
        runtime_cost(
            ClarityCostFunction::AnalysisListItemsCheck,
            checker,
            type_arg.type_size()?,
        )?;
    }
    TypeSignature::parent_list_type(&typed_args)
        .map_err(|x| x.into())
        .map(TypeSignature::from)
}

fn check_special_print(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(1, args)?;
    checker.type_check(&args[0], context)
}

fn check_special_as_contract(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(1, args)?;
    checker.type_check(&args[0], context)
}

fn check_special_at_block(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(2, args)?;
    checker.type_check_expects(&args[0], context, &BUFF_32)?;
    checker.type_check(&args[1], context)
}

fn check_special_begin(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_arguments_at_least(1, args)?;

    checker.type_check_consecutive_statements(args, context)
}

fn inner_handle_tuple_get(
    tuple_type_sig: &TupleTypeSignature,
    field_to_get: &str,
    checker: &mut TypeChecker,
) -> TypeResult {
    runtime_cost(
        ClarityCostFunction::AnalysisCheckTupleGet,
        checker,
        tuple_type_sig.len(),
    )?;

    let return_type = tuple_type_sig
        .field_type(field_to_get)
        .ok_or(CheckError::new(CheckErrors::NoSuchTupleField(
            field_to_get.to_string(),
            tuple_type_sig.clone(),
        )))?
        .clone();
    Ok(return_type)
}

fn check_special_get(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(2, args)?;

    let field_to_get = args[0].match_atom().ok_or(CheckErrors::BadTupleFieldName)?;

    let argument_type = checker.type_check(&args[1], context)?;

    if let TypeSignature::TupleType(tuple_type_sig) = argument_type {
        inner_handle_tuple_get(&tuple_type_sig, field_to_get, checker)
    } else if let TypeSignature::OptionalType(value_type_sig) = argument_type {
        if let TypeSignature::TupleType(tuple_type_sig) = *value_type_sig {
            let inner_type = inner_handle_tuple_get(&tuple_type_sig, field_to_get, checker)?;
            let option_type = TypeSignature::new_option(inner_type)?;
            Ok(option_type)
        } else {
            Err(CheckErrors::ExpectedTuple(*value_type_sig).into())
        }
    } else {
        Err(CheckErrors::ExpectedTuple(argument_type).into())
    }
}

fn check_special_merge(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(2, args)?;

    let res = checker.type_check(&args[0], context)?;
    let mut base = match res {
        TypeSignature::TupleType(tuple_sig) => Ok(tuple_sig),
        _ => Err(CheckErrors::ExpectedTuple(res.clone())),
    }?;

    let res = checker.type_check(&args[1], context)?;
    let mut update = match res {
        TypeSignature::TupleType(tuple_sig) => Ok(tuple_sig),
        _ => Err(CheckErrors::ExpectedTuple(res.clone())),
    }?;
    runtime_cost(
        ClarityCostFunction::AnalysisCheckTupleMerge,
        checker,
        update.len(),
    )?;

    base.shallow_merge(&mut update);
    Ok(TypeSignature::TupleType(base))
}

pub fn check_special_tuple_cons(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_arguments_at_least(1, args)?;

    let mut tuple_type_data = Vec::new();

    runtime_cost(
        ClarityCostFunction::AnalysisCheckTupleCons,
        checker,
        args.len(),
    )?;

    handle_binding_list(args, |var_name, var_sexp| {
        checker.type_check(var_sexp, context).and_then(|var_type| {
            runtime_cost(
                ClarityCostFunction::AnalysisTupleItemsCheck,
                checker,
                var_type.type_size()?,
            )?;
            tuple_type_data.push((var_name.clone(), var_type));
            Ok(())
        })
    })?;

    let tuple_signature = TupleTypeSignature::try_from(tuple_type_data)
        .map_err(|_| CheckErrors::BadTupleConstruction)?;

    Ok(TypeSignature::TupleType(tuple_signature))
}

fn check_special_let(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_arguments_at_least(2, args)?;

    let binding_list = args[0]
        .match_list()
        .ok_or(CheckError::new(CheckErrors::BadLetSyntax))?;

    let mut out_context = context.extend()?;

    runtime_cost(ClarityCostFunction::AnalysisCheckLet, checker, args.len())?;

    handle_binding_list(binding_list, |var_name, var_sexp| {
        checker.contract_context.check_name_used(var_name)?;
        if out_context.lookup_variable_type(var_name).is_some() {
            return Err(CheckError::new(CheckErrors::NameAlreadyUsed(
                var_name.to_string(),
            )));
        }

        let typed_result = checker.type_check(var_sexp, &out_context)?;

        runtime_cost(
            ClarityCostFunction::AnalysisBindName,
            checker,
            typed_result.type_size()?,
        )?;
        out_context
            .variable_types
            .insert(var_name.clone(), typed_result);
        Ok(())
    })?;

    checker.type_check_consecutive_statements(&args[1..args.len()], &out_context)
}

fn check_special_fetch_var(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    _context: &TypingContext,
) -> TypeResult {
    check_argument_count(1, args)?;

    let var_name = args[0]
        .match_atom()
        .ok_or(CheckError::new(CheckErrors::BadMapName))?;

    let value_type = checker
        .contract_context
        .get_persisted_variable_type(var_name)
        .ok_or(CheckError::new(CheckErrors::NoSuchDataVariable(
            var_name.to_string(),
        )))?;

    runtime_cost(
        ClarityCostFunction::AnalysisTypeLookup,
        &mut checker.cost_track,
        value_type.type_size()?,
    )?;

    Ok(value_type.clone())
}

fn check_special_set_var(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_arguments_at_least(2, args)?;

    let var_name = args[0].match_atom().ok_or(CheckErrors::BadMapName)?;

    let value_type = checker.type_check(&args[1], context)?;

    let expected_value_type = checker
        .contract_context
        .get_persisted_variable_type(var_name)
        .ok_or(CheckErrors::NoSuchDataVariable(var_name.to_string()))?;

    runtime_cost(
        ClarityCostFunction::AnalysisTypeLookup,
        &mut checker.cost_track,
        expected_value_type.type_size()?,
    )?;
    analysis_typecheck_cost(&mut checker.cost_track, &value_type, &expected_value_type)?;

    if !expected_value_type.admits_type(&value_type) {
        return Err(CheckError::new(CheckErrors::TypeError(
            expected_value_type.clone(),
            value_type,
        )));
    } else {
        return Ok(TypeSignature::BoolType);
    }
}

fn check_special_equals(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_arguments_at_least(1, args)?;

    let mut arg_types = checker.type_check_all(args, context)?;

    let mut arg_type = arg_types[0].clone();
    for x_type in arg_types.drain(..) {
        analysis_typecheck_cost(checker, &x_type, &arg_type)?;
        arg_type = TypeSignature::least_supertype(&x_type, &arg_type)
            .map_err(|_| CheckErrors::TypeError(x_type, arg_type))?;
    }

    Ok(TypeSignature::BoolType)
}

fn check_special_if(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(3, args)?;

    checker.type_check_expects(&args[0], context, &TypeSignature::BoolType)?;

    let arg_types = checker.type_check_all(&args[1..], context)?;

    let expr1 = &arg_types[0];
    let expr2 = &arg_types[1];

    analysis_typecheck_cost(checker, expr1, expr2)?;

    TypeSignature::least_supertype(expr1, expr2)
        .map_err(|_| CheckErrors::IfArmsMustMatch(expr1.clone(), expr2.clone()).into())
}

fn check_contract_call(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_arguments_at_least(2, args)?;

    let func_name = args[1]
        .match_atom()
        .ok_or(CheckError::new(CheckErrors::ContractCallExpectName))?;
    checker.type_map.set_type(&args[1], no_type())?;

    let expected_sig = match &args[0].expr {
        SymbolicExpressionType::LiteralValue(Value::Principal(PrincipalData::Contract(
            ref contract_identifier,
        ))) => {
            // Static dispatch
            let contract_call_function = {
                if let Some(FunctionType::Fixed(function)) = checker
                    .db
                    .get_public_function_type(&contract_identifier, func_name)?
                {
                    Ok(function)
                } else if let Some(FunctionType::Fixed(function)) = checker
                    .db
                    .get_read_only_function_type(&contract_identifier, func_name)?
                {
                    Ok(function)
                } else {
                    Err(CheckError::new(CheckErrors::NoSuchPublicFunction(
                        contract_identifier.to_string(),
                        func_name.to_string(),
                    )))
                }
            }?;

            let func_signature = FunctionSignature::from(contract_call_function);

            runtime_cost(
                ClarityCostFunction::AnalysisGetFunctionEntry,
                checker,
                func_signature.total_type_size()?,
            )?;

            func_signature
        }
        SymbolicExpressionType::Atom(trait_instance) => {
            // Dynamic dispatch
            let trait_id = match context.lookup_trait_reference_type(trait_instance) {
                Some(trait_id) => trait_id,
                _ => {
                    return Err(
                        CheckErrors::TraitReferenceUnknown(trait_instance.to_string()).into(),
                    )
                }
            };

            runtime_cost(ClarityCostFunction::AnalysisLookupFunction, checker, 0)?;

            let trait_signature = checker.contract_context.get_trait(&trait_id.name).ok_or(
                CheckErrors::TraitReferenceUnknown(trait_id.name.to_string()),
            )?;
            let func_signature =
                trait_signature
                    .get(func_name)
                    .ok_or(CheckErrors::TraitMethodUnknown(
                        trait_id.name.to_string(),
                        func_name.to_string(),
                    ))?;

            runtime_cost(
                ClarityCostFunction::AnalysisLookupFunctionTypes,
                &mut checker.cost_track,
                func_signature.total_type_size()?,
            )?;

            func_signature.clone()
        }
        _ => return Err(CheckError::new(CheckErrors::ContractCallExpectName)),
    };

    check_argument_count(expected_sig.args.len(), &args[2..])?;
    for (expected_type, arg) in expected_sig.args.iter().zip(&args[2..]) {
        checker.type_check_expects(arg, context, expected_type)?;
    }

    Ok(expected_sig.returns)
}

fn check_contract_of(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(1, args)?;

    let trait_instance = match &args[0].expr {
        SymbolicExpressionType::Atom(trait_instance) => trait_instance,
        _ => return Err(CheckError::new(CheckErrors::ContractOfExpectsTrait)),
    };

    let trait_id = match context.lookup_trait_reference_type(trait_instance) {
        Some(trait_id) => trait_id,
        _ => return Err(CheckErrors::TraitReferenceUnknown(trait_instance.to_string()).into()),
    };

    runtime_cost(ClarityCostFunction::ContractOf, checker, 1)?;

    checker
        .contract_context
        .get_trait(&trait_id.name)
        .ok_or_else(|| CheckErrors::TraitReferenceUnknown(trait_id.name.to_string()))?;

    Ok(TypeSignature::PrincipalType)
}

fn check_principal_of(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(1, args)?;
    checker.type_check_expects(&args[0], context, &BUFF_33)?;
    Ok(TypeSignature::new_response(TypeSignature::PrincipalType, TypeSignature::UIntType).unwrap())
}

fn check_secp256k1_recover(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(2, args)?;
    checker.type_check_expects(&args[0], context, &BUFF_32)?;
    checker.type_check_expects(&args[1], context, &BUFF_65)?;
    Ok(TypeSignature::new_response(BUFF_33.clone(), TypeSignature::UIntType).unwrap())
}

fn check_secp256k1_verify(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_argument_count(3, args)?;
    checker.type_check_expects(&args[0], context, &BUFF_32)?;
    checker.type_check_expects(&args[1], context, &BUFF_65)?;
    checker.type_check_expects(&args[2], context, &BUFF_33)?;
    Ok(TypeSignature::BoolType)
}

fn check_get_block_info(
    checker: &mut TypeChecker,
    args: &[SymbolicExpression],
    context: &TypingContext,
) -> TypeResult {
    check_arguments_at_least(2, args)?;

    let block_info_prop_str = args[0]
        .match_atom()
        .ok_or(CheckError::new(CheckErrors::GetBlockInfoExpectPropertyName))?;

    let block_info_prop =
        BlockInfoProperty::lookup_by_name(block_info_prop_str).ok_or(CheckError::new(
            CheckErrors::NoSuchBlockInfoProperty(block_info_prop_str.to_string()),
        ))?;

    checker.type_check_expects(&args[1], &context, &TypeSignature::UIntType)?;

    Ok(TypeSignature::new_option(block_info_prop.type_result())?)
}

impl TypedNativeFunction {
    pub fn type_check_appliction(
        &self,
        checker: &mut TypeChecker,
        args: &[SymbolicExpression],
        context: &TypingContext,
    ) -> TypeResult {
        use self::TypedNativeFunction::{Simple, Special};
        match self {
            Special(SpecialNativeFunction(check)) => check(checker, args, context),
            Simple(SimpleNativeFunction(function_type)) => {
                checker.type_check_function_type(function_type, args, context)
            }
        }
    }

    pub fn type_native_function(function: &NativeFunctions) -> TypedNativeFunction {
        use self::TypedNativeFunction::{Simple, Special};
        use vm::functions::NativeFunctions::*;
        match function {
            Add | Subtract | Divide | Multiply => {
                Simple(SimpleNativeFunction(FunctionType::ArithmeticVariadic))
            }
            CmpGeq | CmpLeq | CmpLess | CmpGreater => {
                Simple(SimpleNativeFunction(FunctionType::ArithmeticComparison))
            }
            Sqrti | Log2 => Simple(SimpleNativeFunction(FunctionType::ArithmeticUnary)),
            Modulo | Power | BitwiseXOR => {
                Simple(SimpleNativeFunction(FunctionType::ArithmeticBinary))
            }
            And | Or => Simple(SimpleNativeFunction(FunctionType::Variadic(
                TypeSignature::BoolType,
                TypeSignature::BoolType,
            ))),
            ToUInt => Simple(SimpleNativeFunction(FunctionType::Fixed(FixedFunction {
                args: vec![FunctionArg::new(
                    TypeSignature::IntType,
                    ClarityName::try_from("value".to_owned())
                        .expect("FAIL: ClarityName failed to accept default arg name"),
                )],
                returns: TypeSignature::UIntType,
            }))),
            ToInt => Simple(SimpleNativeFunction(FunctionType::Fixed(FixedFunction {
                args: vec![FunctionArg::new(
                    TypeSignature::UIntType,
                    ClarityName::try_from("value".to_owned())
                        .expect("FAIL: ClarityName failed to accept default arg name"),
                )],
                returns: TypeSignature::IntType,
            }))),
            Not => Simple(SimpleNativeFunction(FunctionType::Fixed(FixedFunction {
                args: vec![FunctionArg::new(
                    TypeSignature::BoolType,
                    ClarityName::try_from("value".to_owned())
                        .expect("FAIL: ClarityName failed to accept default arg name"),
                )],
                returns: TypeSignature::BoolType,
            }))),
            Hash160 => Simple(SimpleNativeFunction(FunctionType::UnionArgs(
                vec![
                    TypeSignature::max_buffer(),
                    TypeSignature::UIntType,
                    TypeSignature::IntType,
                ],
                BUFF_20.clone(),
            ))),
            Sha256 => Simple(SimpleNativeFunction(FunctionType::UnionArgs(
                vec![
                    TypeSignature::max_buffer(),
                    TypeSignature::UIntType,
                    TypeSignature::IntType,
                ],
                BUFF_32.clone(),
            ))),
            Sha512Trunc256 => Simple(SimpleNativeFunction(FunctionType::UnionArgs(
                vec![
                    TypeSignature::max_buffer(),
                    TypeSignature::UIntType,
                    TypeSignature::IntType,
                ],
                BUFF_32.clone(),
            ))),
            Sha512 => Simple(SimpleNativeFunction(FunctionType::UnionArgs(
                vec![
                    TypeSignature::max_buffer(),
                    TypeSignature::UIntType,
                    TypeSignature::IntType,
                ],
                BUFF_64.clone(),
            ))),
            Keccak256 => Simple(SimpleNativeFunction(FunctionType::UnionArgs(
                vec![
                    TypeSignature::max_buffer(),
                    TypeSignature::UIntType,
                    TypeSignature::IntType,
                ],
                BUFF_32.clone(),
            ))),
            Secp256k1Recover => Special(SpecialNativeFunction(&check_secp256k1_recover)),
            Secp256k1Verify => Special(SpecialNativeFunction(&check_secp256k1_verify)),
            GetStxBalance => Simple(SimpleNativeFunction(FunctionType::Fixed(FixedFunction {
                args: vec![FunctionArg::new(
                    TypeSignature::PrincipalType,
                    ClarityName::try_from("owner".to_owned())
                        .expect("FAIL: ClarityName failed to accept default arg name"),
                )],
                returns: TypeSignature::UIntType,
            }))),
            StxTransfer => Simple(SimpleNativeFunction(FunctionType::Fixed(FixedFunction {
                args: vec![
                    FunctionArg::new(
                        TypeSignature::UIntType,
                        ClarityName::try_from("amount".to_owned())
                            .expect("FAIL: ClarityName failed to accept default arg name"),
                    ),
                    FunctionArg::new(
                        TypeSignature::PrincipalType,
                        ClarityName::try_from("sender".to_owned())
                            .expect("FAIL: ClarityName failed to accept default arg name"),
                    ),
                    FunctionArg::new(
                        TypeSignature::PrincipalType,
                        ClarityName::try_from("recipient".to_owned())
                            .expect("FAIL: ClarityName failed to accept default arg name"),
                    ),
                ],
                returns: TypeSignature::new_response(
                    TypeSignature::BoolType,
                    TypeSignature::UIntType,
                )
                .unwrap(),
            }))),
            StxBurn => Simple(SimpleNativeFunction(FunctionType::Fixed(FixedFunction {
                args: vec![
                    FunctionArg::new(
                        TypeSignature::UIntType,
                        ClarityName::try_from("amount".to_owned())
                            .expect("FAIL: ClarityName failed to accept default arg name"),
                    ),
                    FunctionArg::new(
                        TypeSignature::PrincipalType,
                        ClarityName::try_from("sender".to_owned())
                            .expect("FAIL: ClarityName failed to accept default arg name"),
                    ),
                ],
                returns: TypeSignature::new_response(
                    TypeSignature::BoolType,
                    TypeSignature::UIntType,
                )
                .unwrap(),
            }))),
            GetTokenBalance => Special(SpecialNativeFunction(&assets::check_special_get_balance)),
            GetAssetOwner => Special(SpecialNativeFunction(&assets::check_special_get_owner)),
            TransferToken => Special(SpecialNativeFunction(&assets::check_special_transfer_token)),
            TransferAsset => Special(SpecialNativeFunction(&assets::check_special_transfer_asset)),
            MintAsset => Special(SpecialNativeFunction(&assets::check_special_mint_asset)),
            MintToken => Special(SpecialNativeFunction(&assets::check_special_mint_token)),
            BurnAsset => Special(SpecialNativeFunction(&assets::check_special_burn_asset)),
            BurnToken => Special(SpecialNativeFunction(&assets::check_special_burn_token)),
            GetTokenSupply => Special(SpecialNativeFunction(
                &assets::check_special_get_token_supply,
            )),
            Equals => Special(SpecialNativeFunction(&check_special_equals)),
            If => Special(SpecialNativeFunction(&check_special_if)),
            Let => Special(SpecialNativeFunction(&check_special_let)),
            FetchVar => Special(SpecialNativeFunction(&check_special_fetch_var)),
            SetVar => Special(SpecialNativeFunction(&check_special_set_var)),
            Map => Special(SpecialNativeFunction(&sequences::check_special_map)),
            Filter => Special(SpecialNativeFunction(&sequences::check_special_filter)),
            Fold => Special(SpecialNativeFunction(&sequences::check_special_fold)),
            Append => Special(SpecialNativeFunction(&sequences::check_special_append)),
            Concat => Special(SpecialNativeFunction(&sequences::check_special_concat)),
            AsMaxLen => Special(SpecialNativeFunction(&sequences::check_special_as_max_len)),
            Len => Special(SpecialNativeFunction(&sequences::check_special_len)),
            ElementAt => Special(SpecialNativeFunction(&sequences::check_special_element_at)),
            IndexOf => Special(SpecialNativeFunction(&sequences::check_special_index_of)),
            ListCons => Special(SpecialNativeFunction(&check_special_list_cons)),
            FetchEntry => Special(SpecialNativeFunction(&maps::check_special_fetch_entry)),
            SetEntry => Special(SpecialNativeFunction(&maps::check_special_set_entry)),
            InsertEntry => Special(SpecialNativeFunction(&maps::check_special_insert_entry)),
            DeleteEntry => Special(SpecialNativeFunction(&maps::check_special_delete_entry)),
            TupleCons => Special(SpecialNativeFunction(&check_special_tuple_cons)),
            TupleGet => Special(SpecialNativeFunction(&check_special_get)),
            TupleMerge => Special(SpecialNativeFunction(&check_special_merge)),
            Begin => Special(SpecialNativeFunction(&check_special_begin)),
            Print => Special(SpecialNativeFunction(&check_special_print)),
            AsContract => Special(SpecialNativeFunction(&check_special_as_contract)),
            ContractCall => Special(SpecialNativeFunction(&check_contract_call)),
            ContractOf => Special(SpecialNativeFunction(&check_contract_of)),
            PrincipalOf => Special(SpecialNativeFunction(&check_principal_of)),
            GetBlockInfo => Special(SpecialNativeFunction(&check_get_block_info)),
            ConsSome => Special(SpecialNativeFunction(&options::check_special_some)),
            ConsOkay => Special(SpecialNativeFunction(&options::check_special_okay)),
            ConsError => Special(SpecialNativeFunction(&options::check_special_error)),
            DefaultTo => Special(SpecialNativeFunction(&options::check_special_default_to)),
            Asserts => Special(SpecialNativeFunction(&options::check_special_asserts)),
            UnwrapRet => Special(SpecialNativeFunction(&options::check_special_unwrap_or_ret)),
            UnwrapErrRet => Special(SpecialNativeFunction(
                &options::check_special_unwrap_err_or_ret,
            )),
            Unwrap => Special(SpecialNativeFunction(&options::check_special_unwrap)),
            UnwrapErr => Special(SpecialNativeFunction(&options::check_special_unwrap_err)),
            TryRet => Special(SpecialNativeFunction(&options::check_special_try_ret)),
            Match => Special(SpecialNativeFunction(&options::check_special_match)),
            IsOkay => Special(SpecialNativeFunction(&options::check_special_is_response)),
            IsErr => Special(SpecialNativeFunction(&options::check_special_is_response)),
            IsNone => Special(SpecialNativeFunction(&options::check_special_is_optional)),
            IsSome => Special(SpecialNativeFunction(&options::check_special_is_optional)),
            AtBlock => Special(SpecialNativeFunction(&check_special_at_block)),
        }
    }
}
