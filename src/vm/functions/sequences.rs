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
use vm::costs::{cost_functions, runtime_cost, CostOverflowingMath};
use vm::errors::{
    check_argument_count, check_arguments_at_least, CheckErrors, InterpreterResult as Result,
    RuntimeErrorType,
};
use vm::representations::{SymbolicExpression, SymbolicExpressionType};
use vm::types::{
    signatures::ListTypeData, CharType, ListData, SequenceData, TypeSignature,
    TypeSignature::BoolType, Value,
};
use vm::{apply, eval, lookup_function, CallableType, Environment, LocalContext};

pub fn list_cons(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    let eval_tried: Result<Vec<Value>> = args.iter().map(|x| eval(x, env, context)).collect();
    let args = eval_tried?;

    let mut arg_size = 0;
    for a in args.iter() {
        arg_size = arg_size.cost_overflow_add(a.size().into())?;
    }

    runtime_cost(ClarityCostFunction::ListCons, env, arg_size)?;

    Value::list_from(args)
}

pub fn special_filter(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;

    runtime_cost(ClarityCostFunction::Filter, env, 0)?;

    let function_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let mut sequence = eval(&args[1], env, context)?;
    let function = lookup_function(&function_name, env)?;

    match sequence {
        Value::Sequence(ref mut sequence_data) => {
            sequence_data.filter(&mut |atom_value: SymbolicExpression| {
                let argument = [atom_value];
                let filter_eval = apply(&function, &argument, env, context)?;
                if let Value::Bool(include) = filter_eval {
                    return Ok(include);
                } else {
                    return Err(CheckErrors::TypeValueError(BoolType, filter_eval).into());
                }
            })?;
        }
        _ => return Err(CheckErrors::ExpectedSequence(TypeSignature::type_of(&sequence)).into()),
    };
    Ok(sequence)
}

pub fn special_fold(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(3, args)?;

    runtime_cost(ClarityCostFunction::Fold, env, 0)?;

    let function_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;

    let function = lookup_function(&function_name, env)?;
    let mut sequence = eval(&args[1], env, context)?;
    let initial = eval(&args[2], env, context)?;

    match sequence {
        Value::Sequence(ref mut sequence_data) => {
            sequence_data
                .atom_values()
                .into_iter()
                .try_fold(initial, |acc, x| {
                    apply(
                        &function,
                        &[x, SymbolicExpression::atom_value(acc)],
                        env,
                        context,
                    )
                })
        }
        _ => Err(CheckErrors::ExpectedSequence(TypeSignature::type_of(&sequence)).into()),
    }
}

pub fn special_map(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_arguments_at_least(2, args)?;

    runtime_cost(ClarityCostFunction::Map, env, args.len())?;

    let function_name = args[0].match_atom().ok_or(CheckErrors::ExpectedName)?;
    let function = lookup_function(&function_name, env)?;

    // Let's consider a function f (f a b c ...)
    // We will first re-arrange our sequences [a0, a1, ...] [b0, b1, ...] [c0, c1, ...] ...
    // To get something like: [a0, b0, c0, ...] [a1, b1, c1, ...]
    let mut mapped_func_args = vec![];
    let mut min_args_len = usize::MAX;
    for map_arg in args[1..].iter() {
        let mut sequence = eval(map_arg, env, context)?;
        match sequence {
            Value::Sequence(ref mut sequence_data) => {
                min_args_len = min_args_len.min(sequence_data.len());
                for (apply_index, value) in sequence_data.atom_values().into_iter().enumerate() {
                    if apply_index > min_args_len {
                        break;
                    }
                    if apply_index >= mapped_func_args.len() {
                        mapped_func_args.push(vec![value]);
                    } else {
                        mapped_func_args[apply_index].push(value);
                    }
                }
            }
            _ => {
                return Err(CheckErrors::ExpectedSequence(TypeSignature::type_of(&sequence)).into())
            }
        }
    }

    // We can now apply the map
    let mut mapped_results = vec![];
    let mut previous_len = None;
    for arguments in mapped_func_args.iter() {
        // Stop iterating when we are done with the shortest sequence
        if let Some(previous_len) = previous_len {
            if previous_len != arguments.len() {
                break;
            }
        } else {
            previous_len = Some(arguments.len());
        }
        let res = apply(&function, &arguments, env, context)?;
        mapped_results.push(res);
    }

    Value::list_from(mapped_results)
}

pub fn special_append(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;

    let sequence = eval(&args[0], env, context)?;
    match sequence {
        Value::Sequence(SequenceData::List(list)) => {
            let element = eval(&args[1], env, context)?;
            let ListData {
                mut data,
                type_signature,
            } = list;
            let (entry_type, size) = type_signature.destruct();
            let element_type = TypeSignature::type_of(&element);
            runtime_cost(
                ClarityCostFunction::Append,
                env,
                u64::from(cmp::max(entry_type.size(), element_type.size())),
            )?;
            if entry_type.is_no_type() {
                assert_eq!(size, 0);
                return Value::list_from(vec![element]);
            }
            if let Ok(next_entry_type) = TypeSignature::least_supertype(&entry_type, &element_type)
            {
                let next_type_signature = ListTypeData::new_list(next_entry_type, size + 1)?;
                data.push(element);
                Ok(Value::Sequence(SequenceData::List(ListData {
                    type_signature: next_type_signature,
                    data,
                })))
            } else {
                Err(CheckErrors::TypeValueError(entry_type, element).into())
            }
        }
        _ => Err(CheckErrors::ExpectedListApplication.into()),
    }
}

pub fn special_concat(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;

    let mut wrapped_seq = eval(&args[0], env, context)?;
    let mut other_wrapped_seq = eval(&args[1], env, context)?;

    runtime_cost(
        ClarityCostFunction::Concat,
        env,
        u64::from(wrapped_seq.size()).cost_overflow_add(u64::from(other_wrapped_seq.size()))?,
    )?;

    match (&mut wrapped_seq, &mut other_wrapped_seq) {
        (Value::Sequence(ref mut seq), Value::Sequence(ref mut other_seq)) => seq.append(other_seq),
        _ => Err(RuntimeErrorType::BadTypeConstruction.into()),
    }?;

    Ok(wrapped_seq)
}

pub fn special_as_max_len(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(2, args)?;

    let mut sequence = eval(&args[0], env, context)?;

    runtime_cost(ClarityCostFunction::AsMaxLen, env, 0)?;

    if let Some(Value::UInt(expected_len)) = args[1].match_literal_value() {
        let sequence_len = match sequence {
            Value::Sequence(ref sequence_data) => sequence_data.len() as u128,
            _ => {
                return Err(CheckErrors::ExpectedSequence(TypeSignature::type_of(&sequence)).into())
            }
        };
        if sequence_len > *expected_len {
            Ok(Value::none())
        } else {
            if let Value::Sequence(SequenceData::List(ref mut list)) = sequence {
                list.type_signature.reduce_max_len(*expected_len as u32);
            }
            Ok(Value::some(sequence)?)
        }
    } else {
        let actual_len = eval(&args[1], env, context)?;
        Err(
            CheckErrors::TypeError(TypeSignature::UIntType, TypeSignature::type_of(&actual_len))
                .into(),
        )
    }
}

pub fn native_len(sequence: Value) -> Result<Value> {
    match sequence {
        Value::Sequence(sequence_data) => Ok(Value::UInt(sequence_data.len() as u128)),
        _ => Err(CheckErrors::ExpectedSequence(TypeSignature::type_of(&sequence)).into()),
    }
}

pub fn native_index_of(sequence: Value, to_find: Value) -> Result<Value> {
    if let Value::Sequence(sequence_data) = sequence {
        match sequence_data.contains(to_find)? {
            Some(index) => Value::some(Value::UInt(index as u128)),
            None => Ok(Value::none()),
        }
    } else {
        Err(CheckErrors::ExpectedSequence(TypeSignature::type_of(&sequence)).into())
    }
}

pub fn native_element_at(sequence: Value, index: Value) -> Result<Value> {
    let sequence_data = if let Value::Sequence(sequence_data) = sequence {
        sequence_data
    } else {
        return Err(CheckErrors::ExpectedSequence(TypeSignature::type_of(&sequence)).into());
    };

    let index = if let Value::UInt(index_u128) = index {
        if let Ok(index_usize) = usize::try_from(index_u128) {
            index_usize
        } else {
            return Ok(Value::none());
        }
    } else {
        return Err(CheckErrors::TypeValueError(TypeSignature::UIntType, index).into());
    };

    if let Some(result) = sequence_data.element_at(index) {
        Value::some(result)
    } else {
        Ok(Value::none())
    }
}

pub fn special_slice(
    args: &[SymbolicExpression],
    env: &mut Environment,
    context: &LocalContext,
) -> Result<Value> {
    check_argument_count(3, args)?;

    // TODO: runtime_cost

    let seq = eval(&args[0], env, context)?;
    let position = eval(&args[1], env, context)?;
    let length = eval(&args[2], env, context)?;

    let sliced_seq = match (seq, position, length) {
        (Value::Sequence(seq), Value::UInt(position), Value::UInt(length)) => {
            let (position, length) = match (usize::try_from(position), usize::try_from(length)) {
                (Ok(position), Ok(length)) => (position, length),
                _ => return Ok(Value::none()),
            };

            seq.slice(position, length)
        }
        _ => return Err(RuntimeErrorType::BadTypeConstruction.into()),
    }?;
    Ok(sliced_seq)
}
