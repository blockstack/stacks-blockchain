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

use vm::analysis::types::{AnalysisPass, ContractAnalysis};
use vm::functions::define::{DefineFunctions, DefineFunctionsParsed};
use vm::functions::tuples;
use vm::functions::NativeFunctions;
use vm::representations::SymbolicExpressionType::{
    Atom, AtomValue, Field, List, LiteralValue, TraitReference,
};
use vm::representations::{ClarityName, SymbolicExpression, SymbolicExpressionType};
use vm::types::{parse_name_type_pairs, PrincipalData, TupleTypeSignature, TypeSignature, Value};

use std::collections::HashMap;
use vm::variables::NativeVariables;

use crate::vm::ClarityVersion;

pub use super::errors::{
    check_argument_count, check_arguments_at_least, CheckError, CheckErrors, CheckResult,
};
use super::AnalysisDatabase;

#[cfg(test)]
mod tests;

///
/// A static-analysis pass that checks whether or not
///  a proposed cost-function defining contract is allowable.
/// Cost-function defining contracts may not use contract-call,
///  any database operations, traits, or iterating operations (e.g., list
///  operations)
///
pub struct ArithmeticOnlyChecker<'a> {
    clarity_version: &'a ClarityVersion,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Error {
    DefineTypeForbidden(DefineFunctions),
    VariableForbidden(NativeVariables),
    FunctionNotPermitted(NativeFunctions),
    TraitReferencesForbidden,
    UnexpectedContractStructure,
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<'a> ArithmeticOnlyChecker<'a> {
    pub fn check_contract_cost_eligible(contract_analysis: &mut ContractAnalysis) {
        let is_eligible = ArithmeticOnlyChecker::run(contract_analysis).is_ok();
        contract_analysis.is_cost_contract_eligible = is_eligible;
    }

    pub fn run(contract_analysis: &ContractAnalysis) -> Result<(), Error> {
        let checker = ArithmeticOnlyChecker {
            clarity_version: &contract_analysis.clarity_version,
        };
        for exp in contract_analysis.expressions.iter() {
            checker.check_top_levels(&exp)?;
        }

        Ok(())
    }

    fn check_define_function(
        &self,
        _signature: &[SymbolicExpression],
        body: &SymbolicExpression,
    ) -> Result<(), Error> {
        self.check_expression(body)
    }

    fn check_top_levels(&self, expr: &SymbolicExpression) -> Result<(), Error> {
        use vm::functions::define::DefineFunctionsParsed::*;
        if let Some(define_type) = DefineFunctionsParsed::try_parse(expr)
            .map_err(|_| Error::UnexpectedContractStructure)?
        {
            match define_type {
                // The _arguments_ to constant defines must be checked to ensure that
                //   any _evaluated arguments_ supplied to them are valid.
                Constant { value, .. } => self.check_expression(value),
                PrivateFunction { signature, body } => self.check_define_function(signature, body),
                ReadOnlyFunction { signature, body } => self.check_define_function(signature, body),
                PersistedVariable { .. } => Err(Error::DefineTypeForbidden(
                    DefineFunctions::PersistedVariable,
                )),
                BoundedFungibleToken { .. } => {
                    Err(Error::DefineTypeForbidden(DefineFunctions::FungibleToken))
                }
                PublicFunction { .. } => {
                    Err(Error::DefineTypeForbidden(DefineFunctions::PublicFunction))
                }
                Map { .. } => Err(Error::DefineTypeForbidden(DefineFunctions::Map)),
                NonFungibleToken { .. } => Err(Error::DefineTypeForbidden(
                    DefineFunctions::NonFungibleToken,
                )),
                UnboundedFungibleToken { .. } => {
                    Err(Error::DefineTypeForbidden(DefineFunctions::FungibleToken))
                }
                Trait { .. } => Err(Error::DefineTypeForbidden(DefineFunctions::Trait)),
                UseTrait { .. } => Err(Error::DefineTypeForbidden(DefineFunctions::UseTrait)),
                ImplTrait { .. } => Err(Error::DefineTypeForbidden(DefineFunctions::ImplTrait)),
            }
        } else {
            self.check_expression(expr)
        }
    }

    fn check_expression(&self, expr: &SymbolicExpression) -> Result<(), Error> {
        match expr.expr {
            AtomValue(_) | LiteralValue(_) => {
                // values and literals are always allowed
                Ok(())
            }
            Atom(ref variable) => self.check_variables_allowed(variable),
            Field(_) | TraitReference(_, _) => Err(Error::TraitReferencesForbidden),
            List(ref expression) => self.check_function_application(expression),
        }
    }

    fn check_variables_allowed(&self, var_name: &ClarityName) -> Result<(), Error> {
        use vm::variables::NativeVariables::*;
        if let Some(native_var) = NativeVariables::lookup_by_name(var_name) {
            match native_var {
                ContractCaller | TxSender | TotalLiquidMicroSTX | BlockHeight | BurnBlockHeight
                | Regtest | TxSponsor => Err(Error::VariableForbidden(native_var)),
                NativeNone | NativeTrue | NativeFalse => Ok(()),
            }
        } else {
            Ok(())
        }
    }

    fn try_native_function_check(
        &self,
        function: &str,
        args: &[SymbolicExpression],
    ) -> Option<Result<(), Error>> {
        NativeFunctions::lookup_by_name_before_version(function, self.clarity_version)
            .map(|function| self.check_native_function(function, args))
    }

    fn check_native_function(
        &self,
        function: NativeFunctions,
        args: &[SymbolicExpression],
    ) -> Result<(), Error> {
        use vm::functions::NativeFunctions::*;
        match function {
            FetchVar | GetBlockInfo | GetTokenBalance | GetAssetOwner | FetchEntry | SetEntry
            | DeleteEntry | InsertEntry | SetVar | MintAsset | MintToken | TransferAsset
            | TransferToken | ContractCall | StxTransfer | StxBurn | AtBlock | GetStxBalance
            | GetTokenSupply | BurnToken | BurnAsset | StxGetAccount => {
                return Err(Error::FunctionNotPermitted(function));
            }
            Append | Concat | AsMaxLen | ContractOf | PrincipalOf | ListCons | Print
            | AsContract | ElementAt | IndexOf | Map | Filter | Fold | Slice => {
                return Err(Error::FunctionNotPermitted(function));
            }
            Sha512 | Sha512Trunc256 | Secp256k1Recover | Secp256k1Verify | Hash160 | Sha256
            | Keccak256 => {
                return Err(Error::FunctionNotPermitted(function));
            }
            Add | Subtract | Divide | Multiply | CmpGeq | CmpLeq | CmpLess | CmpGreater
            | Modulo | Power | Sqrti | Log2 | BitwiseXOR | And | Or | Not | Equals | If
            | ConsSome | ConsOkay | ConsError | DefaultTo | UnwrapRet | UnwrapErrRet | IsOkay
            | IsNone | Asserts | Unwrap | UnwrapErr | IsErr | IsSome | TryRet | ToUInt | ToInt
            | Len | Begin | TupleMerge => self.check_all(args),
            // we need to treat all the remaining functions specially, because these
            //   do not eval all of their arguments (rather, one or more of their arguments
            //   is a name)
            TupleGet => {
                // these functions use a name in the first argument
                check_argument_count(2, args).map_err(|_| Error::UnexpectedContractStructure)?;
                self.check_all(&args[1..])
            }
            Match => {
                if !(args.len() == 4 || args.len() == 5) {
                    return Err(Error::UnexpectedContractStructure);
                }
                // check the match input
                self.check_expression(&args[0])?;
                // check the 'ok' branch
                self.check_expression(&args[2])?;
                // check the 'err' branch
                if args.len() == 4 {
                    self.check_expression(&args[3])
                } else {
                    self.check_expression(&args[4])
                }
            }
            Let => {
                check_arguments_at_least(2, args)
                    .map_err(|_| Error::UnexpectedContractStructure)?;

                let binding_list = args[0]
                    .match_list()
                    .ok_or(Error::UnexpectedContractStructure)?;

                for pair in binding_list.iter() {
                    let pair_expression = pair
                        .match_list()
                        .ok_or(Error::UnexpectedContractStructure)?;
                    if pair_expression.len() != 2 {
                        return Err(Error::UnexpectedContractStructure);
                    }

                    self.check_expression(&pair_expression[1])?;
                }

                self.check_all(&args[1..args.len()])
            }
            TupleCons => {
                for pair in args.iter() {
                    let pair_expression = pair
                        .match_list()
                        .ok_or(Error::UnexpectedContractStructure)?;
                    if pair_expression.len() != 2 {
                        return Err(Error::UnexpectedContractStructure);
                    }

                    self.check_expression(&pair_expression[1])?;
                }
                Ok(())
            }
        }
    }

    fn check_all(&self, expressions: &[SymbolicExpression]) -> Result<(), Error> {
        for expr in expressions.iter() {
            self.check_expression(expr)?;
        }
        Ok(())
    }

    fn check_function_application(&self, expression: &[SymbolicExpression]) -> Result<(), Error> {
        let (function_name, args) = expression
            .split_first()
            .ok_or(Error::UnexpectedContractStructure)?;

        let function_name = function_name
            .match_atom()
            .ok_or(Error::UnexpectedContractStructure)?;

        if let Some(result) = self.try_native_function_check(function_name, args) {
            result
        } else {
            // non-native function invocations are always okay, just check the args!
            self.check_all(args)
        }
    }
}
