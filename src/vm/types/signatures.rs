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

// TypeSignatures
use std::collections::{BTreeMap, HashMap};
use std::convert::{TryFrom, TryInto};
use std::hash::{Hash, Hasher};
use std::{cmp, fmt};

use address::c32;
use util::hash;
use vm::costs::{cost_functions, runtime_cost, CostOverflowingMath};
use vm::errors::{CheckErrors, Error as VMError, IncomparableError, RuntimeErrorType};
use vm::representations::{
    ClarityName, ContractName, SymbolicExpression, SymbolicExpressionType, TraitDefinition,
};
use vm::types::{
    CharType, QualifiedContractIdentifier, SequenceData, SequencedValue, StandardPrincipalData,
    TraitIdentifier, Value, MAX_TYPE_DEPTH, MAX_VALUE_SIZE, WRAPPER_VALUE_SIZE,
};

type Result<R> = std::result::Result<R, CheckErrors>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct AssetIdentifier {
    pub contract_identifier: QualifiedContractIdentifier,
    pub asset_name: ClarityName,
}

impl AssetIdentifier {
    pub fn STX() -> AssetIdentifier {
        AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData(0, [0u8; 20]),
                ContractName::try_from("STX".to_string()).unwrap(),
            ),
            asset_name: ClarityName::try_from("STX".to_string()).unwrap(),
        }
    }

    pub fn STX_burned() -> AssetIdentifier {
        AssetIdentifier {
            contract_identifier: QualifiedContractIdentifier::new(
                StandardPrincipalData(0, [0u8; 20]),
                ContractName::try_from("BURNED".to_string()).unwrap(),
            ),
            asset_name: ClarityName::try_from("BURNED".to_string()).unwrap(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TupleTypeSignature {
    type_map: BTreeMap<ClarityName, TypeSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BufferLength(u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StringUTF8Length(u32);

// INVARIANTS enforced by the Type Signatures.
//   1. A TypeSignature constructor will always fail rather than construct a
//        type signature for a too large or invalid type. This is why any variable length
//        type signature has a guarded constructor.
//   2. The only methods which may be called on TypeSignatures that are too large
//        (i.e., the only function that can be called by the constructor before
//         it fails) is the `.size()` method, which may be used to check the size.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TypeSignature {
    NoType,
    IntType,
    UIntType,
    BoolType,
    SequenceType(SequenceSubtype),
    PrincipalType,
    TupleType(TupleTypeSignature),
    OptionalType(Box<TypeSignature>),
    ResponseType(Box<(TypeSignature, TypeSignature)>),
    TraitReferenceType(TraitIdentifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SequenceSubtype {
    BufferType(BufferLength),
    ListType(ListTypeData),
    StringType(StringSubtype),
}

impl SequenceSubtype {
    pub fn unit_type(&self) -> TypeSignature {
        match &self {
            SequenceSubtype::ListType(ref list_data) => list_data.clone().destruct().0,
            SequenceSubtype::BufferType(_) => TypeSignature::min_buffer(),
            SequenceSubtype::StringType(StringSubtype::ASCII(_)) => {
                TypeSignature::min_string_ascii()
            }
            SequenceSubtype::StringType(StringSubtype::UTF8(_)) => TypeSignature::min_string_utf8(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StringSubtype {
    ASCII(BufferLength),
    UTF8(StringUTF8Length),
}

use self::TypeSignature::{
    BoolType, IntType, NoType, OptionalType, PrincipalType, ResponseType, SequenceType,
    TraitReferenceType, TupleType, UIntType,
};

lazy_static! {
    pub static ref BUFF_64: TypeSignature = SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(64u32).expect("BUG: Legal Clarity buffer length marked invalid")
    ));
    pub static ref BUFF_65: TypeSignature = SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(65u32).expect("BUG: Legal Clarity buffer length marked invalid")
    ));
    pub static ref BUFF_32: TypeSignature = SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(32u32).expect("BUG: Legal Clarity buffer length marked invalid")
    ));
    pub static ref BUFF_33: TypeSignature = SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(33u32).expect("BUG: Legal Clarity buffer length marked invalid")
    ));
    pub static ref BUFF_20: TypeSignature = SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(20u32).expect("BUG: Legal Clarity buffer length marked invalid")
    ));
    pub static ref BUFF_1: TypeSignature = SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(1u32).expect("BUG: Legal Clarity buffer length marked invalid")
    ));
    pub static ref BUFF_16: TypeSignature = SequenceType(SequenceSubtype::BufferType(
        BufferLength::try_from(16u32).expect("BUG: Legal Clarity buffer length marked invalid")
    ));
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ListTypeData {
    max_len: u32,
    entry_type: Box<TypeSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSignature {
    pub args: Vec<TypeSignature>,
    pub returns: TypeSignature,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixedFunction {
    pub args: Vec<FunctionArg>,
    pub returns: TypeSignature,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionType {
    Variadic(TypeSignature, TypeSignature),
    Fixed(FixedFunction),
    // Functions where the single input is a union type, e.g., Buffer or Int
    UnionArgs(Vec<TypeSignature>, TypeSignature),
    ArithmeticVariadic,
    ArithmeticUnary,
    ArithmeticBinary,
    ArithmeticComparison,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionArg {
    pub signature: TypeSignature,
    pub name: ClarityName,
}

#[cfg(test)]
impl From<&str> for TypeSignature {
    fn from(val: &str) -> Self {
        use vm::ast::parse;
        let expr = &parse(&QualifiedContractIdentifier::transient(), val).unwrap()[0];
        TypeSignature::parse_type_repr(expr, &mut ()).unwrap()
    }
}

impl From<FixedFunction> for FunctionSignature {
    fn from(data: FixedFunction) -> FunctionSignature {
        let FixedFunction { args, returns } = data;
        let args = args.into_iter().map(|x| x.signature).collect();
        FunctionSignature { args, returns }
    }
}

impl From<ListTypeData> for TypeSignature {
    fn from(data: ListTypeData) -> Self {
        SequenceType(SequenceSubtype::ListType(data))
    }
}

impl From<TupleTypeSignature> for TypeSignature {
    fn from(data: TupleTypeSignature) -> Self {
        TupleType(data)
    }
}

impl From<&BufferLength> for u32 {
    fn from(v: &BufferLength) -> u32 {
        v.0
    }
}

impl From<BufferLength> for u32 {
    fn from(v: BufferLength) -> u32 {
        v.0
    }
}

impl TryFrom<u32> for BufferLength {
    type Error = CheckErrors;
    fn try_from(data: u32) -> Result<BufferLength> {
        if data > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(BufferLength(data))
        }
    }
}

impl TryFrom<usize> for BufferLength {
    type Error = CheckErrors;
    fn try_from(data: usize) -> Result<BufferLength> {
        if data > (MAX_VALUE_SIZE as usize) {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(BufferLength(data as u32))
        }
    }
}

impl TryFrom<i128> for BufferLength {
    type Error = CheckErrors;
    fn try_from(data: i128) -> Result<BufferLength> {
        if data > (MAX_VALUE_SIZE as i128) {
            Err(CheckErrors::ValueTooLarge)
        } else if data < 0 {
            Err(CheckErrors::ValueOutOfBounds)
        } else {
            Ok(BufferLength(data as u32))
        }
    }
}

impl From<&StringUTF8Length> for u32 {
    fn from(v: &StringUTF8Length) -> u32 {
        v.0
    }
}

impl From<StringUTF8Length> for u32 {
    fn from(v: StringUTF8Length) -> u32 {
        v.0
    }
}

impl TryFrom<u32> for StringUTF8Length {
    type Error = CheckErrors;
    fn try_from(data: u32) -> Result<StringUTF8Length> {
        let len = data
            .checked_mul(4)
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if len > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(StringUTF8Length(data))
        }
    }
}

impl TryFrom<usize> for StringUTF8Length {
    type Error = CheckErrors;
    fn try_from(data: usize) -> Result<StringUTF8Length> {
        let len = data
            .checked_mul(4)
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if len > (MAX_VALUE_SIZE as usize) {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(StringUTF8Length(data as u32))
        }
    }
}

impl TryFrom<i128> for StringUTF8Length {
    type Error = CheckErrors;
    fn try_from(data: i128) -> Result<StringUTF8Length> {
        let len = data
            .checked_mul(4)
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if len > (MAX_VALUE_SIZE as i128) {
            Err(CheckErrors::ValueTooLarge)
        } else if data < 0 {
            Err(CheckErrors::ValueOutOfBounds)
        } else {
            Ok(StringUTF8Length(data as u32))
        }
    }
}

impl ListTypeData {
    pub fn new_list(entry_type: TypeSignature, max_len: u32) -> Result<ListTypeData> {
        let would_be_depth = 1 + entry_type.depth();
        if would_be_depth > MAX_TYPE_DEPTH {
            return Err(CheckErrors::TypeSignatureTooDeep);
        }

        let list_data = ListTypeData {
            entry_type: Box::new(entry_type),
            max_len: max_len as u32,
        };
        let would_be_size = list_data
            .inner_size()
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if would_be_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(list_data)
        }
    }

    pub fn destruct(self) -> (TypeSignature, u32) {
        (*self.entry_type, self.max_len)
    }

    // if checks like as-max-len pass, they may _reduce_
    //   but should not increase the type signatures max length
    pub fn reduce_max_len(&mut self, new_max_len: u32) {
        if new_max_len <= self.max_len {
            self.max_len = new_max_len;
        }
    }

    pub fn get_max_len(&self) -> u32 {
        self.max_len
    }

    pub fn get_list_item_type(&self) -> &TypeSignature {
        &self.entry_type
    }
}

impl TypeSignature {
    pub fn new_option(inner_type: TypeSignature) -> Result<TypeSignature> {
        let new_size = WRAPPER_VALUE_SIZE + inner_type.size();
        let new_depth = 1 + inner_type.depth();
        if new_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else if new_depth > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep)
        } else {
            Ok(OptionalType(Box::new(inner_type)))
        }
    }

    pub fn new_response(ok_type: TypeSignature, err_type: TypeSignature) -> Result<TypeSignature> {
        let new_size = WRAPPER_VALUE_SIZE + cmp::max(ok_type.size(), err_type.size());
        let new_depth = 1 + cmp::max(ok_type.depth(), err_type.depth());

        if new_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else if new_depth > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep)
        } else {
            Ok(ResponseType(Box::new((ok_type, err_type))))
        }
    }

    pub fn is_response_type(&self) -> bool {
        if let TypeSignature::ResponseType(_) = self {
            true
        } else {
            false
        }
    }

    pub fn is_no_type(&self) -> bool {
        &TypeSignature::NoType == self
    }

    pub fn admits(&self, x: &Value) -> bool {
        let x_type = TypeSignature::type_of(x);
        self.admits_type(&x_type)
    }

    pub fn admits_type(&self, other: &TypeSignature) -> bool {
        match self {
            SequenceType(SequenceSubtype::ListType(ref my_list_type)) => {
                if let SequenceType(SequenceSubtype::ListType(other_list_type)) = other {
                    if other_list_type.max_len == 0 {
                        // if other is an empty list, a list type should always admit.
                        true
                    } else if my_list_type.max_len >= other_list_type.max_len {
                        my_list_type
                            .entry_type
                            .admits_type(&*other_list_type.entry_type)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            SequenceType(SequenceSubtype::BufferType(ref my_len)) => {
                if let SequenceType(SequenceSubtype::BufferType(ref other_len)) = other {
                    my_len.0 >= other_len.0
                } else {
                    false
                }
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                if let SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(other_len))) =
                    other
                {
                    len.0 >= other_len.0
                } else {
                    false
                }
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                if let SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(other_len))) =
                    other
                {
                    len.0 >= other_len.0
                } else {
                    false
                }
            }
            OptionalType(ref my_inner_type) => {
                if let OptionalType(other_inner_type) = other {
                    // Option types will always admit a "NoType" OptionalType -- which
                    //   can only be a None
                    if other_inner_type.is_no_type() {
                        true
                    } else {
                        my_inner_type.admits_type(other_inner_type)
                    }
                } else {
                    false
                }
            }
            ResponseType(ref my_inner_type) => {
                if let ResponseType(other_inner_type) = other {
                    // ResponseTypes admit according to the following rule:
                    //   if other.ErrType is NoType, and other.OkType admits => admit
                    //   if other.OkType is NoType, and other.ErrType admits => admit
                    //   if both OkType and ErrType admit => admit
                    //   otherwise fail.
                    if other_inner_type.0.is_no_type() {
                        my_inner_type.1.admits_type(&other_inner_type.1)
                    } else if other_inner_type.1.is_no_type() {
                        my_inner_type.0.admits_type(&other_inner_type.0)
                    } else {
                        my_inner_type.1.admits_type(&other_inner_type.1)
                            && my_inner_type.0.admits_type(&other_inner_type.0)
                    }
                } else {
                    false
                }
            }
            TupleType(ref tuple_sig) => {
                if let TupleType(ref other_tuple_sig) = other {
                    tuple_sig.admits(other_tuple_sig)
                } else {
                    false
                }
            }
            NoType => panic!("NoType should never be asked to admit."),
            _ => other == self,
        }
    }
}

impl TryFrom<Vec<(ClarityName, TypeSignature)>> for TupleTypeSignature {
    type Error = CheckErrors;
    fn try_from(mut type_data: Vec<(ClarityName, TypeSignature)>) -> Result<TupleTypeSignature> {
        if type_data.len() == 0 {
            return Err(CheckErrors::EmptyTuplesNotAllowed);
        }

        let mut type_map = BTreeMap::new();
        for (name, type_info) in type_data.drain(..) {
            if type_map.contains_key(&name) {
                return Err(CheckErrors::NameAlreadyUsed(name.into()));
            } else {
                type_map.insert(name, type_info);
            }
        }
        TupleTypeSignature::try_from(type_map)
    }
}

impl TryFrom<BTreeMap<ClarityName, TypeSignature>> for TupleTypeSignature {
    type Error = CheckErrors;
    fn try_from(type_map: BTreeMap<ClarityName, TypeSignature>) -> Result<TupleTypeSignature> {
        if type_map.len() == 0 {
            return Err(CheckErrors::EmptyTuplesNotAllowed);
        }
        for child_sig in type_map.values() {
            if (1 + child_sig.depth()) > MAX_TYPE_DEPTH {
                return Err(CheckErrors::TypeSignatureTooDeep);
            }
        }
        let result = TupleTypeSignature { type_map };
        let would_be_size = result
            .inner_size()
            .ok_or_else(|| CheckErrors::ValueTooLarge)?;
        if would_be_size > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge)
        } else {
            Ok(result)
        }
    }
}

impl TupleTypeSignature {
    pub fn len(&self) -> u64 {
        self.type_map.len() as u64
    }

    pub fn field_type(&self, field: &str) -> Option<&TypeSignature> {
        self.type_map.get(field)
    }

    pub fn get_type_map(&self) -> &BTreeMap<ClarityName, TypeSignature> {
        &self.type_map
    }

    pub fn admits(&self, other: &TupleTypeSignature) -> bool {
        if self.type_map.len() != other.type_map.len() {
            return false;
        }

        for (name, my_type_sig) in self.type_map.iter() {
            if let Some(other_type_sig) = other.type_map.get(name) {
                if !my_type_sig.admits_type(other_type_sig) {
                    return false;
                }
            } else {
                return false;
            }
        }

        return true;
    }

    pub fn parse_name_type_pair_list<A: CostTracker>(
        type_def: &SymbolicExpression,
        accounting: &mut A,
    ) -> Result<TupleTypeSignature> {
        if let SymbolicExpressionType::List(ref name_type_pairs) = type_def.expr {
            let mapped_key_types = parse_name_type_pairs(name_type_pairs, accounting)?;
            TupleTypeSignature::try_from(mapped_key_types)
        } else {
            Err(CheckErrors::BadSyntaxExpectedListOfPairs)
        }
    }

    pub fn shallow_merge(&mut self, update: &mut TupleTypeSignature) {
        self.type_map.append(&mut update.type_map);
    }
}

impl FixedFunction {
    pub fn total_type_size(&self) -> Result<u64> {
        let mut function_type_size = u64::from(self.returns.type_size()?);
        for arg in self.args.iter() {
            function_type_size =
                function_type_size.cost_overflow_add(u64::from(arg.signature.type_size()?))?;
        }
        Ok(function_type_size)
    }
}

impl FunctionSignature {
    pub fn total_type_size(&self) -> Result<u64> {
        let mut function_type_size = u64::from(self.returns.type_size()?);
        for arg in self.args.iter() {
            function_type_size =
                function_type_size.cost_overflow_add(u64::from(arg.type_size()?))?;
        }
        Ok(function_type_size)
    }

    pub fn check_args_trait_compliance(&self, args: Vec<TypeSignature>) -> bool {
        if args.len() != self.args.len() {
            return false;
        }
        let args_iter = self.args.iter().zip(args.iter());
        for (expected_arg, arg) in args_iter {
            match (expected_arg, arg) {
                (
                    TypeSignature::TraitReferenceType(expected),
                    TypeSignature::TraitReferenceType(candidate),
                ) => {
                    if candidate != expected {
                        return false;
                    }
                }
                _ => {
                    if !arg.admits_type(&expected_arg) {
                        return false;
                    }
                }
            }
        }
        true
    }
}

impl FunctionArg {
    pub fn new(signature: TypeSignature, name: ClarityName) -> FunctionArg {
        FunctionArg { signature, name }
    }
}

impl TypeSignature {
    pub fn empty_buffer() -> TypeSignature {
        SequenceType(SequenceSubtype::BufferType(0_u32.try_into().unwrap()))
    }

    pub fn min_buffer() -> TypeSignature {
        SequenceType(SequenceSubtype::BufferType(1_u32.try_into().unwrap()))
    }

    pub fn min_string_ascii() -> TypeSignature {
        SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
            1_u32.try_into().unwrap(),
        )))
    }

    pub fn min_string_utf8() -> TypeSignature {
        SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(
            1_u32.try_into().unwrap(),
        )))
    }

    pub fn max_buffer() -> TypeSignature {
        SequenceType(SequenceSubtype::BufferType(
            BufferLength::try_from(MAX_VALUE_SIZE)
                .expect("FAIL: Max Clarity Value Size is no longer realizable in Buffer Type"),
        ))
    }

    /// If one of the types is a NoType, return Ok(the other type), otherwise return least_supertype(a, b)
    pub fn factor_out_no_type(a: &TypeSignature, b: &TypeSignature) -> Result<TypeSignature> {
        if a.is_no_type() {
            Ok(b.clone())
        } else if b.is_no_type() {
            Ok(a.clone())
        } else {
            Self::least_supertype(a, b)
        }
    }

    ///
    /// This function returns the most-restrictive type that admits _both_ A and B (something like a least common supertype),
    /// or Errors if no such type exists. On error, it throws NoSuperType(A,B), unless a constructor error'ed -- in which case,
    /// it throws the constructor's error.
    ///
    ///  For two Tuples:
    ///      least_supertype(A, B) := (tuple \for_each(key k) least_supertype(type_a_k, type_b_k))
    ///  For two Lists:
    ///      least_supertype(A, B) := (list max_len: max(max_len A, max_len B), entry: least_supertype(entry_a, entry_b))
    ///        if max_len A | max_len B is 0: entry := Non-empty list entry
    ///  For two responses:
    ///      least_supertype(A, B) := (response least_supertype(ok_a, ok_b), least_supertype(err_a, err_b))
    ///        if any entries are NoType, use the other type's entry
    ///  For two options:
    ///      least_supertype(A, B) := (option least_supertype(some_a, some_b))
    ///        if some_a | some_b is NoType, use the other type's entry.
    ///  For buffers:
    ///      least_supertype(A, B) := (buff len: max(len A, len B))
    ///  For ints, uints, principals, bools:
    ///      least_supertype(A, B) := if A != B, error, else A
    ///
    pub fn least_supertype(a: &TypeSignature, b: &TypeSignature) -> Result<TypeSignature> {
        match (a, b) {
            (
                TupleType(TupleTypeSignature { type_map: types_a }),
                TupleType(TupleTypeSignature { type_map: types_b }),
            ) => {
                let mut type_map_out = BTreeMap::new();
                for (name, entry_a) in types_a.iter() {
                    let entry_b = types_b
                        .get(name)
                        .ok_or(CheckErrors::TypeError(a.clone(), b.clone()))?;
                    let entry_out = Self::least_supertype(entry_a, entry_b)?;
                    type_map_out.insert(name.clone(), entry_out);
                }
                Ok(TupleTypeSignature::try_from(type_map_out).map(|x| x.into())
                   .expect("ERR: least_supertype attempted to construct a too-large supertype of two types"))
            }
            (
                SequenceType(SequenceSubtype::ListType(ListTypeData {
                    max_len: len_a,
                    entry_type: entry_a,
                })),
                SequenceType(SequenceSubtype::ListType(ListTypeData {
                    max_len: len_b,
                    entry_type: entry_b,
                })),
            ) => {
                let entry_type = if *len_a == 0 {
                    *(entry_b.clone())
                } else if *len_b == 0 {
                    *(entry_a.clone())
                } else {
                    Self::least_supertype(entry_a, entry_b)?
                };
                let max_len = cmp::max(len_a, len_b);
                Ok(Self::list_of(entry_type, *max_len)
                   .expect("ERR: least_supertype attempted to construct a too-large supertype of two types"))
            }
            (ResponseType(resp_a), ResponseType(resp_b)) => {
                let ok_type = Self::factor_out_no_type(&resp_a.0, &resp_b.0)?;
                let err_type = Self::factor_out_no_type(&resp_a.1, &resp_b.1)?;
                Ok(Self::new_response(ok_type, err_type)?)
            }
            (OptionalType(some_a), OptionalType(some_b)) => {
                let some_type = Self::factor_out_no_type(some_a, some_b)?;
                Ok(Self::new_option(some_type)?)
            }
            (
                SequenceType(SequenceSubtype::BufferType(buff_a)),
                SequenceType(SequenceSubtype::BufferType(buff_b)),
            ) => {
                let buff_len = if u32::from(buff_a) > u32::from(buff_b) {
                    buff_a
                } else {
                    buff_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::BufferType(buff_len)))
            }
            (
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(string_a))),
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(string_b))),
            ) => {
                let str_len = if u32::from(string_a) > u32::from(string_b) {
                    string_a
                } else {
                    string_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::StringType(
                    StringSubtype::ASCII(str_len),
                )))
            }
            (
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(string_a))),
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(string_b))),
            ) => {
                let str_len = if u32::from(string_a) > u32::from(string_b) {
                    string_a
                } else {
                    string_b
                }
                .clone();
                Ok(SequenceType(SequenceSubtype::StringType(
                    StringSubtype::UTF8(str_len),
                )))
            }
            (NoType, x) | (x, NoType) => Ok(x.clone()),
            (x, y) => {
                if x == y {
                    Ok(x.clone())
                } else {
                    Err(CheckErrors::TypeError(a.clone(), b.clone()))
                }
            }
        }
    }

    pub fn list_of(item_type: TypeSignature, max_len: u32) -> Result<TypeSignature> {
        ListTypeData::new_list(item_type, max_len).map(|x| x.into())
    }

    pub fn empty_list() -> ListTypeData {
        ListTypeData {
            entry_type: Box::new(TypeSignature::NoType),
            max_len: 0,
        }
    }

    pub fn type_of(x: &Value) -> TypeSignature {
        match x {
            Value::Principal(_) => PrincipalType,
            Value::Int(_v) => IntType,
            Value::UInt(_v) => UIntType,
            Value::Bool(_v) => BoolType,
            Value::Tuple(v) => TupleType(v.type_signature.clone()),
            Value::Sequence(SequenceData::List(list_data)) => list_data.type_signature(),
            Value::Sequence(SequenceData::Buffer(buff_data)) => buff_data.type_signature(),
            Value::Sequence(SequenceData::String(CharType::ASCII(ascii_data))) => {
                ascii_data.type_signature()
            }
            Value::Sequence(SequenceData::String(CharType::UTF8(utf8_data))) => {
                utf8_data.type_signature()
            }
            Value::Optional(v) => v.type_signature(),
            Value::Response(v) => v.type_signature(),
        }
    }

    // Checks if resulting type signature is of valid size.
    pub fn construct_parent_list_type(args: &[Value]) -> Result<ListTypeData> {
        let children_types: Vec<_> = args.iter().map(|x| TypeSignature::type_of(x)).collect();
        TypeSignature::parent_list_type(&children_types)
    }

    pub fn parent_list_type(
        children: &[TypeSignature],
    ) -> std::result::Result<ListTypeData, CheckErrors> {
        if let Some((first, rest)) = children.split_first() {
            let mut current_entry_type = first.clone();
            for next_entry in rest.iter() {
                current_entry_type = Self::least_supertype(&current_entry_type, next_entry)?;
            }
            let len = u32::try_from(children.len()).map_err(|_| CheckErrors::ValueTooLarge)?;
            ListTypeData::new_list(current_entry_type, len)
        } else {
            Ok(TypeSignature::empty_list())
        }
    }
}

/// Parsing functions.
impl TypeSignature {
    fn parse_atom_type(typename: &str) -> Result<TypeSignature> {
        match typename {
            "int" => Ok(TypeSignature::IntType),
            "uint" => Ok(TypeSignature::UIntType),
            "bool" => Ok(TypeSignature::BoolType),
            "principal" => Ok(TypeSignature::PrincipalType),
            _ => Err(CheckErrors::UnknownTypeName(typename.into())),
        }
    }

    // Parses list type signatures ->
    // (list maximum-length atomic-type)
    fn parse_list_type_repr<A: CostTracker>(
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        if type_args.len() != 2 {
            return Err(CheckErrors::InvalidTypeDescription);
        }

        if let SymbolicExpressionType::LiteralValue(Value::Int(max_len)) = &type_args[0].expr {
            let atomic_type_arg = &type_args[type_args.len() - 1];
            let entry_type = TypeSignature::parse_type_repr(atomic_type_arg, accounting)?;
            let max_len = u32::try_from(*max_len).map_err(|_| CheckErrors::ValueTooLarge)?;
            ListTypeData::new_list(entry_type, max_len).map(|x| x.into())
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    // Parses type signatures of the following form:
    // (tuple (key-name-0 value-type-0) (key-name-1 value-type-1))
    fn parse_tuple_type_repr<A: CostTracker>(
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        let mapped_key_types = parse_name_type_pairs(type_args, accounting)?;
        let tuple_type_signature = TupleTypeSignature::try_from(mapped_key_types)?;
        Ok(TypeSignature::from(tuple_type_signature))
    }

    // Parses type signatures of the form:
    // (buff 10)
    fn parse_buff_type_repr(type_args: &[SymbolicExpression]) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        if let SymbolicExpressionType::LiteralValue(Value::Int(buff_len)) = &type_args[0].expr {
            BufferLength::try_from(*buff_len)
                .map(|buff_len| SequenceType(SequenceSubtype::BufferType(buff_len)))
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    // Parses type signatures of the form:
    // (string-utf8 10)
    fn parse_string_utf8_type_repr(type_args: &[SymbolicExpression]) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        if let SymbolicExpressionType::LiteralValue(Value::Int(utf8_len)) = &type_args[0].expr {
            StringUTF8Length::try_from(*utf8_len).map(|utf8_len| {
                SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(utf8_len)))
            })
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    // Parses type signatures of the form:
    // (string-ascii 10)
    fn parse_string_ascii_type_repr(type_args: &[SymbolicExpression]) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        if let SymbolicExpressionType::LiteralValue(Value::Int(buff_len)) = &type_args[0].expr {
            BufferLength::try_from(*buff_len).map(|buff_len| {
                SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(buff_len)))
            })
        } else {
            Err(CheckErrors::InvalidTypeDescription)
        }
    }

    fn parse_optional_type_repr<A: CostTracker>(
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        if type_args.len() != 1 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        let inner_type = TypeSignature::parse_type_repr(&type_args[0], accounting)?;

        Ok(TypeSignature::new_option(inner_type)?)
    }

    pub fn parse_response_type_repr<A: CostTracker>(
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        if type_args.len() != 2 {
            return Err(CheckErrors::InvalidTypeDescription);
        }
        let ok_type = TypeSignature::parse_type_repr(&type_args[0], accounting)?;
        let err_type = TypeSignature::parse_type_repr(&type_args[1], accounting)?;
        Ok(TypeSignature::new_response(ok_type, err_type)?)
    }

    pub fn parse_type_repr<A: CostTracker>(
        x: &SymbolicExpression,
        accounting: &mut A,
    ) -> Result<TypeSignature> {
        runtime_cost(ClarityCostFunction::TypeParseStep, accounting, 0)?;

        match x.expr {
            SymbolicExpressionType::Atom(ref atom_type_str) => {
                let atomic_type = TypeSignature::parse_atom_type(atom_type_str)?;
                Ok(atomic_type)
            }
            SymbolicExpressionType::List(ref list_contents) => {
                let (compound_type, rest) = list_contents
                    .split_first()
                    .ok_or(CheckErrors::InvalidTypeDescription)?;
                if let SymbolicExpressionType::Atom(ref compound_type) = compound_type.expr {
                    match compound_type.as_ref() {
                        "list" => TypeSignature::parse_list_type_repr(rest, accounting),
                        "buff" => TypeSignature::parse_buff_type_repr(rest),
                        "string-utf8" => TypeSignature::parse_string_utf8_type_repr(rest),
                        "string-ascii" => TypeSignature::parse_string_ascii_type_repr(rest),
                        "tuple" => TypeSignature::parse_tuple_type_repr(rest, accounting),
                        "optional" => TypeSignature::parse_optional_type_repr(rest, accounting),
                        "response" => TypeSignature::parse_response_type_repr(rest, accounting),
                        _ => Err(CheckErrors::InvalidTypeDescription),
                    }
                } else {
                    Err(CheckErrors::InvalidTypeDescription)
                }
            }
            SymbolicExpressionType::TraitReference(_, ref trait_definition) => {
                match trait_definition {
                    TraitDefinition::Defined(trait_id) => {
                        Ok(TypeSignature::TraitReferenceType(trait_id.clone()))
                    }
                    TraitDefinition::Imported(trait_id) => {
                        Ok(TypeSignature::TraitReferenceType(trait_id.clone()))
                    }
                }
            }
            _ => Err(CheckErrors::InvalidTypeDescription),
        }
    }

    pub fn parse_trait_type_repr<A: CostTracker>(
        type_args: &[SymbolicExpression],
        accounting: &mut A,
    ) -> Result<BTreeMap<ClarityName, FunctionSignature>> {
        let mut trait_signature: BTreeMap<ClarityName, FunctionSignature> = BTreeMap::new();
        let functions_types = type_args[0]
            .match_list()
            .ok_or(CheckErrors::DefineTraitBadSignature)?;

        for function_type in functions_types.iter() {
            let args = function_type
                .match_list()
                .ok_or(CheckErrors::DefineTraitBadSignature)?;
            if args.len() != 3 {
                return Err(CheckErrors::InvalidTypeDescription);
            }

            // Extract function's name
            let fn_name = args[0]
                .match_atom()
                .ok_or(CheckErrors::DefineTraitBadSignature)?;

            // Extract function's arguments
            let fn_args_exprs = args[1]
                .match_list()
                .ok_or(CheckErrors::DefineTraitBadSignature)?;
            let mut fn_args = vec![];
            for arg_type in fn_args_exprs.iter() {
                let arg_t = TypeSignature::parse_type_repr(&arg_type, accounting)?;
                fn_args.push(arg_t);
            }

            // Extract function's type return - must be a response
            let fn_return = match TypeSignature::parse_type_repr(&args[2], accounting) {
                Ok(response) => match response {
                    TypeSignature::ResponseType(_) => Ok(response),
                    _ => Err(CheckErrors::DefineTraitBadSignature),
                },
                _ => Err(CheckErrors::DefineTraitBadSignature),
            }?;

            trait_signature.insert(
                fn_name.clone(),
                FunctionSignature {
                    args: fn_args,
                    returns: fn_return,
                },
            );
        }
        Ok(trait_signature)
    }
}

/// These implement the size calculations in TypeSignatures
///    in constructors of TypeSignatures, only `.inner_size()` may be called.
///    .inner_size is a failable method to compute the size of the type signature,
///    Failures indicate that a type signature represents _too large_ of a value.
/// TypeSignature constructors will fail instead of constructing such a type.
///   because of this, the public interface to size is infallible.
impl TypeSignature {
    pub fn depth(&self) -> u8 {
        // unlike inner_size, depth will never threaten to overflow,
        //  because a new type can only increase depth by 1.
        match self {
            // NoType's may be asked for their size at runtime --
            //  legal constructions like `(ok 1)` have NoType parts (if they have unknown error variant types).
            TraitReferenceType(_)
            | NoType
            | IntType
            | UIntType
            | BoolType
            | PrincipalType
            | SequenceType(SequenceSubtype::BufferType(_))
            | SequenceType(SequenceSubtype::StringType(_)) => 1,
            TupleType(tuple_sig) => 1 + tuple_sig.max_depth(),
            SequenceType(SequenceSubtype::ListType(list_type)) => {
                1 + list_type.get_list_item_type().depth()
            }
            OptionalType(t) => 1 + t.depth(),
            ResponseType(v) => 1 + cmp::max(v.0.depth(), v.1.depth()),
        }
    }

    pub fn size(&self) -> u32 {
        self.inner_size().expect(
            "FAIL: .size() overflowed on too large of a type. construction should have failed!",
        )
    }

    fn inner_size(&self) -> Option<u32> {
        match self {
            // NoType's may be asked for their size at runtime --
            //  legal constructions like `(ok 1)` have NoType parts (if they have unknown error variant types).
            NoType => Some(1),
            IntType => Some(16),
            UIntType => Some(16),
            BoolType => Some(1),
            PrincipalType => Some(148), // 20+128
            TupleType(tuple_sig) => tuple_sig.inner_size(),
            SequenceType(SequenceSubtype::BufferType(len))
            | SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                Some(4 + u32::from(len))
            }
            SequenceType(SequenceSubtype::ListType(list_type)) => list_type.inner_size(),
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                Some(4 + 4 * u32::from(len))
            }
            OptionalType(t) => t.size().checked_add(WRAPPER_VALUE_SIZE),
            ResponseType(v) => {
                // ResponseTypes are 1 byte for the committed bool,
                //   plus max(err_type, ok_type)
                let (t, s) = (&v.0, &v.1);
                let t_size = t.size();
                let s_size = s.size();
                cmp::max(t_size, s_size).checked_add(WRAPPER_VALUE_SIZE)
            }
            TraitReferenceType(_) => Some(276), // 20+128+128
        }
    }

    pub fn type_size(&self) -> Result<u32> {
        self.inner_type_size()
            .ok_or_else(|| CheckErrors::ValueTooLarge)
    }

    /// Returns the size of the _type signature_
    fn inner_type_size(&self) -> Option<u32> {
        match self {
            // NoType's may be asked for their size at runtime --
            //  legal constructions like `(ok 1)` have NoType parts (if they have unknown error variant types).
            // These types all only use ~1 byte for their type enum
            NoType | IntType | UIntType | BoolType | PrincipalType => Some(1),
            // u32 length + type enum
            TupleType(tuple_sig) => tuple_sig.type_size(),
            SequenceType(SequenceSubtype::BufferType(_)) => Some(1 + 4),
            SequenceType(SequenceSubtype::ListType(list_type)) => list_type.type_size(),
            SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(_))) => Some(1 + 4),
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(_))) => Some(1 + 4),
            OptionalType(t) => t.inner_type_size()?.checked_add(1),
            ResponseType(v) => {
                let (t, s) = (&v.0, &v.1);
                t.inner_type_size()?
                    .checked_add(s.inner_type_size()?)?
                    .checked_add(1)
            }
            TraitReferenceType(_) => Some(1),
        }
    }
}

impl ListTypeData {
    /// List Size: type_signature_size + max_len * entry_type.size()
    fn inner_size(&self) -> Option<u32> {
        let total_size = self
            .entry_type
            .size()
            .checked_mul(self.max_len)?
            .checked_add(self.type_size()?)?;
        if total_size > MAX_VALUE_SIZE {
            None
        } else {
            Some(total_size)
        }
    }

    fn type_size(&self) -> Option<u32> {
        let total_size = self.entry_type.inner_type_size()?.checked_add(4 + 1)?; // 1 byte for Type enum, 4 for max_len.
        if total_size > MAX_VALUE_SIZE {
            None
        } else {
            Some(total_size)
        }
    }
}

impl TupleTypeSignature {
    /// Tuple Size:
    ///    size( btreemap<name, type> ) = 2*map.len() + sum(names) + sum(values)
    pub fn type_size(&self) -> Option<u32> {
        let mut type_map_size = u32::try_from(self.type_map.len()).ok()?.checked_mul(2)?;

        for (name, type_signature) in self.type_map.iter() {
            // we only accept ascii names, so 1 char = 1 byte.
            type_map_size = type_map_size
                .checked_add(type_signature.inner_type_size()?)?
                // name.len() is bound to MAX_STRING_LEN (128), so `as u32` won't ever truncate
                .checked_add(name.len() as u32)?;
        }

        if type_map_size > MAX_VALUE_SIZE {
            None
        } else {
            Some(type_map_size)
        }
    }

    pub fn size(&self) -> u32 {
        self.inner_size()
            .expect("size() overflowed on a constructed type.")
    }

    fn max_depth(&self) -> u8 {
        let mut max = 0;
        for (_name, type_signature) in self.type_map.iter() {
            max = cmp::max(max, type_signature.depth())
        }
        max
    }

    /// Tuple Size:
    ///    size( btreemap<name, value> ) + type_size
    ///    size( btreemap<name, value> ) = 2*map.len() + sum(names) + sum(values)
    fn inner_size(&self) -> Option<u32> {
        let mut total_size = u32::try_from(self.type_map.len())
            .ok()?
            .checked_mul(2)?
            .checked_add(self.type_size()?)?;

        for (name, type_signature) in self.type_map.iter() {
            // we only accept ascii names, so 1 char = 1 byte.
            total_size = total_size
                .checked_add(type_signature.size())?
                // name.len() is bound to MAX_STRING_LEN (128), so `as u32` won't ever truncate
                .checked_add(name.len() as u32)?;
        }

        if total_size > MAX_VALUE_SIZE {
            None
        } else {
            Some(total_size)
        }
    }
}

use vm::costs::cost_functions::ClarityCostFunction;
use vm::costs::CostTracker;

pub fn parse_name_type_pairs<A: CostTracker>(
    name_type_pairs: &[SymbolicExpression],
    accounting: &mut A,
) -> Result<Vec<(ClarityName, TypeSignature)>> {
    // this is a pretty deep nesting here, but what we're trying to do is pick out the values of
    // the form:
    // ((name1 type1) (name2 type2) (name3 type3) ...)
    // which is a list of 2-length lists of atoms.
    use vm::representations::SymbolicExpressionType::{Atom, List};

    // step 1: parse it into a vec of symbolicexpression pairs.
    let as_pairs: Result<Vec<_>> = name_type_pairs
        .iter()
        .map(|key_type_pair| {
            if let List(ref as_vec) = key_type_pair.expr {
                if as_vec.len() != 2 {
                    Err(CheckErrors::BadSyntaxExpectedListOfPairs)
                } else {
                    Ok((&as_vec[0], &as_vec[1]))
                }
            } else {
                Err(CheckErrors::BadSyntaxExpectedListOfPairs)
            }
        })
        .collect();

    // step 2: turn into a vec of (name, typesignature) pairs.
    let key_types: Result<Vec<_>> = (as_pairs?)
        .iter()
        .map(|(name_symbol, type_symbol)| {
            let name = name_symbol
                .match_atom()
                .ok_or(CheckErrors::BadSyntaxExpectedListOfPairs)?
                .clone();
            let type_info = TypeSignature::parse_type_repr(type_symbol, accounting)?;
            Ok((name, type_info))
        })
        .collect();

    key_types
}

impl fmt::Display for TupleTypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(tuple")?;
        for (field_name, field_type) in self.type_map.iter() {
            write!(f, " ({} {})", &**field_name, field_type)?;
        }
        write!(f, ")")
    }
}

impl fmt::Debug for TupleTypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TupleTypeSignature {{")?;
        for (field_name, field_type) in self.type_map.iter() {
            write!(f, " \"{}\": {},", &**field_name, field_type)?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for AssetIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}::{}",
            &*self.contract_identifier.to_string(),
            &*self.asset_name
        )
    }
}

impl fmt::Display for TypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NoType => write!(f, "UnknownType"),
            IntType => write!(f, "int"),
            UIntType => write!(f, "uint"),
            BoolType => write!(f, "bool"),
            OptionalType(t) => write!(f, "(optional {})", t),
            ResponseType(v) => write!(f, "(response {} {})", v.0, v.1),
            TupleType(t) => write!(f, "{}", t),
            PrincipalType => write!(f, "principal"),
            SequenceType(SequenceSubtype::BufferType(len)) => write!(f, "(buff {})", len),
            SequenceType(SequenceSubtype::ListType(list_type_data)) => write!(
                f,
                "(list {} {})",
                list_type_data.max_len, list_type_data.entry_type
            ),
            SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(len))) => {
                write!(f, "(string-ascii {})", len)
            }
            SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(len))) => {
                write!(f, "(string-utf8 {})", len)
            }
            TraitReferenceType(trait_alias) => write!(f, "<{}>", trait_alias.to_string()),
        }
    }
}

impl fmt::Display for BufferLength {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for StringUTF8Length {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for FunctionArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.signature)
    }
}

#[cfg(test)]
mod test {
    use super::CheckErrors::*;
    use super::*;
    use vm::execute;

    fn fail_parse(val: &str) -> CheckErrors {
        use vm::ast::parse;
        let expr = &parse(&QualifiedContractIdentifier::transient(), val).unwrap()[0];
        TypeSignature::parse_type_repr(expr, &mut ()).unwrap_err()
    }

    #[test]
    fn type_of_list_of_buffs() {
        let value = execute("(list \"abc\" \"abcde\")").unwrap().unwrap();
        let type_descr = "(list 2 (string-ascii 5))".into();
        assert_eq!(TypeSignature::type_of(&value), type_descr);
    }

    #[test]
    fn type_signature_way_too_big() {
        // first_tuple.type_size ~= 131
        // second_tuple.type_size = k * (130+130)
        // to get a type-size greater than max_value all by itself,
        //   set k = 4033
        let first_tuple = TypeSignature::from("(tuple (a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 bool))");

        let mut keys = vec![];
        for i in 0..4033 {
            let key_name = ClarityName::try_from(format!("a{:0127}", i)).unwrap();
            let key_val = first_tuple.clone();
            keys.push((key_name, key_val));
        }

        assert_eq!(
            TupleTypeSignature::try_from(keys).unwrap_err(),
            ValueTooLarge
        );
    }

    #[test]
    fn test_construction() {
        let bad_type_descriptions = [
            ("(tuple)", EmptyTuplesNotAllowed),
            ("(list int int)", InvalidTypeDescription),
            ("(list 4294967296 int)", ValueTooLarge),
            ("(list 50 bazel)", UnknownTypeName("bazel".into())),
            ("(buff)", InvalidTypeDescription),
            ("(buff 4294967296)", ValueTooLarge),
            ("(buff int)", InvalidTypeDescription),
            ("(response int)", InvalidTypeDescription),
            ("(optional bazel)", UnknownTypeName("bazel".into())),
            ("(response bazel int)", UnknownTypeName("bazel".into())),
            ("(response int bazel)", UnknownTypeName("bazel".into())),
            ("bazel", UnknownTypeName("bazel".into())),
            ("()", InvalidTypeDescription),
            ("(1234)", InvalidTypeDescription),
            ("(int 3 int)", InvalidTypeDescription),
            ("1234", InvalidTypeDescription),
            ("(list 1 (buff 1048576))", ValueTooLarge),
            ("(list 4294967295 (buff 2))", ValueTooLarge),
            ("(list 2147483647 (buff 2))", ValueTooLarge),
            ("(tuple (l (buff 1048576)))", ValueTooLarge),
        ];

        for (desc, expected) in bad_type_descriptions.iter() {
            assert_eq!(&fail_parse(desc), expected);
        }

        let okay_types = [
            "(list 16 uint)",
            "(list 15 (response int bool))",
            "(list 15 (response bool int))",
            "(buff 1048576)",
            "(list 4400 bool)",
            "(tuple (l (buff 1048550)))",
        ];

        for desc in okay_types.iter() {
            TypeSignature::from(*desc); // panics on failed types.
        }
    }
}
