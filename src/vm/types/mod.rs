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

pub mod serialization;
pub mod signatures;

use std::collections::BTreeMap;
use std::convert::{TryFrom, TryInto};
use std::{char, str};
use std::{cmp, fmt};

use regex::Regex;

use address::c32;
use util::hash;

use vm::errors::{
    CheckErrors, IncomparableError, InterpreterError, InterpreterResult as Result, RuntimeErrorType,
};
use vm::representations::{ClarityName, ContractName, SymbolicExpression, SymbolicExpressionType};

pub use vm::types::signatures::{
    parse_name_type_pairs, AssetIdentifier, BufferLength, FixedFunction, FunctionArg,
    FunctionSignature, FunctionType, ListTypeData, SequenceSubtype, StringSubtype,
    StringUTF8Length, TupleTypeSignature, TypeSignature, BUFF_1, BUFF_20, BUFF_32, BUFF_33,
    BUFF_64, BUFF_65,
};

pub const MAX_VALUE_SIZE: u32 = 1024 * 1024; // 1MB
pub const BOUND_VALUE_SERIALIZATION_BYTES: u32 = MAX_VALUE_SIZE * 2;
pub const BOUND_VALUE_SERIALIZATION_HEX: u32 = BOUND_VALUE_SERIALIZATION_BYTES * 2;

pub const MAX_TYPE_DEPTH: u8 = 32;
// this is the charged size for wrapped values, i.e., response or optionals
pub const WRAPPER_VALUE_SIZE: u32 = 1;

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct TupleData {
    // todo: remove type_signature
    pub type_signature: TupleTypeSignature,
    pub data_map: BTreeMap<ClarityName, Value>,
}

#[derive(Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuffData {
    pub data: Vec<u8>,
}

#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct ListData {
    pub data: Vec<Value>,
    // todo: remove type_signature
    pub type_signature: ListTypeData,
}

#[derive(Clone, Eq, PartialEq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct StandardPrincipalData(pub u8, pub [u8; 20]);

impl StandardPrincipalData {
    pub fn transient() -> StandardPrincipalData {
        Self(
            1,
            [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        )
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct QualifiedContractIdentifier {
    pub issuer: StandardPrincipalData,
    pub name: ContractName,
}

impl QualifiedContractIdentifier {
    pub fn new(issuer: StandardPrincipalData, name: ContractName) -> QualifiedContractIdentifier {
        Self { issuer, name }
    }

    pub fn local(name: &str) -> Result<QualifiedContractIdentifier> {
        let name = name.to_string().try_into()?;
        Ok(Self::new(StandardPrincipalData::transient(), name))
    }

    pub fn transient() -> QualifiedContractIdentifier {
        let name = String::from("__transient").try_into().unwrap();
        Self {
            issuer: StandardPrincipalData::transient(),
            name,
        }
    }

    pub fn parse(literal: &str) -> Result<QualifiedContractIdentifier> {
        let split: Vec<_> = literal.splitn(2, ".").collect();
        if split.len() != 2 {
            return Err(RuntimeErrorType::ParseError(
                "Invalid principal literal: expected a `.` in a qualified contract name"
                    .to_string(),
            )
            .into());
        }
        let sender = PrincipalData::parse_standard_principal(split[0])?;
        let name = split[1].to_string().try_into()?;
        Ok(QualifiedContractIdentifier::new(sender, name))
    }

    pub fn to_string(&self) -> String {
        format!("{}.{}", self.issuer, self.name.to_string())
    }
}

impl fmt::Display for QualifiedContractIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum PrincipalData {
    Standard(StandardPrincipalData),
    Contract(QualifiedContractIdentifier),
}

pub enum ContractIdentifier {
    Relative(ContractName),
    Qualified(QualifiedContractIdentifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OptionalData {
    pub data: Option<Box<Value>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResponseData {
    pub committed: bool,
    pub data: Box<Value>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct TraitIdentifier {
    pub name: ClarityName,
    pub contract_identifier: QualifiedContractIdentifier,
}

impl TraitIdentifier {
    pub fn new(
        issuer: StandardPrincipalData,
        contract_name: ContractName,
        name: ClarityName,
    ) -> TraitIdentifier {
        Self {
            name,
            contract_identifier: QualifiedContractIdentifier {
                issuer,
                name: contract_name,
            },
        }
    }

    pub fn parse_fully_qualified(literal: &str) -> Result<TraitIdentifier> {
        let (issuer, contract_name, name) = Self::parse(literal)?;
        let issuer = issuer.ok_or(RuntimeErrorType::BadTypeConstruction)?;
        Ok(TraitIdentifier::new(issuer, contract_name, name))
    }

    pub fn parse_sugared_syntax(literal: &str) -> Result<(ContractName, ClarityName)> {
        let (_, contract_name, name) = Self::parse(literal)?;
        Ok((contract_name, name))
    }

    pub fn parse(
        literal: &str,
    ) -> Result<(Option<StandardPrincipalData>, ContractName, ClarityName)> {
        let split: Vec<_> = literal.splitn(3, ".").collect();
        if split.len() != 3 {
            return Err(RuntimeErrorType::ParseError(
                "Invalid principal literal: expected a `.` in a qualified contract name"
                    .to_string(),
            )
            .into());
        }

        let issuer = match split[0].len() {
            0 => None,
            _ => Some(PrincipalData::parse_standard_principal(split[0])?),
        };
        let contract_name = split[1].to_string().try_into()?;
        let name = split[2].to_string().try_into()?;

        Ok((issuer, contract_name, name))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Value {
    Int(i128),
    UInt(u128),
    Bool(bool),
    Sequence(SequenceData),
    Principal(PrincipalData),
    Tuple(TupleData),
    Optional(OptionalData),
    Response(ResponseData),
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum SequenceData {
    Buffer(BuffData),
    List(ListData),
    String(CharType),
}

impl SequenceData {
    pub fn atom_values(&mut self) -> Vec<SymbolicExpression> {
        match self {
            SequenceData::Buffer(ref mut data) => data.atom_values(),
            SequenceData::List(ref mut data) => data.atom_values(),
            SequenceData::String(CharType::ASCII(ref mut data)) => data.atom_values(),
            SequenceData::String(CharType::UTF8(ref mut data)) => data.atom_values(),
        }
    }

    pub fn len(&self) -> usize {
        match &self {
            SequenceData::Buffer(data) => data.items().len(),
            SequenceData::List(data) => data.items().len(),
            SequenceData::String(CharType::ASCII(data)) => data.items().len(),
            SequenceData::String(CharType::UTF8(data)) => data.items().len(),
        }
    }

    pub fn element_at(self, index: usize) -> Option<Value> {
        if self.len() <= index {
            return None;
        }
        let result = match self {
            SequenceData::Buffer(data) => Value::buff_from_byte(data.data[index]),
            SequenceData::List(mut data) => data.data.remove(index),
            SequenceData::String(CharType::ASCII(data)) => {
                Value::string_ascii_from_bytes(vec![data.data[index]])
                    .expect("BUG: failed to initialize single-byte ASCII buffer")
            }
            SequenceData::String(CharType::UTF8(mut data)) => {
                Value::Sequence(SequenceData::String(CharType::UTF8(UTF8Data {
                    data: vec![data.data.remove(index)],
                })))
            }
        };

        Some(result)
    }

    pub fn contains(&self, to_find: Value) -> Result<Option<usize>> {
        match self {
            SequenceData::Buffer(ref data) => {
                if let Value::Sequence(SequenceData::Buffer(to_find_vec)) = to_find {
                    if to_find_vec.data.len() != 1 {
                        Ok(None)
                    } else {
                        for (index, entry) in data.data.iter().enumerate() {
                            if entry == &to_find_vec.data[0] {
                                return Ok(Some(index));
                            }
                        }
                        Ok(None)
                    }
                } else {
                    Err(CheckErrors::TypeValueError(TypeSignature::min_buffer(), to_find).into())
                }
            }
            SequenceData::List(ref data) => {
                for (index, entry) in data.data.iter().enumerate() {
                    if entry == &to_find {
                        return Ok(Some(index));
                    }
                }
                Ok(None)
            }
            SequenceData::String(CharType::ASCII(ref data)) => {
                if let Value::Sequence(SequenceData::String(CharType::ASCII(to_find_vec))) = to_find
                {
                    if to_find_vec.data.len() != 1 {
                        Ok(None)
                    } else {
                        for (index, entry) in data.data.iter().enumerate() {
                            if entry == &to_find_vec.data[0] {
                                return Ok(Some(index));
                            }
                        }
                        Ok(None)
                    }
                } else {
                    Err(
                        CheckErrors::TypeValueError(TypeSignature::min_string_ascii(), to_find)
                            .into(),
                    )
                }
            }
            SequenceData::String(CharType::UTF8(ref data)) => {
                if let Value::Sequence(SequenceData::String(CharType::UTF8(to_find_vec))) = to_find
                {
                    if to_find_vec.data.len() != 1 {
                        Ok(None)
                    } else {
                        for (index, entry) in data.data.iter().enumerate() {
                            if entry == &to_find_vec.data[0] {
                                return Ok(Some(index));
                            }
                        }
                        Ok(None)
                    }
                } else {
                    Err(
                        CheckErrors::TypeValueError(TypeSignature::min_string_utf8(), to_find)
                            .into(),
                    )
                }
            }
        }
    }

    pub fn filter<F>(&mut self, filter: &mut F) -> Result<()>
    where
        F: FnMut(SymbolicExpression) -> Result<bool>,
    {
        // Note: this macro can probably get removed once
        // ```Vec::drain_filter<F>(&mut self, filter: F) -> DrainFilter<T, F>```
        // is available in rust stable channel (experimental at this point).
        macro_rules! drain_filter {
            ($data:expr, $seq_type:ident) => {
                let mut i = 0;
                while i != $data.data.len() {
                    let atom_value =
                        SymbolicExpression::atom_value($seq_type::to_value(&$data.data[i]));
                    match filter(atom_value) {
                        Ok(res) if res == false => {
                            $data.data.remove(i);
                        }
                        Ok(_) => {
                            i += 1;
                        }
                        Err(err) => return Err(err),
                    }
                }
            };
        }

        match self {
            SequenceData::Buffer(ref mut data) => {
                drain_filter!(data, BuffData);
            }
            SequenceData::List(ref mut data) => {
                drain_filter!(data, ListData);
            }
            SequenceData::String(CharType::ASCII(ref mut data)) => {
                drain_filter!(data, ASCIIData);
            }
            SequenceData::String(CharType::UTF8(ref mut data)) => {
                drain_filter!(data, UTF8Data);
            }
        }
        Ok(())
    }

    pub fn append(&mut self, other_seq: &mut SequenceData) -> Result<()> {
        match (self, other_seq) {
            (
                SequenceData::List(ref mut inner_data),
                SequenceData::List(ref mut other_inner_data),
            ) => inner_data.append(other_inner_data),
            (
                SequenceData::Buffer(ref mut inner_data),
                SequenceData::Buffer(ref mut other_inner_data),
            ) => inner_data.append(other_inner_data),
            (
                SequenceData::String(CharType::ASCII(ref mut inner_data)),
                SequenceData::String(CharType::ASCII(ref mut other_inner_data)),
            ) => inner_data.append(other_inner_data),
            (
                SequenceData::String(CharType::UTF8(ref mut inner_data)),
                SequenceData::String(CharType::UTF8(ref mut other_inner_data)),
            ) => inner_data.append(other_inner_data),
            _ => Err(RuntimeErrorType::BadTypeConstruction.into()),
        }?;
        Ok(())
    }
}

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum CharType {
    UTF8(UTF8Data),
    ASCII(ASCIIData),
}

impl fmt::Display for CharType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CharType::ASCII(string) => write!(f, "{}", string),
            CharType::UTF8(string) => write!(f, "{}", string),
        }
    }
}

impl fmt::Debug for CharType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ASCIIData {
    pub data: Vec<u8>,
}

impl fmt::Display for ASCIIData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut escaped_str = String::new();
        for c in self.data.iter() {
            let escaped_char = format!("{}", std::ascii::escape_default(*c));
            escaped_str.push_str(&escaped_char);
        }
        write!(f, "{}", format!("\"{}\"", escaped_str))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UTF8Data {
    pub data: Vec<Vec<u8>>,
}

impl fmt::Display for UTF8Data {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = String::new();
        for c in self.data.iter() {
            if c.len() > 1 {
                // We escape extended charset
                result.push_str(&format!("\\u{{{}}}", hash::to_hex(&c[..])));
            } else {
                // We render an ASCII char, escaped
                let escaped_char = format!("{}", std::ascii::escape_default(c[0]));
                result.push_str(&escaped_char);
            }
        }
        write!(f, "{}", format!("u\"{}\"", result))
    }
}

pub trait SequencedValue<T> {
    fn type_signature(&self) -> TypeSignature;

    fn items(&self) -> &Vec<T>;

    fn drained_items(&mut self) -> Vec<T>;

    fn to_value(v: &T) -> Value;

    fn atom_values(&mut self) -> Vec<SymbolicExpression> {
        self.drained_items()
            .iter()
            .map(|item| SymbolicExpression::atom_value(Self::to_value(&item)))
            .collect()
    }
}

impl SequencedValue<Value> for ListData {
    fn items(&self) -> &Vec<Value> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<Value> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> TypeSignature {
        TypeSignature::SequenceType(SequenceSubtype::ListType(self.type_signature.clone()))
    }

    fn to_value(v: &Value) -> Value {
        v.clone()
    }
}

impl SequencedValue<u8> for BuffData {
    fn items(&self) -> &Vec<u8> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<u8> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> TypeSignature {
        let buff_length = BufferLength::try_from(self.data.len())
            .expect("ERROR: Too large of a buffer successfully constructed.");
        TypeSignature::SequenceType(SequenceSubtype::BufferType(buff_length))
    }

    fn to_value(v: &u8) -> Value {
        Value::buff_from_byte(*v)
    }
}

impl SequencedValue<u8> for ASCIIData {
    fn items(&self) -> &Vec<u8> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<u8> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> TypeSignature {
        let buff_length = BufferLength::try_from(self.data.len())
            .expect("ERROR: Too large of a buffer successfully constructed.");
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::ASCII(
            buff_length,
        )))
    }

    fn to_value(v: &u8) -> Value {
        Value::string_ascii_from_bytes(vec![*v])
            .expect("ERROR: Invalid ASCII string successfully constructed")
    }
}

impl SequencedValue<Vec<u8>> for UTF8Data {
    fn items(&self) -> &Vec<Vec<u8>> {
        &self.data
    }

    fn drained_items(&mut self) -> Vec<Vec<u8>> {
        self.data.drain(..).collect()
    }

    fn type_signature(&self) -> TypeSignature {
        let str_len = StringUTF8Length::try_from(self.data.len())
            .expect("ERROR: Too large of a buffer successfully constructed.");
        TypeSignature::SequenceType(SequenceSubtype::StringType(StringSubtype::UTF8(str_len)))
    }

    fn to_value(v: &Vec<u8>) -> Value {
        Value::string_utf8_from_bytes(v.clone())
            .expect("ERROR: Invalid UTF8 string successfully constructed")
    }
}

define_named_enum!(BlockInfoProperty {
    Time("time"),
    VrfSeed("vrf-seed"),
    HeaderHash("header-hash"),
    IdentityHeaderHash("id-header-hash"),
    BurnchainHeaderHash("burnchain-header-hash"),
    MinerAddress("miner-address"),
});

define_named_enum!(PrincipalProperty {
    Version("version"),
    PubKeyHash("pub-key-hash"),
});

impl OptionalData {
    pub fn type_signature(&self) -> TypeSignature {
        let type_result = match self.data {
            Some(ref v) => TypeSignature::new_option(TypeSignature::type_of(&v)),
            None => TypeSignature::new_option(TypeSignature::NoType),
        };
        type_result.expect("Should not have constructed too large of a type.")
    }
}

impl ResponseData {
    pub fn type_signature(&self) -> TypeSignature {
        let type_result = match self.committed {
            true => TypeSignature::new_response(
                TypeSignature::type_of(&self.data),
                TypeSignature::NoType,
            ),
            false => TypeSignature::new_response(
                TypeSignature::NoType,
                TypeSignature::type_of(&self.data),
            ),
        };
        type_result.expect("Should not have constructed too large of a type.")
    }
}

impl BlockInfoProperty {
    pub fn type_result(&self) -> TypeSignature {
        use self::BlockInfoProperty::*;
        match self {
            Time => TypeSignature::UIntType,
            IdentityHeaderHash | VrfSeed | HeaderHash | BurnchainHeaderHash => BUFF_32.clone(),
            MinerAddress => TypeSignature::PrincipalType,
        }
    }
}

impl PrincipalProperty {
    pub fn type_result(&self) -> TypeSignature {
        use self::PrincipalProperty::*;
        match self {
            Version => TypeSignature::UIntType,
            PubKeyHash => BUFF_20.clone(),
        }
    }
}

impl PartialEq for ListData {
    fn eq(&self, other: &ListData) -> bool {
        self.data == other.data
    }
}

impl PartialEq for TupleData {
    fn eq(&self, other: &TupleData) -> bool {
        self.data_map == other.data_map
    }
}

pub const NONE: Value = Value::Optional(OptionalData { data: None });

impl Value {
    pub fn some(data: Value) -> Result<Value> {
        if data.size() + WRAPPER_VALUE_SIZE > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge.into())
        } else if data.depth() + 1 > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep.into())
        } else {
            Ok(Value::Optional(OptionalData {
                data: Some(Box::new(data)),
            }))
        }
    }

    pub fn none() -> Value {
        NONE.clone()
    }

    pub fn okay_true() -> Value {
        Value::Response(ResponseData {
            committed: true,
            data: Box::new(Value::Bool(true)),
        })
    }

    pub fn err_uint(ecode: u128) -> Value {
        Value::Response(ResponseData {
            committed: false,
            data: Box::new(Value::UInt(ecode)),
        })
    }

    pub fn err_none() -> Value {
        Value::Response(ResponseData {
            committed: false,
            data: Box::new(NONE.clone()),
        })
    }

    pub fn okay(data: Value) -> Result<Value> {
        if data.size() + WRAPPER_VALUE_SIZE > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge.into())
        } else if data.depth() + 1 > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep.into())
        } else {
            Ok(Value::Response(ResponseData {
                committed: true,
                data: Box::new(data),
            }))
        }
    }

    pub fn error(data: Value) -> Result<Value> {
        if data.size() + WRAPPER_VALUE_SIZE > MAX_VALUE_SIZE {
            Err(CheckErrors::ValueTooLarge.into())
        } else if data.depth() + 1 > MAX_TYPE_DEPTH {
            Err(CheckErrors::TypeSignatureTooDeep.into())
        } else {
            Ok(Value::Response(ResponseData {
                committed: false,
                data: Box::new(data),
            }))
        }
    }

    pub fn size(&self) -> u32 {
        TypeSignature::type_of(self).size()
    }

    pub fn depth(&self) -> u8 {
        TypeSignature::type_of(self).depth()
    }

    /// Invariant: the supplied Values have already been "checked", i.e., it's a valid Value object
    ///  this invariant is enforced through the Value constructors, each of which checks to ensure
    ///  that any typing data is correct.
    pub fn list_with_type(list_data: Vec<Value>, expected_type: ListTypeData) -> Result<Value> {
        // Constructors for TypeSignature ensure that the size of the Value cannot
        //   be greater than MAX_VALUE_SIZE (they error on such constructions)
        //   so we do not need to perform that check here.
        if (expected_type.get_max_len() as usize) < list_data.len() {
            return Err(InterpreterError::FailureConstructingListWithType.into());
        }

        {
            let expected_item_type = expected_type.get_list_item_type();

            for item in &list_data {
                if !expected_item_type.admits(&item) {
                    return Err(InterpreterError::FailureConstructingListWithType.into());
                }
            }
        }

        Ok(Value::Sequence(SequenceData::List(ListData {
            data: list_data,
            type_signature: expected_type,
        })))
    }

    pub fn list_from(list_data: Vec<Value>) -> Result<Value> {
        // Constructors for TypeSignature ensure that the size of the Value cannot
        //   be greater than MAX_VALUE_SIZE (they error on such constructions)
        // Aaron: at this point, we've _already_ allocated memory for this type.
        //     (e.g., from a (map...) call, or a (list...) call.
        //     this is a problem _if_ the static analyzer cannot already prevent
        //     this case. This applies to all the constructor size checks.
        let type_sig = TypeSignature::construct_parent_list_type(&list_data)?;
        Ok(Value::Sequence(SequenceData::List(ListData {
            data: list_data,
            type_signature: type_sig,
        })))
    }

    pub fn buff_from(buff_data: Vec<u8>) -> Result<Value> {
        // check the buffer size
        BufferLength::try_from(buff_data.len())?;
        // construct the buffer
        Ok(Value::Sequence(SequenceData::Buffer(BuffData {
            data: buff_data,
        })))
    }

    pub fn buff_from_byte(byte: u8) -> Value {
        Value::Sequence(SequenceData::Buffer(BuffData { data: vec![byte] }))
    }

    pub fn string_ascii_from_bytes(bytes: Vec<u8>) -> Result<Value> {
        // check the string size
        BufferLength::try_from(bytes.len())?;

        for b in bytes.iter() {
            if !b.is_ascii_alphanumeric() && !b.is_ascii_punctuation() && !b.is_ascii_whitespace() {
                return Err(CheckErrors::InvalidCharactersDetected.into());
            }
        }
        // construct the string
        Ok(Value::Sequence(SequenceData::String(CharType::ASCII(
            ASCIIData { data: bytes },
        ))))
    }

    pub fn string_utf8_from_string_utf8_literal(tokenized_str: String) -> Result<Value> {
        let wrapped_codepoints_matcher =
            Regex::new("^\\\\u\\{(?P<value>[[:xdigit:]]+)\\}").unwrap();
        let mut window = tokenized_str.as_str();
        let mut cursor = 0;
        let mut data: Vec<Vec<u8>> = vec![];
        while !window.is_empty() {
            if let Some(captures) = wrapped_codepoints_matcher.captures(window) {
                let matched = captures.name("value").unwrap();
                let scalar_value = window[matched.start()..matched.end()].to_string();
                let unicode_char = {
                    let u = u32::from_str_radix(&scalar_value, 16).unwrap();
                    let c = char::from_u32(u).unwrap();
                    let mut encoded_char: Vec<u8> = vec![0; c.len_utf8()];
                    c.encode_utf8(&mut encoded_char[..]);
                    encoded_char
                };

                data.push(unicode_char);
                cursor += scalar_value.len() + 4;
            } else {
                let ascii_char = window[0..1].to_string().into_bytes();
                data.push(ascii_char);
                cursor += 1;
            }
            // check the string size
            StringUTF8Length::try_from(data.len())?;

            window = &tokenized_str[cursor..];
        }
        // construct the string
        Ok(Value::Sequence(SequenceData::String(CharType::UTF8(
            UTF8Data { data },
        ))))
    }

    pub fn string_utf8_from_bytes(bytes: Vec<u8>) -> Result<Value> {
        let validated_utf8_str = match str::from_utf8(&bytes) {
            Ok(string) => string,
            _ => return Err(CheckErrors::InvalidCharactersDetected.into()),
        };
        let mut data = vec![];
        for char in validated_utf8_str.chars() {
            let mut encoded_char: Vec<u8> = vec![0; char.len_utf8()];
            char.encode_utf8(&mut encoded_char[..]);
            data.push(encoded_char);
        }
        // check the string size
        StringUTF8Length::try_from(data.len())?;

        Ok(Value::Sequence(SequenceData::String(CharType::UTF8(
            UTF8Data { data },
        ))))
    }

    pub fn expect_ascii(self) -> String {
        if let Value::Sequence(SequenceData::String(CharType::ASCII(ASCIIData { data }))) = self {
            String::from_utf8(data).unwrap()
        } else {
            error!("Value '{:?}' is not an ASCII string", &self);
            panic!();
        }
    }

    pub fn expect_u128(self) -> u128 {
        if let Value::UInt(inner) = self {
            inner
        } else {
            error!("Value '{:?}' is not a u128", &self);
            panic!();
        }
    }

    pub fn expect_i128(self) -> i128 {
        if let Value::Int(inner) = self {
            inner
        } else {
            error!("Value '{:?}' is not an i128", &self);
            panic!();
        }
    }

    pub fn expect_buff(self, sz: usize) -> Vec<u8> {
        if let Value::Sequence(SequenceData::Buffer(buffdata)) = self {
            if buffdata.data.len() <= sz {
                buffdata.data
            } else {
                error!(
                    "Value buffer has len {}, expected {}",
                    buffdata.data.len(),
                    sz
                );
                panic!();
            }
        } else {
            error!("Value '{:?}' is not a buff", &self);
            panic!();
        }
    }

    pub fn expect_list(self) -> Vec<Value> {
        if let Value::Sequence(SequenceData::List(listdata)) = self {
            listdata.data
        } else {
            error!("Value '{:?}' is not a list", &self);
            panic!();
        }
    }

    pub fn expect_buff_padded(self, sz: usize, pad: u8) -> Vec<u8> {
        let mut data = self.expect_buff(sz);
        if sz > data.len() {
            for _ in data.len()..sz {
                data.push(pad)
            }
        }
        data
    }

    pub fn expect_bool(self) -> bool {
        if let Value::Bool(b) = self {
            b
        } else {
            error!("Value '{:?}' is not a bool", &self);
            panic!();
        }
    }

    pub fn expect_tuple(self) -> TupleData {
        if let Value::Tuple(data) = self {
            data
        } else {
            error!("Value '{:?}' is not a tuple", &self);
            panic!();
        }
    }

    pub fn expect_optional(self) -> Option<Value> {
        if let Value::Optional(opt) = self {
            match opt.data {
                Some(boxed_value) => Some(*boxed_value),
                None => None,
            }
        } else {
            error!("Value '{:?}' is not an optional", &self);
            panic!();
        }
    }

    pub fn expect_principal(self) -> PrincipalData {
        if let Value::Principal(p) = self {
            p
        } else {
            error!("Value '{:?}' is not a principal", &self);
            panic!();
        }
    }

    pub fn expect_result(self) -> std::result::Result<Value, Value> {
        if let Value::Response(res_data) = self {
            if res_data.committed {
                Ok(*res_data.data)
            } else {
                Err(*res_data.data)
            }
        } else {
            error!("Value '{:?}' is not a response", &self);
            panic!();
        }
    }

    pub fn expect_result_ok(self) -> Value {
        if let Value::Response(res_data) = self {
            if res_data.committed {
                *res_data.data
            } else {
                error!("Value is not a (ok ..)");
                panic!();
            }
        } else {
            error!("Value '{:?}' is not a response", &self);
            panic!();
        }
    }

    pub fn expect_result_err(self) -> Value {
        if let Value::Response(res_data) = self {
            if !res_data.committed {
                *res_data.data
            } else {
                error!("Value is not a (err ..)");
                panic!();
            }
        } else {
            error!("Value '{:?}' is not a response", &self);
            panic!();
        }
    }
}

impl BuffData {
    pub fn len(&self) -> BufferLength {
        self.data.len().try_into().unwrap()
    }

    pub fn as_slice(&self) -> &[u8] {
        self.data.as_slice()
    }

    fn append(&mut self, other_seq: &mut BuffData) -> Result<()> {
        self.data.append(&mut other_seq.data);
        Ok(())
    }

    pub fn empty() -> Self {
        Self { data: Vec::new() }
    }
}

impl ListData {
    pub fn len(&self) -> u32 {
        self.data.len().try_into().unwrap()
    }

    fn append(&mut self, other_seq: &mut ListData) -> Result<()> {
        let entry_type_a = self.type_signature.get_list_item_type();
        let entry_type_b = other_seq.type_signature.get_list_item_type();
        let entry_type = TypeSignature::factor_out_no_type(&entry_type_a, &entry_type_b)?;
        let max_len = self.type_signature.get_max_len() + other_seq.type_signature.get_max_len();
        self.type_signature = ListTypeData::new_list(entry_type, max_len)?;
        self.data.append(&mut other_seq.data);
        Ok(())
    }
}

impl ASCIIData {
    fn append(&mut self, other_seq: &mut ASCIIData) -> Result<()> {
        self.data.append(&mut other_seq.data);
        Ok(())
    }

    pub fn len(&self) -> BufferLength {
        self.data.len().try_into().unwrap()
    }
}

impl UTF8Data {
    fn append(&mut self, other_seq: &mut UTF8Data) -> Result<()> {
        self.data.append(&mut other_seq.data);
        Ok(())
    }

    pub fn len(&self) -> BufferLength {
        self.data.len().try_into().unwrap()
    }
}

impl fmt::Display for OptionalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.data {
            Some(ref x) => write!(f, "(some {})", x),
            None => write!(f, "none"),
        }
    }
}

impl fmt::Display for ResponseData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.committed {
            true => write!(f, "(ok {})", self.data),
            false => write!(f, "(err {})", self.data),
        }
    }
}

impl fmt::Display for BuffData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", hash::to_hex(&self.data))
    }
}

impl fmt::Debug for BuffData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Int(int) => write!(f, "{}", int),
            Value::UInt(int) => write!(f, "u{}", int),
            Value::Bool(boolean) => write!(f, "{}", boolean),
            Value::Tuple(data) => write!(f, "{}", data),
            Value::Principal(principal_data) => write!(f, "{}", principal_data),
            Value::Optional(opt_data) => write!(f, "{}", opt_data),
            Value::Response(res_data) => write!(f, "{}", res_data),
            Value::Sequence(SequenceData::Buffer(vec_bytes)) => write!(f, "0x{}", &vec_bytes),
            Value::Sequence(SequenceData::String(string)) => write!(f, "{}", string),
            Value::Sequence(SequenceData::List(list_data)) => {
                write!(f, "(")?;
                for (ix, v) in list_data.data.iter().enumerate() {
                    if ix > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl PrincipalData {
    pub fn version(&self) -> u8 {
        match self {
            PrincipalData::Standard(StandardPrincipalData(version, _)) => *version,
            PrincipalData::Contract(QualifiedContractIdentifier { issuer, name: _ }) => issuer.0,
        }
    }

    pub fn parse(literal: &str) -> Result<PrincipalData> {
        // be permissive about leading single-quote
        let literal = if literal.starts_with("'") {
            &literal[1..]
        } else {
            literal
        };

        if literal.contains(".") {
            PrincipalData::parse_qualified_contract_principal(literal)
        } else {
            PrincipalData::parse_standard_principal(literal).map(PrincipalData::from)
        }
    }

    pub fn parse_qualified_contract_principal(literal: &str) -> Result<PrincipalData> {
        let contract_id = QualifiedContractIdentifier::parse(literal)?;
        Ok(PrincipalData::Contract(contract_id))
    }

    pub fn parse_standard_principal(literal: &str) -> Result<StandardPrincipalData> {
        let (version, data) = c32::c32_address_decode(&literal).map_err(|x| {
            RuntimeErrorType::ParseError(format!("Invalid principal literal: {}", x))
        })?;
        if data.len() != 20 {
            return Err(RuntimeErrorType::ParseError(
                "Invalid principal literal: Expected 20 data bytes.".to_string(),
            )
            .into());
        }
        let mut fixed_data = [0; 20];
        fixed_data.copy_from_slice(&data[..20]);
        Ok(StandardPrincipalData(version, fixed_data))
    }
}

impl StandardPrincipalData {
    pub fn to_address(&self) -> String {
        c32::c32_address(self.0, &self.1[..]).unwrap_or_else(|_| "INVALID_C32_ADD".to_string())
    }
}

impl fmt::Display for StandardPrincipalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let c32_str = self.to_address();
        write!(f, "{}", c32_str)
    }
}

impl fmt::Debug for StandardPrincipalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let c32_str = self.to_address();
        write!(f, "StandardPrincipalData({})", c32_str)
    }
}

impl fmt::Display for PrincipalData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PrincipalData::Standard(sender) => write!(f, "{}", sender),
            PrincipalData::Contract(contract_identifier) => write!(
                f,
                "{}.{}",
                contract_identifier.issuer,
                contract_identifier.name.to_string()
            ),
        }
    }
}

impl fmt::Display for TraitIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.contract_identifier, self.name.to_string())
    }
}

impl From<StandardPrincipalData> for Value {
    fn from(principal: StandardPrincipalData) -> Self {
        Value::Principal(PrincipalData::from(principal))
    }
}

impl From<QualifiedContractIdentifier> for Value {
    fn from(principal: QualifiedContractIdentifier) -> Self {
        Value::Principal(PrincipalData::Contract(principal))
    }
}

impl From<PrincipalData> for Value {
    fn from(p: PrincipalData) -> Self {
        Value::Principal(p)
    }
}

impl From<StandardPrincipalData> for PrincipalData {
    fn from(p: StandardPrincipalData) -> Self {
        PrincipalData::Standard(p)
    }
}

impl From<QualifiedContractIdentifier> for PrincipalData {
    fn from(principal: QualifiedContractIdentifier) -> Self {
        PrincipalData::Contract(principal)
    }
}

impl From<TupleData> for Value {
    fn from(t: TupleData) -> Self {
        Value::Tuple(t)
    }
}

impl TupleData {
    fn new(
        type_signature: TupleTypeSignature,
        data_map: BTreeMap<ClarityName, Value>,
    ) -> Result<TupleData> {
        let t = TupleData {
            type_signature,
            data_map,
        };
        Ok(t)
    }

    pub fn len(&self) -> u64 {
        self.data_map.len() as u64
    }

    pub fn from_data(mut data: Vec<(ClarityName, Value)>) -> Result<TupleData> {
        let mut type_map = BTreeMap::new();
        let mut data_map = BTreeMap::new();
        for (name, value) in data.drain(..) {
            let type_info = TypeSignature::type_of(&value);
            if type_map.contains_key(&name) {
                return Err(CheckErrors::NameAlreadyUsed(name.into()).into());
            } else {
                type_map.insert(name.clone(), type_info);
            }
            data_map.insert(name, value);
        }

        Self::new(TupleTypeSignature::try_from(type_map)?, data_map)
    }

    pub fn from_data_typed(
        mut data: Vec<(ClarityName, Value)>,
        expected: &TupleTypeSignature,
    ) -> Result<TupleData> {
        let mut data_map = BTreeMap::new();
        for (name, value) in data.drain(..) {
            let expected_type = expected
                .field_type(&name)
                .ok_or(InterpreterError::FailureConstructingTupleWithType)?;
            if !expected_type.admits(&value) {
                return Err(InterpreterError::FailureConstructingTupleWithType.into());
            }
            data_map.insert(name, value);
        }
        Self::new(expected.clone(), data_map)
    }

    pub fn get(&self, name: &str) -> Result<&Value> {
        self.data_map.get(name).ok_or_else(|| {
            CheckErrors::NoSuchTupleField(name.to_string(), self.type_signature.clone()).into()
        })
    }

    pub fn get_owned(mut self, name: &str) -> Result<Value> {
        self.data_map.remove(name).ok_or_else(|| {
            CheckErrors::NoSuchTupleField(name.to_string(), self.type_signature.clone()).into()
        })
    }

    pub fn shallow_merge(mut base: TupleData, updates: TupleData) -> Result<TupleData> {
        let TupleData {
            data_map,
            mut type_signature,
        } = updates;
        for (name, value) in data_map.into_iter() {
            base.data_map.insert(name, value);
        }
        base.type_signature.shallow_merge(&mut type_signature);
        Ok(base)
    }
}

impl fmt::Display for TupleData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(tuple")?;
        for (name, value) in self.data_map.iter() {
            write!(f, " ")?;
            write!(f, "({} {})", &**name, value)?;
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_constructors() {
        assert_eq!(
            Value::list_with_type(
                vec![Value::Int(5), Value::Int(2)],
                ListTypeData::new_list(TypeSignature::BoolType, 3).unwrap()
            ),
            Err(InterpreterError::FailureConstructingListWithType.into())
        );
        assert_eq!(
            ListTypeData::new_list(TypeSignature::IntType, MAX_VALUE_SIZE as u32),
            Err(CheckErrors::ValueTooLarge)
        );

        assert_eq!(
            Value::buff_from(vec![0; (MAX_VALUE_SIZE + 1) as usize]),
            Err(CheckErrors::ValueTooLarge.into())
        );

        // Test that wrappers (okay, error, some)
        //   correctly error when _they_ cause the value size
        //   to exceed the max value size (note, the buffer constructor
        //   isn't causing the error).
        assert_eq!(
            Value::okay(Value::buff_from(vec![0; (MAX_VALUE_SIZE) as usize]).unwrap()),
            Err(CheckErrors::ValueTooLarge.into())
        );

        assert_eq!(
            Value::error(Value::buff_from(vec![0; (MAX_VALUE_SIZE) as usize]).unwrap()),
            Err(CheckErrors::ValueTooLarge.into())
        );

        assert_eq!(
            Value::some(Value::buff_from(vec![0; (MAX_VALUE_SIZE) as usize]).unwrap()),
            Err(CheckErrors::ValueTooLarge.into())
        );

        // Test that the depth limit is correctly enforced:
        //   for tuples, lists, somes, okays, errors.

        let cons = || {
            Value::some(Value::some(Value::some(Value::some(Value::some(
                Value::some(Value::some(Value::some(Value::some(Value::some(
                    Value::some(Value::some(Value::some(Value::some(Value::some(
                        Value::some(Value::some(Value::some(Value::some(Value::some(
                            Value::some(Value::some(Value::some(Value::some(Value::some(
                                Value::some(Value::some(Value::some(Value::some(
                                    Value::some(Value::some(Value::Int(1))?)?,
                                )?)?)?)?,
                            )?)?)?)?)?,
                        )?)?)?)?)?,
                    )?)?)?)?)?,
                )?)?)?)?)?,
            )?)?)?)?)
        };
        let inner_value = cons().unwrap();
        assert_eq!(
            TupleData::from_data(vec![("a".into(), inner_value.clone())]),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );

        assert_eq!(
            Value::list_from(vec![inner_value.clone()]),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );
        assert_eq!(
            Value::okay(inner_value.clone()),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );
        assert_eq!(
            Value::error(inner_value.clone()),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );
        assert_eq!(
            Value::some(inner_value.clone()),
            Err(CheckErrors::TypeSignatureTooDeep.into())
        );

        if std::env::var("CIRCLE_TESTING") == Ok("1".to_string()) {
            println!("Skipping allocation test on Circle");
            return;
        }

        // on 32-bit archs, this error cannot even happen, so don't test (and cause an overflow panic)
        if (u32::max_value() as usize) < usize::max_value() {
            assert_eq!(
                Value::buff_from(vec![0; (u32::max_value() as usize) + 10]),
                Err(CheckErrors::ValueTooLarge.into())
            );
        }
    }

    #[test]
    fn simple_size_test() {
        assert_eq!(Value::Int(10).size(), 16);
    }

    #[test]
    fn simple_tuple_get_test() {
        let t = TupleData::from_data(vec![("abc".into(), Value::Int(0))]).unwrap();
        assert_eq!(t.get("abc"), Ok(&Value::Int(0)));
        // should error!
        t.get("abcd").unwrap_err();
    }

    #[test]
    fn test_some_displays() {
        assert_eq!(
            &format!(
                "{}",
                Value::list_from(vec![Value::Int(10), Value::Int(5)]).unwrap()
            ),
            "(10 5)"
        );
        assert_eq!(
            &format!("{}", Value::some(Value::Int(10)).unwrap()),
            "(some 10)"
        );
        assert_eq!(
            &format!("{}", Value::okay(Value::Int(10)).unwrap()),
            "(ok 10)"
        );
        assert_eq!(
            &format!("{}", Value::error(Value::Int(10)).unwrap()),
            "(err 10)"
        );
        assert_eq!(&format!("{}", Value::none()), "none");
        assert_eq!(
            &format!(
                "{}",
                Value::from(
                    PrincipalData::parse_standard_principal(
                        "SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G"
                    )
                    .unwrap()
                )
            ),
            "SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G"
        );

        assert_eq!(
            &format!(
                "{}",
                Value::from(TupleData::from_data(vec![("a".into(), Value::Int(2))]).unwrap())
            ),
            "(tuple (a 2))"
        );
    }

    #[test]
    fn expect_buff() {
        let buff = Value::Sequence(SequenceData::Buffer(BuffData {
            data: vec![1, 2, 3, 4, 5],
        }));
        assert_eq!(buff.clone().expect_buff(5), vec![1, 2, 3, 4, 5]);
        assert_eq!(buff.clone().expect_buff(6), vec![1, 2, 3, 4, 5]);
        assert_eq!(
            buff.clone().expect_buff_padded(6, 0),
            vec![1, 2, 3, 4, 5, 0]
        );
        assert_eq!(buff.clone().expect_buff(10), vec![1, 2, 3, 4, 5]);
        assert_eq!(
            buff.clone().expect_buff_padded(10, 1),
            vec![1, 2, 3, 4, 5, 1, 1, 1, 1, 1]
        );
    }

    #[test]
    #[should_panic]
    fn expect_buff_too_small() {
        let buff = Value::Sequence(SequenceData::Buffer(BuffData {
            data: vec![1, 2, 3, 4, 5],
        }));
        let _ = buff.expect_buff(4);
    }
}
