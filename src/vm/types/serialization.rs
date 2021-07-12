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

use std::borrow::Borrow;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::io::{Read, Write};
use std::{error, fmt, str};

use serde_json::Value as JSONValue;

use util::hash::{hex_bytes, to_hex};
use util::retry::BoundReader;
use vm::database::{ClarityDeserializable, ClaritySerializable};
use vm::errors::{
    CheckErrors, Error as ClarityError, IncomparableError, InterpreterError, InterpreterResult,
    RuntimeErrorType,
};
use vm::representations::{ClarityName, ContractName, MAX_STRING_LEN};
use vm::types::{
    BufferLength, CharType, OptionalData, PrincipalData, QualifiedContractIdentifier, ResponseData,
    SequenceData, SequenceSubtype, StandardPrincipalData, StringSubtype, StringUTF8Length,
    TupleData, TypeSignature, Value, BOUND_VALUE_SERIALIZATION_BYTES, MAX_VALUE_SIZE,
};

use crate::codec::{Error as codec_error, StacksMessageCodec};

/// Errors that may occur in serialization or deserialization
/// If deserialization failed because the described type is a bad type and
///   a CheckError is thrown, it gets wrapped in BadTypeError.
/// Any IOErrrors from the supplied buffer will manifest as IOError variants,
///   except for EOF -- if the deserialization code experiences an EOF, it is caught
///   and rethrown as DeserializationError
#[derive(Debug, PartialEq)]
pub enum SerializationError {
    IOError(IncomparableError<std::io::Error>),
    BadTypeError(CheckErrors),
    DeserializationError(String),
    DeserializeExpected(TypeSignature),
}

impl std::fmt::Display for SerializationError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SerializationError::IOError(e) => {
                write!(f, "Serialization error caused by IO: {}", e.err)
            }
            SerializationError::BadTypeError(e) => {
                write!(f, "Deserialization error, bad type, caused by: {}", e)
            }
            SerializationError::DeserializationError(e) => {
                write!(f, "Deserialization error: {}", e)
            }
            SerializationError::DeserializeExpected(e) => write!(
                f,
                "Deserialization expected the type of the input to be: {}",
                e
            ),
        }
    }
}

impl error::Error for SerializationError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            SerializationError::IOError(e) => Some(&e.err),
            SerializationError::BadTypeError(e) => Some(e),
            _ => None,
        }
    }
}

// Note: a byte stream that describes a longer type than
//   there are available bytes to read will result in an IOError(UnexpectedEOF)
impl From<std::io::Error> for SerializationError {
    fn from(err: std::io::Error) -> Self {
        SerializationError::IOError(IncomparableError { err })
    }
}

impl From<&str> for SerializationError {
    fn from(e: &str) -> Self {
        SerializationError::DeserializationError(e.into())
    }
}

impl From<CheckErrors> for SerializationError {
    fn from(e: CheckErrors) -> Self {
        SerializationError::BadTypeError(e)
    }
}

define_u8_enum!(TypePrefix {
    Int = 0,
    UInt = 1,
    Buffer = 2,
    BoolTrue = 3,
    BoolFalse = 4,
    PrincipalStandard = 5,
    PrincipalContract = 6,
    ResponseOk = 7,
    ResponseErr = 8,
    OptionalNone = 9,
    OptionalSome = 10,
    List = 11,
    Tuple = 12,
    StringASCII = 13,
    StringUTF8 = 14
});

impl From<&PrincipalData> for TypePrefix {
    fn from(v: &PrincipalData) -> TypePrefix {
        use super::PrincipalData::*;
        match v {
            Standard(_) => TypePrefix::PrincipalStandard,
            Contract(_) => TypePrefix::PrincipalContract,
        }
    }
}

impl From<&Value> for TypePrefix {
    fn from(v: &Value) -> TypePrefix {
        use super::CharType;
        use super::SequenceData::*;
        use super::Value::*;

        match v {
            Int(_) => TypePrefix::Int,
            UInt(_) => TypePrefix::UInt,
            Bool(value) => {
                if *value {
                    TypePrefix::BoolTrue
                } else {
                    TypePrefix::BoolFalse
                }
            }
            Principal(p) => TypePrefix::from(p),
            Response(response) => {
                if response.committed {
                    TypePrefix::ResponseOk
                } else {
                    TypePrefix::ResponseErr
                }
            }
            Optional(OptionalData { data: None }) => TypePrefix::OptionalNone,
            Optional(OptionalData { data: Some(_) }) => TypePrefix::OptionalSome,
            Tuple(_) => TypePrefix::Tuple,
            Sequence(Buffer(_)) => TypePrefix::Buffer,
            Sequence(List(_)) => TypePrefix::List,
            Sequence(String(CharType::ASCII(_))) => TypePrefix::StringASCII,
            Sequence(String(CharType::UTF8(_))) => TypePrefix::StringUTF8,
        }
    }
}

/// Not a public trait,
///   this is just used to simplify serializing some types that
///   are repeatedly serialized or deserialized.
trait ClarityValueSerializable<T: std::marker::Sized> {
    fn serialize_write<W: Write>(&self, w: &mut W) -> std::io::Result<()>;
    fn deserialize_read<R: Read>(r: &mut R) -> Result<T, SerializationError>;
}

impl ClarityValueSerializable<StandardPrincipalData> for StandardPrincipalData {
    fn serialize_write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(&[self.0])?;
        w.write_all(&self.1)
    }

    fn deserialize_read<R: Read>(r: &mut R) -> Result<Self, SerializationError> {
        let mut version = [0; 1];
        let mut data = [0; 20];
        r.read_exact(&mut version)?;
        r.read_exact(&mut data)?;
        Ok(StandardPrincipalData(version[0], data))
    }
}

macro_rules! serialize_guarded_string {
    ($Name:ident) => {
        impl ClarityValueSerializable<$Name> for $Name {
            fn serialize_write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
                w.write_all(&self.len().to_be_bytes())?;
                // self.as_bytes() is always len bytes, because this is only used for GuardedStrings
                //   which are a subset of ASCII
                w.write_all(self.as_str().as_bytes())
            }

            fn deserialize_read<R: Read>(r: &mut R) -> Result<Self, SerializationError> {
                let mut len = [0; 1];
                r.read_exact(&mut len)?;
                let len = u8::from_be_bytes(len);
                if len > MAX_STRING_LEN {
                    return Err(SerializationError::DeserializationError(
                        "String too long".to_string(),
                    ));
                }

                let mut data = vec![0; len as usize];
                r.read_exact(&mut data)?;

                String::from_utf8(data)
                    .map_err(|_| "Non-UTF8 string data".into())
                    .and_then(|x| $Name::try_from(x).map_err(|_| "Illegal Clarity string".into()))
            }
        }
    };
}

serialize_guarded_string!(ClarityName);
serialize_guarded_string!(ContractName);

impl PrincipalData {
    fn inner_consensus_serialize<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        w.write_all(&[TypePrefix::from(self) as u8])?;
        match self {
            PrincipalData::Standard(p) => p.serialize_write(w),
            PrincipalData::Contract(contract_identifier) => {
                contract_identifier.issuer.serialize_write(w)?;
                contract_identifier.name.serialize_write(w)
            }
        }
    }

    fn inner_consensus_deserialize<R: Read>(
        r: &mut R,
    ) -> Result<PrincipalData, SerializationError> {
        let mut header = [0];
        r.read_exact(&mut header)?;

        let prefix = TypePrefix::from_u8(header[0]).ok_or_else(|| "Bad principal prefix")?;

        match prefix {
            TypePrefix::PrincipalStandard => {
                StandardPrincipalData::deserialize_read(r).map(PrincipalData::from)
            }
            TypePrefix::PrincipalContract => {
                let issuer = StandardPrincipalData::deserialize_read(r)?;
                let name = ContractName::deserialize_read(r)?;
                Ok(PrincipalData::from(QualifiedContractIdentifier {
                    issuer,
                    name,
                }))
            }
            _ => Err("Bad principal prefix".into()),
        }
    }
}

impl StacksMessageCodec for PrincipalData {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), codec_error> {
        self.inner_consensus_serialize(fd)
            .map_err(codec_error::WriteError)
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<PrincipalData, codec_error> {
        PrincipalData::inner_consensus_deserialize(fd)
            .map_err(|e| codec_error::DeserializeError(e.to_string()))
    }
}

macro_rules! check_match {
    ($item:expr, $Pattern:pat) => {
        match $item {
            None => Ok(()),
            Some($Pattern) => Ok(()),
            Some(x) => Err(SerializationError::DeserializeExpected(x.clone())),
        }
    };
}

impl Value {
    pub fn deserialize_read<R: Read>(
        r: &mut R,
        expected_type: Option<&TypeSignature>,
    ) -> Result<Value, SerializationError> {
        let mut bound_reader = BoundReader::from_reader(r, BOUND_VALUE_SERIALIZATION_BYTES as u64);
        Value::inner_deserialize_read(&mut bound_reader, expected_type, 0)
    }

    fn inner_deserialize_read<R: Read>(
        r: &mut R,
        expected_type: Option<&TypeSignature>,
        depth: u8,
    ) -> Result<Value, SerializationError> {
        use super::PrincipalData::*;
        use super::Value::*;

        if depth >= 16 {
            return Err(CheckErrors::TypeSignatureTooDeep.into());
        }

        let mut header = [0];
        r.read_exact(&mut header)?;

        let prefix = TypePrefix::from_u8(header[0]).ok_or_else(|| "Bad type prefix")?;

        match prefix {
            TypePrefix::Int => {
                check_match!(expected_type, TypeSignature::IntType)?;
                let mut buffer = [0; 16];
                r.read_exact(&mut buffer)?;
                Ok(Int(i128::from_be_bytes(buffer)))
            }
            TypePrefix::UInt => {
                check_match!(expected_type, TypeSignature::UIntType)?;
                let mut buffer = [0; 16];
                r.read_exact(&mut buffer)?;
                Ok(UInt(u128::from_be_bytes(buffer)))
            }
            TypePrefix::Buffer => {
                let mut buffer_len = [0; 4];
                r.read_exact(&mut buffer_len)?;
                let buffer_len = BufferLength::try_from(u32::from_be_bytes(buffer_len))?;

                if let Some(x) = expected_type {
                    let passed_test = match x {
                        TypeSignature::SequenceType(SequenceSubtype::BufferType(expected_len)) => {
                            u32::from(&buffer_len) <= u32::from(expected_len)
                        }
                        _ => false,
                    };
                    if !passed_test {
                        return Err(SerializationError::DeserializeExpected(x.clone()));
                    }
                }

                let mut data = vec![0; u32::from(buffer_len) as usize];

                r.read_exact(&mut data[..])?;

                Value::buff_from(data).map_err(|_| "Bad buffer".into())
            }
            TypePrefix::BoolTrue => {
                check_match!(expected_type, TypeSignature::BoolType)?;
                Ok(Bool(true))
            }
            TypePrefix::BoolFalse => {
                check_match!(expected_type, TypeSignature::BoolType)?;
                Ok(Bool(false))
            }
            TypePrefix::PrincipalStandard => {
                check_match!(expected_type, TypeSignature::PrincipalType)?;
                StandardPrincipalData::deserialize_read(r).map(Value::from)
            }
            TypePrefix::PrincipalContract => {
                check_match!(expected_type, TypeSignature::PrincipalType)?;
                let issuer = StandardPrincipalData::deserialize_read(r)?;
                let name = ContractName::deserialize_read(r)?;
                Ok(Value::from(QualifiedContractIdentifier { issuer, name }))
            }
            TypePrefix::ResponseOk | TypePrefix::ResponseErr => {
                let committed = prefix == TypePrefix::ResponseOk;

                let expect_contained_type = match expected_type {
                    None => None,
                    Some(x) => {
                        let contained_type = match (committed, x) {
                            (true, TypeSignature::ResponseType(types)) => Ok(&types.0),
                            (false, TypeSignature::ResponseType(types)) => Ok(&types.1),
                            _ => Err(SerializationError::DeserializeExpected(x.clone())),
                        }?;
                        Some(contained_type)
                    }
                };

                let data = Value::inner_deserialize_read(r, expect_contained_type, depth + 1)?;
                let value = if committed {
                    Value::okay(data)
                } else {
                    Value::error(data)
                }
                .map_err(|_x| "Value too large")?;

                Ok(value)
            }
            TypePrefix::OptionalNone => {
                check_match!(expected_type, TypeSignature::OptionalType(_))?;
                Ok(Value::none())
            }
            TypePrefix::OptionalSome => {
                let expect_contained_type = match expected_type {
                    None => None,
                    Some(x) => {
                        let contained_type = match x {
                            TypeSignature::OptionalType(some_type) => Ok(some_type.as_ref()),
                            _ => Err(SerializationError::DeserializeExpected(x.clone())),
                        }?;
                        Some(contained_type)
                    }
                };

                let value = Value::some(Value::inner_deserialize_read(
                    r,
                    expect_contained_type,
                    depth + 1,
                )?)
                .map_err(|_x| "Value too large")?;

                Ok(value)
            }
            TypePrefix::List => {
                let mut len = [0; 4];
                r.read_exact(&mut len)?;
                let len = u32::from_be_bytes(len);

                if len > MAX_VALUE_SIZE {
                    return Err("Illegal list type".into());
                }

                let (list_type, entry_type) = match expected_type {
                    None => (None, None),
                    Some(TypeSignature::SequenceType(SequenceSubtype::ListType(list_type))) => {
                        if len > list_type.get_max_len() {
                            return Err(SerializationError::DeserializeExpected(
                                expected_type.unwrap().clone(),
                            ));
                        }
                        (Some(list_type), Some(list_type.get_list_item_type()))
                    }
                    Some(x) => return Err(SerializationError::DeserializeExpected(x.clone())),
                };

                let mut items = Vec::with_capacity(len as usize);
                for _i in 0..len {
                    items.push(Value::inner_deserialize_read(r, entry_type, depth + 1)?);
                }

                if let Some(list_type) = list_type {
                    Value::list_with_type(items, list_type.clone())
                        .map_err(|_| "Illegal list type".into())
                } else {
                    Value::list_from(items).map_err(|_| "Illegal list type".into())
                }
            }
            TypePrefix::Tuple => {
                let mut len = [0; 4];
                r.read_exact(&mut len)?;
                let len = u32::from_be_bytes(len);

                if len > MAX_VALUE_SIZE {
                    return Err(SerializationError::DeserializationError(
                        "Illegal tuple type".to_string(),
                    ));
                }

                let tuple_type = match expected_type {
                    None => None,
                    Some(TypeSignature::TupleType(tuple_type)) => {
                        if len as u64 != tuple_type.len() {
                            return Err(SerializationError::DeserializeExpected(
                                expected_type.unwrap().clone(),
                            ));
                        }
                        Some(tuple_type)
                    }
                    Some(x) => return Err(SerializationError::DeserializeExpected(x.clone())),
                };

                let mut items = Vec::with_capacity(len as usize);
                for _i in 0..len {
                    let key = ClarityName::deserialize_read(r)?;

                    let expected_field_type = match tuple_type {
                        None => None,
                        Some(some_tuple) => Some(some_tuple.field_type(&key).ok_or_else(|| {
                            SerializationError::DeserializeExpected(expected_type.unwrap().clone())
                        })?),
                    };

                    let value = Value::inner_deserialize_read(r, expected_field_type, depth + 1)?;
                    items.push((key, value))
                }

                if let Some(tuple_type) = tuple_type {
                    TupleData::from_data_typed(items, tuple_type)
                        .map_err(|_| "Illegal tuple type".into())
                        .map(Value::from)
                } else {
                    TupleData::from_data(items)
                        .map_err(|_| "Illegal tuple type".into())
                        .map(Value::from)
                }
            }
            TypePrefix::StringASCII => {
                let mut buffer_len = [0; 4];
                r.read_exact(&mut buffer_len)?;
                let buffer_len = BufferLength::try_from(u32::from_be_bytes(buffer_len))?;

                if let Some(x) = expected_type {
                    let passed_test = match x {
                        TypeSignature::SequenceType(SequenceSubtype::StringType(
                            StringSubtype::ASCII(expected_len),
                        )) => u32::from(&buffer_len) <= u32::from(expected_len),
                        _ => false,
                    };
                    if !passed_test {
                        return Err(SerializationError::DeserializeExpected(x.clone()));
                    }
                }

                let mut data = vec![0; u32::from(buffer_len) as usize];

                r.read_exact(&mut data[..])?;

                Value::string_ascii_from_bytes(data).map_err(|_| "Bad string".into())
            }
            TypePrefix::StringUTF8 => {
                let mut total_len = [0; 4];
                r.read_exact(&mut total_len)?;
                let total_len = BufferLength::try_from(u32::from_be_bytes(total_len))?;

                let mut data: Vec<u8> = vec![0; u32::from(total_len) as usize];

                r.read_exact(&mut data[..])?;

                let value = Value::string_utf8_from_bytes(data)
                    .map_err(|_| "Illegal string_utf8 type".into());

                if let Some(x) = expected_type {
                    let passed_test = match (x, &value) {
                        (
                            TypeSignature::SequenceType(SequenceSubtype::StringType(
                                StringSubtype::UTF8(expected_len),
                            )),
                            Ok(Value::Sequence(SequenceData::String(CharType::UTF8(utf8)))),
                        ) => utf8.data.len() as u32 <= u32::from(expected_len),
                        _ => false,
                    };
                    if !passed_test {
                        return Err(SerializationError::DeserializeExpected(x.clone()));
                    }
                }

                value
            }
        }
    }

    pub fn serialize_write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        use super::CharType::*;
        use super::PrincipalData::*;
        use super::SequenceData::{self, *};
        use super::Value::*;

        w.write_all(&[TypePrefix::from(self) as u8])?;
        match self {
            Int(value) => w.write_all(&value.to_be_bytes())?,
            UInt(value) => w.write_all(&value.to_be_bytes())?,
            Principal(Standard(data)) => data.serialize_write(w)?,
            Principal(Contract(contract_identifier)) => {
                contract_identifier.issuer.serialize_write(w)?;
                contract_identifier.name.serialize_write(w)?;
            }
            Response(response) => response.data.serialize_write(w)?,
            // Bool types don't need any more data.
            Bool(_) => {}
            // None types don't need any more data.
            Optional(OptionalData { data: None }) => {}
            Optional(OptionalData { data: Some(value) }) => {
                value.serialize_write(w)?;
            }
            Sequence(List(data)) => {
                w.write_all(&data.len().to_be_bytes())?;
                for item in data.data.iter() {
                    item.serialize_write(w)?;
                }
            }
            Sequence(Buffer(value)) => {
                w.write_all(&(u32::from(value.len()).to_be_bytes()))?;
                w.write_all(&value.data)?
            }
            Sequence(SequenceData::String(UTF8(value))) => {
                let total_len: u32 = value.data.iter().fold(0u32, |len, c| len + c.len() as u32);
                w.write_all(&(total_len.to_be_bytes()))?;
                for bytes in value.data.iter() {
                    w.write_all(&bytes)?
                }
            }
            Sequence(SequenceData::String(ASCII(value))) => {
                w.write_all(&(u32::from(value.len()).to_be_bytes()))?;
                w.write_all(&value.data)?
            }
            Tuple(data) => {
                w.write_all(&u32::try_from(data.data_map.len()).unwrap().to_be_bytes())?;
                for (key, value) in data.data_map.iter() {
                    key.serialize_write(w)?;
                    value.serialize_write(w)?;
                }
            }
        };

        Ok(())
    }

    /// This function attempts to deserialize a hex string into a Clarity Value.
    ///   The `expected_type` parameter determines whether or not the deserializer should expect (and enforce)
    ///   a particular type. `ClarityDB` uses this to ensure that lists, tuples, etc. loaded from the database
    ///   have their max-length and other type information set by the type declarations in the contract.
    ///   If passed `None`, the deserializer will construct the values as if they were literals in the contract, e.g.,
    ///     list max length = the length of the list.

    pub fn try_deserialize_bytes(
        bytes: &Vec<u8>,
        expected: &TypeSignature,
    ) -> Result<Value, SerializationError> {
        Value::deserialize_read(&mut bytes.as_slice(), Some(expected))
    }

    pub fn try_deserialize_hex(
        hex: &str,
        expected: &TypeSignature,
    ) -> Result<Value, SerializationError> {
        let mut data = hex_bytes(hex).map_err(|_| "Bad hex string")?;
        Value::try_deserialize_bytes(&mut data, expected)
    }

    pub fn try_deserialize_bytes_untyped(bytes: &Vec<u8>) -> Result<Value, SerializationError> {
        Value::deserialize_read(&mut bytes.as_slice(), None)
    }

    pub fn try_deserialize_hex_untyped(hex: &str) -> Result<Value, SerializationError> {
        let hex = if hex.starts_with("0x") {
            &hex[2..]
        } else {
            &hex
        };
        let mut data = hex_bytes(hex).map_err(|_| "Bad hex string")?;
        Value::try_deserialize_bytes_untyped(&mut data)
    }

    pub fn deserialize(hex: &str, expected: &TypeSignature) -> Self {
        Value::try_deserialize_hex(hex, expected)
            .expect("ERROR: Failed to parse Clarity hex string")
    }
}

impl ClaritySerializable for Value {
    fn serialize(&self) -> String {
        let mut byte_serialization = Vec::new();
        self.serialize_write(&mut byte_serialization)
            .expect("IOError filling byte buffer.");
        to_hex(byte_serialization.as_slice())
    }
}

impl ClarityDeserializable<Value> for Value {
    fn deserialize(hex: &str) -> Self {
        Value::try_deserialize_hex_untyped(hex).expect("ERROR: Failed to parse Clarity hex string")
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use vm::database::ClaritySerializable;
    use vm::errors::Error;
    use vm::types::TypeSignature::{BoolType, IntType};

    use super::super::*;
    use super::SerializationError;

    fn buff_type(size: u32) -> TypeSignature {
        TypeSignature::SequenceType(SequenceSubtype::BufferType(size.try_into().unwrap())).into()
    }

    fn test_deser_ser(v: Value) {
        assert_eq!(
            &v,
            &Value::deserialize(&v.serialize(), &TypeSignature::type_of(&v))
        );
        assert_eq!(
            &v,
            &Value::try_deserialize_hex_untyped(&v.serialize()).unwrap()
        );
    }

    fn test_bad_expectation(v: Value, e: TypeSignature) {
        assert!(
            match Value::try_deserialize_hex(&v.serialize(), &e).unwrap_err() {
                SerializationError::DeserializeExpected(_) => true,
                _ => false,
            }
        )
    }

    #[test]
    fn test_lists() {
        let list_list_int = Value::list_from(vec![Value::list_from(vec![
            Value::Int(1),
            Value::Int(2),
            Value::Int(3),
        ])
        .unwrap()])
        .unwrap();

        // Should be legal!
        Value::try_deserialize_hex(
            &Value::list_from(vec![]).unwrap().serialize(),
            &TypeSignature::from("(list 2 (list 3 int))"),
        )
        .unwrap();
        Value::try_deserialize_hex(
            &list_list_int.serialize(),
            &TypeSignature::from("(list 2 (list 3 int))"),
        )
        .unwrap();
        Value::try_deserialize_hex(
            &list_list_int.serialize(),
            &TypeSignature::from("(list 1 (list 4 int))"),
        )
        .unwrap();

        test_deser_ser(list_list_int.clone());
        test_deser_ser(Value::list_from(vec![]).unwrap());
        test_bad_expectation(list_list_int.clone(), TypeSignature::BoolType);
        // inner type isn't expected
        test_bad_expectation(
            list_list_int.clone(),
            TypeSignature::from("(list 1 (list 4 uint))"),
        );
        // child list longer than expected
        test_bad_expectation(
            list_list_int.clone(),
            TypeSignature::from("(list 1 (list 2 uint))"),
        );
        // parent list longer than expected
        test_bad_expectation(
            list_list_int.clone(),
            TypeSignature::from("(list 0 (list 2 uint))"),
        );

        // make a list too large for the type itself!
        //   this describes a list of size 1+MAX_VALUE_SIZE of Value::Bool(true)'s
        let mut too_big = vec![3u8; 6 + MAX_VALUE_SIZE as usize];
        // list prefix
        too_big[0] = 11;
        // list length
        Write::write_all(
            &mut too_big.get_mut(1..5).unwrap(),
            &(1 + MAX_VALUE_SIZE).to_be_bytes(),
        )
        .unwrap();

        assert_eq!(
            Value::deserialize_read(&mut too_big.as_slice(), None).unwrap_err(),
            "Illegal list type".into()
        );

        // make a list that says it is longer than it is!
        //   this describes a list of size MAX_VALUE_SIZE of Value::Bool(true)'s, but is actually only 59 bools.
        let mut eof = vec![3u8; 64 as usize];
        // list prefix
        eof[0] = 11;
        // list length
        Write::write_all(
            &mut eof.get_mut(1..5).unwrap(),
            &(MAX_VALUE_SIZE).to_be_bytes(),
        )
        .unwrap();

        /*
         * jude -- this should return an IOError
        assert_eq!(
            Value::deserialize_read(&mut eof.as_slice(), None).unwrap_err(),
            "Unexpected end of byte stream".into());
        */

        match Value::deserialize_read(&mut eof.as_slice(), None) {
            Ok(_) => assert!(false, "Accidentally parsed truncated slice"),
            Err(eres) => match eres {
                SerializationError::IOError(ioe) => match ioe.err.kind() {
                    std::io::ErrorKind::UnexpectedEof => {}
                    _ => assert!(false, "Invalid I/O error: {:?}", &ioe),
                },
                _ => assert!(false, "Invalid deserialize error: {:?}", &eres),
            },
        }
    }

    #[test]
    fn test_bools() {
        test_deser_ser(Value::Bool(false));
        test_deser_ser(Value::Bool(true));

        test_bad_expectation(Value::Bool(false), TypeSignature::IntType);
        test_bad_expectation(Value::Bool(true), TypeSignature::IntType);
    }

    #[test]
    fn test_ints() {
        test_deser_ser(Value::Int(0));
        test_deser_ser(Value::Int(1));
        test_deser_ser(Value::Int(-1));
        test_deser_ser(Value::Int(i128::max_value()));
        test_deser_ser(Value::Int(i128::min_value()));

        test_bad_expectation(Value::Int(1), TypeSignature::UIntType);
    }

    #[test]
    fn test_uints() {
        test_deser_ser(Value::UInt(0));
        test_deser_ser(Value::UInt(1));
        test_deser_ser(Value::UInt(u128::max_value()));
        test_deser_ser(Value::UInt(u128::min_value()));

        test_bad_expectation(Value::UInt(1), TypeSignature::IntType);
    }

    #[test]
    fn test_opts() {
        test_deser_ser(Value::none());
        test_deser_ser(Value::some(Value::Int(15)).unwrap());

        test_bad_expectation(Value::none(), TypeSignature::IntType);
        test_bad_expectation(Value::some(Value::Int(15)).unwrap(), TypeSignature::IntType);
        // bad expected _contained_ type
        test_bad_expectation(
            Value::some(Value::Int(15)).unwrap(),
            TypeSignature::from("(optional uint)"),
        );
    }

    #[test]
    fn test_resp() {
        test_deser_ser(Value::okay(Value::Int(15)).unwrap());
        test_deser_ser(Value::error(Value::Int(15)).unwrap());

        // Bad expected types.
        test_bad_expectation(Value::okay(Value::Int(15)).unwrap(), TypeSignature::IntType);
        test_bad_expectation(
            Value::okay(Value::Int(15)).unwrap(),
            TypeSignature::from("(response uint int)"),
        );
        test_bad_expectation(
            Value::error(Value::Int(15)).unwrap(),
            TypeSignature::from("(response int uint)"),
        );
    }

    #[test]
    fn test_buffs() {
        test_deser_ser(Value::buff_from(vec![0, 0, 0, 0]).unwrap());
        test_deser_ser(Value::buff_from(vec![0xde, 0xad, 0xbe, 0xef]).unwrap());
        test_deser_ser(Value::buff_from(vec![0, 0xde, 0xad, 0xbe, 0xef, 0]).unwrap());

        test_bad_expectation(
            Value::buff_from(vec![0, 0xde, 0xad, 0xbe, 0xef, 0]).unwrap(),
            TypeSignature::BoolType,
        );

        // fail because we expect a shorter buffer
        test_bad_expectation(
            Value::buff_from(vec![0, 0xde, 0xad, 0xbe, 0xef, 0]).unwrap(),
            TypeSignature::from("(buff 2)"),
        );
    }

    #[test]
    fn test_string_ascii() {
        test_deser_ser(Value::string_ascii_from_bytes(vec![61, 62, 63, 64]).unwrap());

        // fail because we expect a shorter string
        test_bad_expectation(
            Value::string_ascii_from_bytes(vec![61, 62, 63, 64]).unwrap(),
            TypeSignature::from("(string-ascii 3)"),
        );
    }

    #[test]
    fn test_string_utf8() {
        test_deser_ser(Value::string_utf8_from_bytes(vec![61, 62, 63, 64]).unwrap());
        test_deser_ser(
            Value::string_utf8_from_bytes(vec![61, 62, 63, 240, 159, 164, 151]).unwrap(),
        );

        // fail because we expect a shorter string
        test_bad_expectation(
            Value::string_utf8_from_bytes(vec![61, 62, 63, 64]).unwrap(),
            TypeSignature::from("(string-utf8 3)"),
        );

        test_bad_expectation(
            Value::string_utf8_from_bytes(vec![61, 62, 63, 240, 159, 164, 151]).unwrap(),
            TypeSignature::from("(string-utf8 3)"),
        );
    }

    #[test]
    fn test_tuples() {
        let t_1 = Value::from(
            TupleData::from_data(vec![
                ("a".into(), Value::Int(1)),
                ("b".into(), Value::Int(1)),
            ])
            .unwrap(),
        );
        let t_0 = Value::from(
            TupleData::from_data(vec![
                ("b".into(), Value::Int(1)),
                ("a".into(), Value::Int(1)),
            ])
            .unwrap(),
        );
        let t_2 = Value::from(
            TupleData::from_data(vec![
                ("a".into(), Value::Int(1)),
                ("b".into(), Value::Bool(true)),
            ])
            .unwrap(),
        );
        let t_3 = Value::from(TupleData::from_data(vec![("a".into(), Value::Int(1))]).unwrap());
        let t_4 = Value::from(
            TupleData::from_data(vec![
                ("a".into(), Value::Int(1)),
                ("c".into(), Value::Bool(true)),
            ])
            .unwrap(),
        );

        test_deser_ser(t_0.clone());
        test_deser_ser(t_1.clone());
        test_deser_ser(t_2.clone());
        test_deser_ser(t_3.clone());

        test_bad_expectation(t_0.clone(), TypeSignature::BoolType);

        // t_0 and t_1 are actually the same
        assert_eq!(
            Value::try_deserialize_hex(&t_1.serialize(), &TypeSignature::type_of(&t_0)).unwrap(),
            Value::try_deserialize_hex(&t_0.serialize(), &TypeSignature::type_of(&t_0)).unwrap()
        );

        // field number not equal to expectations
        assert!(
            match Value::try_deserialize_hex(&t_3.serialize(), &TypeSignature::type_of(&t_1))
                .unwrap_err()
            {
                SerializationError::DeserializeExpected(_) => true,
                _ => false,
            }
        );

        // field type mismatch
        assert!(
            match Value::try_deserialize_hex(&t_2.serialize(), &TypeSignature::type_of(&t_1))
                .unwrap_err()
            {
                SerializationError::DeserializeExpected(_) => true,
                _ => false,
            }
        );

        // field not-present in expected
        assert!(
            match Value::try_deserialize_hex(&t_1.serialize(), &TypeSignature::type_of(&t_4))
                .unwrap_err()
            {
                SerializationError::DeserializeExpected(_) => true,
                _ => false,
            }
        );
    }

    #[test]
    fn test_vectors() {
        let tests = [
            ("1010", Err("Bad type prefix".into())),
            ("0000000000000000000000000000000001", Ok(Value::Int(1))),
            ("00ffffffffffffffffffffffffffffffff", Ok(Value::Int(-1))),
            ("0100000000000000000000000000000001", Ok(Value::UInt(1))),
            ("0200000004deadbeef", Ok(Value::buff_from(vec![0xde, 0xad, 0xbe, 0xef])
                                      .unwrap())),
            ("03", Ok(Value::Bool(true))),
            ("04", Ok(Value::Bool(false))),
            ("050011deadbeef11ababffff11deadbeef11ababffff", Ok(
                StandardPrincipalData(
                    0x00,
                    [0x11, 0xde, 0xad, 0xbe, 0xef, 0x11, 0xab, 0xab, 0xff, 0xff,
                     0x11, 0xde, 0xad, 0xbe, 0xef, 0x11, 0xab, 0xab, 0xff, 0xff]).into())),
            ("060011deadbeef11ababffff11deadbeef11ababffff0461626364", Ok(
                QualifiedContractIdentifier::new(
                    StandardPrincipalData(
                        0x00,
                        [0x11, 0xde, 0xad, 0xbe, 0xef, 0x11, 0xab, 0xab, 0xff, 0xff,
                         0x11, 0xde, 0xad, 0xbe, 0xef, 0x11, 0xab, 0xab, 0xff, 0xff]),
                    "abcd".into()).into())),
            ("0700ffffffffffffffffffffffffffffffff", Ok(Value::okay(Value::Int(-1)).unwrap())),
            ("0800ffffffffffffffffffffffffffffffff", Ok(Value::error(Value::Int(-1)).unwrap())),
            ("09", Ok(Value::none())),
            ("0a00ffffffffffffffffffffffffffffffff", Ok(Value::some(Value::Int(-1)).unwrap())),
            ("0b0000000400000000000000000000000000000000010000000000000000000000000000000002000000000000000000000000000000000300fffffffffffffffffffffffffffffffc",
             Ok(Value::list_from(vec![
                 Value::Int(1), Value::Int(2), Value::Int(3), Value::Int(-4)]).unwrap())),
            ("0c000000020362617a0906666f6f62617203",
             Ok(Value::from(TupleData::from_data(vec![
                 ("baz".into(), Value::none()), ("foobar".into(), Value::Bool(true))]).unwrap())))
        ];

        for (test, expected) in tests.iter() {
            if let Ok(x) = expected {
                assert_eq!(test, &x.serialize());
            }
            assert_eq!(expected, &Value::try_deserialize_hex_untyped(test));
            assert_eq!(
                expected,
                &Value::try_deserialize_hex_untyped(&format!("0x{}", test))
            );
        }
    }

    #[test]
    fn try_deser_large_list() {
        let buff = vec![
            11, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        ];

        assert_eq!(
            Value::try_deserialize_bytes_untyped(&buff).unwrap_err(),
            SerializationError::DeserializationError("Illegal list type".to_string())
        );
    }

    #[test]
    fn try_deser_large_tuple() {
        let buff = vec![
            12, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        ];

        assert_eq!(
            Value::try_deserialize_bytes_untyped(&buff).unwrap_err(),
            SerializationError::DeserializationError("Illegal tuple type".to_string())
        );
    }

    #[test]
    fn try_overflow_stack() {
        let input = "08080808080808080808070707080807080808080808080708080808080708080707080707080807080808080808080708080808080708080707080708070807080808080808080708080808080708080708080808080808080807070807080808080808070808070707080807070808070808080808070808070708070807080808080808080707080708070807080708080808080808070808080808070808070808080808080808080707080708080808080807080807070708080707080807080808080807080807070807080708080808080808070708070808080808080708080707070808070708080807080807070708";
        assert_eq!(
            Err(CheckErrors::TypeSignatureTooDeep.into()),
            Value::try_deserialize_hex_untyped(input)
        );
    }

    #[test]
    fn test_principals() {
        let issuer =
            PrincipalData::parse_standard_principal("SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G")
                .unwrap();
        let standard_p = Value::from(issuer.clone());

        let contract_identifier = QualifiedContractIdentifier::new(issuer, "foo".into());
        let contract_p2 = Value::from(PrincipalData::Contract(contract_identifier));

        test_deser_ser(contract_p2.clone());
        test_deser_ser(standard_p.clone());

        test_bad_expectation(contract_p2, TypeSignature::BoolType);
        test_bad_expectation(standard_p, TypeSignature::BoolType);
    }
}
