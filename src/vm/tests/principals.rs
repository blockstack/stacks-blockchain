use util::hash::hex_bytes;
use vm::execute_against_version_and_network;
use vm::types::BufferLength;
use vm::types::SequenceSubtype::{BufferType, StringType};
use vm::types::StringSubtype::ASCII;
use vm::types::TypeSignature::{PrincipalType, SequenceType};
use vm::types::{
    ASCIIData, BuffData, CharType, PrincipalData, SequenceData, StandardPrincipalData, Value,
};
use vm::ClarityVersion;

use crate::clarity_vm::database::MemoryBackingStore;
use std::collections::HashMap;
use vm::callables::{DefineType, DefinedFunction};
use vm::costs::LimitedCostTracker;
use vm::errors::{
    CheckErrors, Error, InterpreterError, InterpreterResult as Result, RuntimeErrorType,
};
use vm::eval;
use vm::execute;
use vm::types::{QualifiedContractIdentifier, TypeSignature};
use vm::{
    CallStack, ContractContext, Environment, GlobalContext, LocalContext, SymbolicExpression,
};

#[test]
fn test_simple_is_standard_check_inputs() {
    let wrong_type_test = "(is-standard u10)";
    assert_eq!(
        execute_against_version_and_network(wrong_type_test, ClarityVersion::Clarity2, true)
            .unwrap_err(),
        CheckErrors::TypeValueError(PrincipalType, Value::UInt(10)).into()
    );
}

#[test]
fn test_simple_is_standard_testnet_cases() {
    let testnet_addr_test = "(is-standard 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );

    let testnet_addr_test = "(is-standard 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6.tokens)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );

    let testnet_addr_test = "(is-standard 'SN2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKP6D2ZK9)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );

    let testnet_addr_test = "(is-standard 'SN2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKP6D2ZK9.tokens)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(testnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );
}

fn test_simple_is_standard_mainnet_cases() {
    let mainnet_addr_test = "(is-standard 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );

    let mainnet_addr_test = "(is-standard 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.tokens)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );

    let mainnet_addr_test = "(is-standard 'SM3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );

    let mainnet_addr_test = "(is-standard 'SM3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.tokens)";
    assert_eq!(
        Value::Bool(true),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(mainnet_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );
}

#[test]
fn test_simple_is_standard_undefined_cases() {
    // When an address is neither a testnet nor a mainnet address, the result should be false.
    let invalid_addr_test = "(is-standard 'S1G2081040G2081040G2081040G208105NK8PE5)";
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(invalid_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(invalid_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );

    let invalid_addr_test = "(is-standard 'S1G2081040G2081040G2081040G208105NK8PE5.tokens)";
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(invalid_addr_test, ClarityVersion::Clarity2, true)
            .unwrap()
            .unwrap()
    );
    assert_eq!(
        Value::Bool(false),
        execute_against_version_and_network(invalid_addr_test, ClarityVersion::Clarity2, false)
            .unwrap()
            .unwrap()
    );
}

#[test]
fn test_simple_parse_principal_version() {
    let testnet_addr_test =
        r#"(parse-principal version 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)"#;
    assert_eq!(
        Value::UInt(26),
        execute_against_version_and_network(
            testnet_addr_test,
            ClarityVersion::Clarity2,
            false
        )
        .unwrap()
        .unwrap()
    );

    let mainnet_addr_test = "(parse-principal version 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY)";
    assert_eq!(
        Value::UInt(22),
        execute_against_version_and_network(
            mainnet_addr_test,
            ClarityVersion::Clarity2,
            true
        )
        .unwrap()
        .unwrap()
    );

    // Note: Still works, even though the address is invalid.
    let invalid_addr_test = "(parse-principal version 'S1G2081040G2081040G2081040G208105NK8PE5)";
    assert_eq!(
        Value::UInt(1),
        execute_against_version_and_network(
            invalid_addr_test,
            ClarityVersion::Clarity2,
            true
        )
        .unwrap()
        .unwrap()
    );
}

#[test]
fn test_simple_parse_principal_pubkeyhash() {
    let testnet_addr_test =
        r#"(parse-principal pub-key-hash 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6)"#;
    assert_eq!(
        Value::Sequence(SequenceData::Buffer(BuffData {
            data: hex_bytes("164247d6f2b425ac5771423ae6c80c754f7172b0").unwrap()
        })),
        execute_against_version_and_network(
            testnet_addr_test,
            ClarityVersion::Clarity2,
            false
        )
        .unwrap()
        .unwrap()
    );

    let mainnet_addr_test =
        "(parse-principal pub-key-hash 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY)";
    assert_eq!(
        Value::Sequence(SequenceData::Buffer(BuffData {
            data: hex_bytes("fa6bf38ed557fe417333710d6033e9419391a320").unwrap()
        })),
        execute_against_version_and_network(
            mainnet_addr_test,
            ClarityVersion::Clarity2,
            true
        )
        .unwrap()
        .unwrap()
    );
}

#[test]
fn test_simple_assemble_principal() {
    let normal_case_test = r#"(assemble-principal u22 0xfa6bf38ed557fe417333710d6033e9419391a320)"#;
    let bytes = hex_bytes("fa6bf38ed557fe417333710d6033e9419391a320").unwrap();
    let mut transfer_buffer = [0u8; 20];
    for i in 0..bytes.len() {
        transfer_buffer[i] = bytes[i];
    }
    assert_eq!(
        Value::Principal(PrincipalData::Standard(StandardPrincipalData(
            22,
            transfer_buffer
        ))),
        execute_against_version_and_network(
            normal_case_test,
            ClarityVersion::Clarity2,
            false
        )
        .unwrap()
        .unwrap()
    );

    // The input buffer is too small.
    let too_small_test = r#"(assemble-principal u22 0x00)"#;
    assert_eq!(
        execute_against_version_and_network(
            too_small_test,
            ClarityVersion::Clarity2,
            false
        )
        .unwrap_err(),
        CheckErrors::TypeValueError(
            SequenceType(BufferType(BufferLength(20))),
            Value::Sequence(SequenceData::Buffer(BuffData { data: vec![00] }))
        )
        .into()
    );
}
