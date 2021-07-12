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

use std::collections::HashMap;

use address::c32;
use address::AddressHashMode;
use chainstate::stacks::StacksPrivateKey;
use chainstate::stacks::StacksPublicKey;
use util::hash::{hex_bytes, to_hex};
use vm::ast::parse;
use vm::callables::DefinedFunction;
use vm::contexts::OwnedEnvironment;
use vm::costs::LimitedCostTracker;
use vm::errors::{CheckErrors, Error, RuntimeErrorType, ShortReturnType};
use vm::tests::execute;
use vm::types::signatures::*;
use vm::types::{BuffData, QualifiedContractIdentifier, TypeSignature};
use vm::types::{PrincipalData, ResponseData, SequenceData, SequenceSubtype};
use vm::{eval, execute as vm_execute};
use vm::{CallStack, ContractContext, Environment, GlobalContext, LocalContext, Value};

use crate::clarity_vm::database::MemoryBackingStore;
use crate::types::chainstate::StacksAddress;
use chainstate::stacks::C32_ADDRESS_VERSION_TESTNET_SINGLESIG;

#[test]
fn test_doubly_defined_persisted_vars() {
    let tests = [
        "(define-non-fungible-token cursor uint) (define-non-fungible-token cursor uint)",
        "(define-fungible-token cursor) (define-fungible-token cursor)",
        "(define-data-var cursor int 0) (define-data-var cursor int 0)",
        "(define-map cursor { cursor: int } { place: uint }) (define-map cursor { cursor: int } { place: uint })" ];
    for p in tests.iter() {
        assert_eq!(
            vm_execute(p).unwrap_err(),
            CheckErrors::NameAlreadyUsed("cursor".into()).into()
        );
    }
}

#[test]
fn test_simple_let() {
    /*
      test program:
      (let ((x 1) (y 2))
        (+ x
           (let ((x 3))
                 (+ x y))
           x))
    */

    let program = "(let ((x 1) (y 2))
                     (+ x
                        (let ((z 3))
                             (+ z y))
                        x))";
    let contract_id = QualifiedContractIdentifier::transient();
    if let Ok(parsed_program) = parse(&contract_id, &program) {
        let context = LocalContext::new();
        let mut marf = MemoryBackingStore::new();
        let mut env = OwnedEnvironment::new(marf.as_clarity_db());

        assert_eq!(
            Ok(Value::Int(7)),
            eval(
                &parsed_program[0],
                &mut env.get_exec_environment(None),
                &context
            )
        );
    } else {
        assert!(false, "Failed to parse program.");
    }
}

#[test]
fn test_sha256() {
    let sha256_evals = [
        "(sha256 0x)",
        "(sha256 0)",
        "(sha256 0x54686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67)", // The quick brown fox jumps over the lazy dog
    ];

    fn to_buffer(hex: &str) -> Value {
        return Value::Sequence(SequenceData::Buffer(BuffData {
            data: hex_bytes(hex).unwrap(),
        }));
    }

    let expectations = [
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "374708fff7719dd5979ec875d56cd2286f6d3cf7ec317a3b25632aab28ec37bb",
        "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592",
    ];

    sha256_evals
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(to_buffer(expectation), execute(program)));
}

#[test]
fn test_sha512() {
    let sha512_evals = [
        "(sha512 0x)",
        "(sha512 0)",
        "(sha512 0x54686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67)", // The quick brown fox jumps over the lazy dog
    ];

    fn p_to_hex(val: Value) -> String {
        match val {
            Value::Sequence(SequenceData::Buffer(BuffData { data })) => to_hex(&data),
            _ => panic!("Failed"),
        }
    }

    let expectations = [
        "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
        "0b6cbac838dfe7f47ea1bd0df00ec282fdf45510c92161072ccfb84035390c4da743d9c3b954eaa1b0f86fc9861b23cc6c8667ab232c11c686432ebb5c8c3f27",
        "07e547d9586f6a73f73fbac0435ed76951218fb7d0c8d788a309d785436bbb642e93a252a954f23912547d1e8a3b5ed6e1bfd7097821233fa0538f3db854fee6"
    ];

    sha512_evals
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation, &p_to_hex(execute(program))));
}

#[test]
fn test_sha512trunc256() {
    let sha512_evals = [
        "(sha512/256 0x)",
        "(sha512/256 0)",
        "(sha512/256 0x54686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67)", // The quick brown fox jumps over the lazy dog
    ];

    fn p_to_hex(val: Value) -> String {
        match val {
            Value::Sequence(SequenceData::Buffer(BuffData { data })) => to_hex(&data),
            _ => panic!("Failed"),
        }
    }

    let expectations = [
        "c672b8d1ef56ed28ab87c3622c5114069bdd3ad7b8f9737498d0c01ecef0967a",
        "e41c9660b04714cdf7249f0fd6e6c5556f54a7e04d299958b69a877e0fada2fb",
        "dd9d67b371519c339ed8dbd25af90e976a1eeefd4ad3d889005e532fc5bef04d",
    ];

    sha512_evals
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation, &p_to_hex(execute(program))));
}

#[test]
fn test_keccak256() {
    let keccak256_evals = [
        "(keccak256 0x)",
        "(keccak256 0)",
        "(keccak256 0x54686520717569636b2062726f776e20666f78206a756d7073206f76657220746865206c617a7920646f67)", // The quick brown fox jumps over the lazy dog
    ];

    fn to_buffer(hex: &str) -> Value {
        return Value::Sequence(SequenceData::Buffer(BuffData {
            data: hex_bytes(hex).unwrap(),
        }));
    }

    let expectations = [
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
        "f490de2920c8a35fabeb13208852aa28c76f9be9b03a4dd2b3c075f7a26923b4",
        "4d741b6f1eb29cb2a9b9911c82f56fa8d73b04959d3d9d222895df6c0b28aa15",
    ];

    keccak256_evals
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(to_buffer(expectation), execute(program)));
}

#[test]
fn test_secp256k1() {
    let secp256k1_evals = [
        "(unwrap! (secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301) 2)",
        "(unwrap-err! (secp256k1-recover? 0x0000000000000000000000000000000000000000000000000000000000000000 0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) 3)",
        "(unwrap-err! (secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1306) 3)",
        "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a13 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        "(secp256k1-verify 0x0000000000000000000000000000000000000000000000000000000000000000 0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1305 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        "(unwrap! (principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110) 4)", // (buff 33)
        "(unwrap-err! (principal-of? 0x000000000000000000000000000000000000000000000000000000000000000000) 3)",
    ];

    let privk = StacksPrivateKey::from_hex(
        "510f96a8efd0b11e211733c1ac5e3fa6f3d3fcdd62869e376c47decb3e14fea101",
    )
    .unwrap(); // need the "compressed extra 0x01 to match, as this changes the address"
    eprintln!("privk {:?}", &privk);
    eprintln!("from_private {:?}", &StacksPublicKey::from_private(&privk));
    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_private(&privk)],
    )
    .unwrap();
    eprintln!("addr from privk {:?}", &addr);
    let principal = addr.to_account_principal();
    if let PrincipalData::Standard(data) = PrincipalData::from(principal.clone()) {
        eprintln!("test_secp256k1 principal {:?}", data.to_address());
    }

    let addr = StacksAddress::from_public_keys(
        C32_ADDRESS_VERSION_TESTNET_SINGLESIG,
        &AddressHashMode::SerializeP2PKH,
        1,
        &vec![StacksPublicKey::from_hex(
            "03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110",
        )
        .unwrap()],
    )
    .unwrap();
    eprintln!("addr from hex {:?}", addr);
    let principal = addr.to_account_principal();
    if let PrincipalData::Standard(data) = PrincipalData::from(principal.clone()) {
        eprintln!("test_secp256k1 principal {:?}", data.to_address());
    }

    let expectations = [
        Value::Sequence(SequenceData::Buffer(BuffData {
            data: hex_bytes("03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110")
                .unwrap(),
        })),
        Value::UInt(1),
        Value::UInt(2),
        Value::Bool(true),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(false),
        Value::Principal(principal),
        Value::UInt(1),
    ];

    secp256k1_evals
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
fn test_secp256k1_errors() {
    let secp256k1_evals = [
        "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)",
        "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a130100)",
        "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04)",
        "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301 3)",

        "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a130111 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7)",
        "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)",

        "(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba77861 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba77861)",
        "(principal-of?)",
    ];

    let expectations: &[Error] = &[
        CheckErrors::TypeValueError(BUFF_32.clone(), Value::Sequence(SequenceData::Buffer(BuffData { data: hex_bytes("de5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f").unwrap() }))).into(),
        CheckErrors::TypeValueError(BUFF_65.clone(), Value::Sequence(SequenceData::Buffer(BuffData { data: hex_bytes("8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a130100").unwrap() }))).into(),
        CheckErrors::IncorrectArgumentCount(2, 1).into(),
        CheckErrors::IncorrectArgumentCount(2, 3).into(),

        CheckErrors::TypeValueError(BUFF_32.clone(), Value::Sequence(SequenceData::Buffer(BuffData { data: hex_bytes("de5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f").unwrap() }))).into(),
        CheckErrors::TypeValueError(BUFF_65.clone(), Value::Sequence(SequenceData::Buffer(BuffData { data: hex_bytes("8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a130111").unwrap() }))).into(),
        CheckErrors::TypeValueError(BUFF_33.clone(), Value::Sequence(SequenceData::Buffer(BuffData { data: hex_bytes("03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7").unwrap() }))).into(),
        CheckErrors::IncorrectArgumentCount(3, 2).into(),

        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::IncorrectArgumentCount(1, 0).into(),
    ];

    for (program, expectation) in secp256k1_evals.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).unwrap_err());
    }
}

#[test]
fn test_buffer_equality() {
    let tests = [
        "(is-eq \"a b c\" \"a b c\")",
        "(is-eq \"\\\" a b d\"
               \"\\\" a b d\")",
        "(not (is-eq \"\\\" a b d\"
                    \" a b d\"))",
    ];
    let expectations = [Value::Bool(true), Value::Bool(true), Value::Bool(true)];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
fn test_principal_equality() {
    let tests = [
        "(is-eq 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        "(not (is-eq 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR
                   'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G))"];
    let expectations = [Value::Bool(true), Value::Bool(true)];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
fn test_simple_if_functions() {
    //
    //  test program:
    //  (define (with_else x) (if (is-eq 5 x) 1 0)
    //  (define (without_else x) (if (is-eq 5 x) 1)
    //  (with_else 5)
    //  (with_else 3)
    //  (without_else 3)

    use vm::callables::DefineType::Private;

    let contract_id = QualifiedContractIdentifier::transient();

    let evals = parse(
        &contract_id,
        &"(with_else 5)
         (without_else 3)
         (with_else 3)",
    );

    let contract_id = QualifiedContractIdentifier::transient();

    let function_bodies = parse(
        &contract_id,
        &"(if (is-eq 5 x) 1 0)
                                  (if (is-eq 5 x) 1 3)",
    );

    if let Ok(parsed_bodies) = function_bodies {
        let func_args1 = vec![("x".into(), TypeSignature::IntType)];
        let func_args2 = vec![("x".into(), TypeSignature::IntType)];
        let user_function1 = DefinedFunction::new(
            func_args1,
            parsed_bodies[0].clone(),
            Private,
            &"with_else".into(),
            &"",
        );

        let user_function2 = DefinedFunction::new(
            func_args2,
            parsed_bodies[1].clone(),
            Private,
            &"without_else".into(),
            &"",
        );

        let context = LocalContext::new();
        let mut contract_context = ContractContext::new(QualifiedContractIdentifier::transient());
        let mut marf = MemoryBackingStore::new();
        let mut global_context =
            GlobalContext::new(false, marf.as_clarity_db(), LimitedCostTracker::new_free());

        contract_context
            .functions
            .insert("with_else".into(), user_function1);
        contract_context
            .functions
            .insert("without_else".into(), user_function2);

        let mut call_stack = CallStack::new();
        let mut env = Environment::new(
            &mut global_context,
            &contract_context,
            &mut call_stack,
            None,
            None,
        );

        if let Ok(tests) = evals {
            assert_eq!(Ok(Value::Int(1)), eval(&tests[0], &mut env, &context));
            assert_eq!(Ok(Value::Int(3)), eval(&tests[1], &mut env, &context));
            assert_eq!(Ok(Value::Int(0)), eval(&tests[2], &mut env, &context));
        } else {
            assert!(false, "Failed to parse function bodies.");
        }
    } else {
        assert!(false, "Failed to parse function bodies.");
    }
}

#[test]
fn test_concat_append_supertype() {
    let tests = [
        "(concat (list) (list 4 5))",
        "(concat (list (list 2) (list) (list 4 5))
                 (list (list) (list) (list 7 8 9)))",
        "(append (list) 1)",
        "(append (list (list 3 4) (list)) (list 4 5 7))",
    ];

    let expectations = [
        Value::list_from(vec![Value::Int(4), Value::Int(5)]).unwrap(),
        Value::list_from(vec![
            Value::list_from(vec![Value::Int(2)]).unwrap(),
            Value::list_from(vec![]).unwrap(),
            Value::list_from(vec![Value::Int(4), Value::Int(5)]).unwrap(),
            Value::list_from(vec![]).unwrap(),
            Value::list_from(vec![]).unwrap(),
            Value::list_from(vec![Value::Int(7), Value::Int(8), Value::Int(9)]).unwrap(),
        ])
        .unwrap(),
        Value::list_from(vec![Value::Int(1)]).unwrap(),
        Value::list_from(vec![
            Value::list_from(vec![Value::Int(3), Value::Int(4)]).unwrap(),
            Value::list_from(vec![]).unwrap(),
            Value::list_from(vec![Value::Int(4), Value::Int(5), Value::Int(7)]).unwrap(),
        ])
        .unwrap(),
    ];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
fn test_simple_arithmetic_functions() {
    let tests = [
        "(* 52314 414)",
        "(/ 52314 414)",
        "(* 2 3 4 5)",
        "(/ 10 13)",
        "(mod 51 2)",
        "(- 5 4 1)",
        "(+ 5 4 1)",
        "(is-eq (* 2 3)
              (+ 2 2 2))",
        "(> 1 2)",
        "(< 1 2)",
        "(<= 1 1)",
        "(>= 2 1)",
        "(>= 1 1)",
        "(pow 2 16)",
        "(pow 2 32)",
        "(pow 0 0)",
        "(pow 170141183460469231731687303715884105727 1)",
        "(pow u340282366920938463463374607431768211455 u1)",
        "(pow 0 170141183460469231731687303715884105727)",
        "(pow u1 u340282366920938463463374607431768211455)",
        "(sqrti u81)",
        "(sqrti u80)",
        "(sqrti 81)",
        "(sqrti 80)",
        // from https://en.wikipedia.org/wiki/128-bit_computing
        "(sqrti 170141183460469231731687303715884105727)", // max i128
        "(sqrti u340282366920938463463374607431768211455)", // max u128
        "(log2 u8)",
        "(log2 u9)",
        "(log2 8)",
        "(log2 9)",
        "(log2 170141183460469231731687303715884105727)", // max i128
        "(log2 u340282366920938463463374607431768211455)", // max u128
        "(+ (pow u2 u127) (- (pow u2 u127) u1))",
        "(+ (to-uint 127) u10)",
        "(to-int (- (pow u2 u127) u1))",
        "(- (pow 2 32))",
    ];

    let expectations = [
        Value::Int(21657996),
        Value::Int(126),
        Value::Int(120),
        Value::Int(0),
        Value::Int(1),
        Value::Int(0),
        Value::Int(10),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(true),
        Value::Bool(true),
        Value::Bool(true),
        Value::Bool(true),
        Value::Int(65536),
        Value::Int(u32::max_value() as i128 + 1),
        Value::Int(1),
        Value::Int(170_141_183_460_469_231_731_687_303_715_884_105_727),
        Value::UInt(340_282_366_920_938_463_463_374_607_431_768_211_455),
        Value::Int(0),
        Value::UInt(1),
        Value::UInt(9),
        Value::UInt(8),
        Value::Int(9),
        Value::Int(8),
        Value::Int(13_043_817_825_332_782_212),
        Value::UInt(18_446_744_073_709_551_615),
        Value::UInt(3),
        Value::UInt(3),
        Value::Int(3),
        Value::Int(3),
        Value::Int(126),
        Value::UInt(127),
        Value::UInt(u128::max_value()),
        Value::UInt(137),
        Value::Int(i128::max_value()),
        Value::Int(-1 * (u32::max_value() as i128 + 1)),
    ];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
fn test_simple_arithmetic_errors() {
    let tests = [
        "(>= 1)",
        "(+ 1 true)",
        "(/ 10 0)",
        "(mod 10 0)",
        "(pow 2 128)",
        "(* 10 (pow 2 126))",
        "(+ (pow 2 126) (pow 2 126))",
        "(- 0 (pow 2 126) (pow 2 126) 1)",
        "(-)",
        "(/)",
        "(mod 1)",
        "(pow 1)",
        "(sqrti)",
        "(sqrti 256 16)",
        "(sqrti -1)",
        "(log2)",
        "(log2 8 9)",
        "(log2 -8)",
        "(xor 1)",
        "(pow 2 (pow 2 32))",
        "(pow 2 (- 1))",
        "(is-eq (some 1) (some true))",
    ];

    let expectations: &[Error] = &[
        CheckErrors::IncorrectArgumentCount(2, 1).into(),
        CheckErrors::TypeValueError(TypeSignature::IntType, Value::Bool(true)).into(),
        RuntimeErrorType::DivisionByZero.into(),
        RuntimeErrorType::DivisionByZero.into(),
        RuntimeErrorType::ArithmeticOverflow.into(),
        RuntimeErrorType::ArithmeticOverflow.into(),
        RuntimeErrorType::ArithmeticOverflow.into(),
        RuntimeErrorType::ArithmeticUnderflow.into(),
        CheckErrors::IncorrectArgumentCount(1, 0).into(),
        CheckErrors::IncorrectArgumentCount(1, 0).into(),
        CheckErrors::IncorrectArgumentCount(2, 1).into(),
        CheckErrors::IncorrectArgumentCount(2, 1).into(),
        CheckErrors::IncorrectArgumentCount(1, 0).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        RuntimeErrorType::Arithmetic("sqrti must be passed a positive integer".to_string()).into(),
        CheckErrors::IncorrectArgumentCount(1, 0).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        RuntimeErrorType::Arithmetic("log2 must be passed a positive integer".to_string()).into(),
        CheckErrors::IncorrectArgumentCount(2, 1).into(),
        RuntimeErrorType::Arithmetic(
            "Power argument to (pow ...) must be a u32 integer".to_string(),
        )
        .into(),
        RuntimeErrorType::Arithmetic(
            "Power argument to (pow ...) must be a u32 integer".to_string(),
        )
        .into(),
        CheckErrors::TypeError(TypeSignature::from("bool"), TypeSignature::from("int")).into(),
    ];

    for (program, expectation) in tests.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).unwrap_err());
    }
}

#[test]
fn test_unsigned_arithmetic() {
    let tests = [
        "(- u10)",
        "(- u10 u11)",
        "(> u10 80)",
        "(+ u10 80)",
        "(to-uint -10)",
        "(to-int (pow u2 u127))",
    ];

    let expectations: &[Error] = &[
        RuntimeErrorType::ArithmeticUnderflow.into(),
        RuntimeErrorType::ArithmeticUnderflow.into(),
        CheckErrors::UnionTypeValueError(
            vec![TypeSignature::IntType, TypeSignature::UIntType],
            Value::UInt(10),
        )
        .into(),
        CheckErrors::TypeValueError(TypeSignature::UIntType, Value::Int(80)).into(),
        RuntimeErrorType::ArithmeticUnderflow.into(),
        RuntimeErrorType::ArithmeticOverflow.into(),
    ];

    for (program, expectation) in tests.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).unwrap_err());
    }
}

#[test]
fn test_options_errors() {
    let tests = [
        "(is-none 2 1)",
        "(is-none true)",
        "(is-ok 2 1)",
        "(is-ok true)",
        "(is-err 2 1)",
        "(is-err true)",
        "(is-some 2 1)",
        "(is-some true)",
        "(ok 2 3)",
        "(some 2 3)",
        "(err 4 5)",
        "(default-to 4 5 7)",
        "(default-to 4 true)",
        "(get field-0 (some 1))",
        "(get field-0 1)",
    ];

    let expectations: &[Error] = &[
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::ExpectedOptionalValue(Value::Bool(true)).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::ExpectedResponseValue(Value::Bool(true)).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::ExpectedResponseValue(Value::Bool(true)).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::ExpectedOptionalValue(Value::Bool(true)).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::IncorrectArgumentCount(2, 3).into(),
        CheckErrors::ExpectedOptionalValue(Value::Bool(true)).into(),
        CheckErrors::ExpectedTuple(TypeSignature::IntType).into(),
        CheckErrors::ExpectedTuple(TypeSignature::IntType).into(),
    ];

    for (program, expectation) in tests.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).unwrap_err());
    }
}

#[test]
fn test_stx_ops_errors() {
    let tests = [
        "(stx-transfer? u4 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        "(stx-transfer? 4 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        "(stx-transfer? u4 u3 u2)",
        "(stx-burn? u4)",
        "(stx-burn? 4 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
    ];

    let expectations: &[Error] = &[
        CheckErrors::IncorrectArgumentCount(3, 2).into(),
        CheckErrors::BadTransferSTXArguments.into(),
        CheckErrors::BadTransferSTXArguments.into(),
        CheckErrors::IncorrectArgumentCount(2, 1).into(),
        CheckErrors::BadTransferSTXArguments.into(),
    ];

    for (program, expectation) in tests.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).unwrap_err());
    }
}

#[test]
fn test_some() {
    let tests = [
        "(is-eq (some 1) (some 1))",
        "(is-eq none none)",
        "(is-none (some 1))",
        "(is-some (some 1))",
        "(is-some none)",
        "(is-none none)",
        "(is-eq (some 1) none)",
        "(is-eq none (some 1))",
        "(is-eq (some 1) (some 2))",
    ];

    let expectations = [
        Value::Bool(true),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(false),
        Value::Bool(false),
    ];

    for (program, expectation) in tests.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).unwrap().unwrap());
    }
}

#[test]
fn test_option_destructs() {
    let tests = [
        "(unwrap! (some 1) 2)",
        "(unwrap-err! (err 1) 2)",
        "(unwrap-err! (some 2) 2)",
        "(unwrap! (ok 3) 2)",
        "(unwrap! (err 3) 2)",
        "(unwrap-panic (ok 3))",
        "(unwrap-panic (some 3))",
        "(unwrap-err-panic (err 3))",
        "(unwrap-err-panic (ok 3))",
        "(unwrap-panic none)",
        "(unwrap-panic (err 3))",
        "(match (some 1) inner-value (+ 1 inner-value) (/ 1 0))",
        "(match none inner-value (/ 1 0) (+ 1 8))",
        "(match (ok 1) ok-val (+ 1 ok-val) err-val (/ err-val 0))",
        "(match (err 1) ok-val (/ ok-val 0) err-val (+ err-val 7))",
        "(match 1 ok-val (/ ok-val 0) err-val (+ err-val 7))",
        "(match 2 ok-val (/ ok-val 0) (+ 3 7))",
        "(try! (err u1))",
        "(try! (ok 3))",
        "(try! none)",
        "(try! (some true))",
        "(try! none 1)",
        "(try! 1)",
    ];

    let expectations: &[Result<Value, Error>] = &[
        Ok(Value::Int(1)),
        Ok(Value::Int(1)),
        Err(CheckErrors::ExpectedResponseValue(Value::some(Value::Int(2)).unwrap()).into()),
        Ok(Value::Int(3)),
        Err(ShortReturnType::ExpectedValue(Value::Int(2)).into()),
        Ok(Value::Int(3)),
        Ok(Value::Int(3)),
        Ok(Value::Int(3)),
        Err(RuntimeErrorType::UnwrapFailure.into()),
        Err(RuntimeErrorType::UnwrapFailure.into()),
        Err(RuntimeErrorType::UnwrapFailure.into()),
        Ok(Value::Int(2)),
        Ok(Value::Int(9)),
        Ok(Value::Int(2)),
        Ok(Value::Int(8)),
        Err(CheckErrors::BadMatchInput(TypeSignature::IntType).into()),
        Err(CheckErrors::BadMatchInput(TypeSignature::IntType).into()),
        Err(ShortReturnType::ExpectedValue(Value::error(Value::UInt(1)).unwrap()).into()),
        Ok(Value::Int(3)),
        Err(ShortReturnType::ExpectedValue(Value::none()).into()),
        Ok(Value::Bool(true)),
        Err(CheckErrors::IncorrectArgumentCount(1, 2).into()),
        Err(CheckErrors::ExpectedOptionalOrResponseValue(Value::Int(1)).into()),
    ];

    for (program, expectation) in tests.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).map(|x| x.unwrap()));
    }
}

#[test]
fn test_hash_errors() {
    let tests = [
        "(sha256 2 1)",
        "(keccak256 3 1)",
        "(hash160 2 1)",
        "(sha256 true)",
        "(keccak256 true)",
        "(hash160 true)",
        "(sha512 true)",
        "(sha512 1 2)",
        "(sha512/256 true)",
        "(sha512/256 1 2)",
    ];

    let expectations: &[Error] = &[
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::UnionTypeValueError(
            vec![
                TypeSignature::IntType,
                TypeSignature::UIntType,
                TypeSignature::max_buffer(),
            ],
            Value::Bool(true),
        )
        .into(),
        CheckErrors::UnionTypeValueError(
            vec![
                TypeSignature::IntType,
                TypeSignature::UIntType,
                TypeSignature::max_buffer(),
            ],
            Value::Bool(true),
        )
        .into(),
        CheckErrors::UnionTypeValueError(
            vec![
                TypeSignature::IntType,
                TypeSignature::UIntType,
                TypeSignature::max_buffer(),
            ],
            Value::Bool(true),
        )
        .into(),
        CheckErrors::UnionTypeValueError(
            vec![
                TypeSignature::IntType,
                TypeSignature::UIntType,
                TypeSignature::max_buffer(),
            ],
            Value::Bool(true),
        )
        .into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
        CheckErrors::UnionTypeValueError(
            vec![
                TypeSignature::IntType,
                TypeSignature::UIntType,
                TypeSignature::max_buffer(),
            ],
            Value::Bool(true),
        )
        .into(),
        CheckErrors::IncorrectArgumentCount(1, 2).into(),
    ];

    for (program, expectation) in tests.iter().zip(expectations.iter()) {
        assert_eq!(*expectation, vm_execute(program).unwrap_err());
    }
}

#[test]
fn test_bool_functions() {
    let tests = [
        "true",
        "(and true true true)",
        "(and false true true)",
        "(and false (> 1 (/ 10 0)))",
        "(or true (> 1 (/ 10 0)))",
        "(or false false false)",
        "(not true)",
        "(and true false)",
        "(or false true)",
    ];

    let expectations = [
        Value::Bool(true),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(false),
        Value::Bool(true),
        Value::Bool(false),
        Value::Bool(false),
        Value::Bool(false),
        Value::Bool(true),
    ];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
fn test_bad_lets() {
    let tests = [
        "(let ((tx-sender 1)) (+ tx-sender tx-sender))",
        "(let ((* 1)) (+ * *))",
        "(let ((a 1) (a 2)) (+ a a))",
        "(let ((a 1) (b 2)) (var-set cursor a) (var-set cursor (+ b (var-get cursor))) (+ a b))",
        "(let ((true 0)) true)",
        "(let ((false 1)) false)",
    ];

    let expectations: &[Error] = &[
        CheckErrors::NameAlreadyUsed("tx-sender".to_string()).into(),
        CheckErrors::NameAlreadyUsed("*".to_string()).into(),
        CheckErrors::NameAlreadyUsed("a".to_string()).into(),
        CheckErrors::NoSuchDataVariable("cursor".to_string()).into(),
        CheckErrors::NameAlreadyUsed("true".to_string()).into(),
        CheckErrors::NameAlreadyUsed("false".to_string()).into(),
    ];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| {
            assert_eq!((*expectation), vm_execute(program).unwrap_err())
        });
}

#[test]
fn test_lets() {
    let tests = [
        "(let ((a 1) (b 2)) (+ a b))",
        "(define-data-var cursor int 0) (let ((a 1) (b 2)) (var-set cursor a) (var-set cursor (+ b (var-get cursor))) (var-get cursor))"];

    let expectations = [Value::Int(3), Value::Int(3)];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
// tests that the type signature of the result of a merge tuple is updated.
//  this is required to pass the type admission checks of, e.g., data store
//  operations like `(define-data-var ...)`
fn merge_update_type_signature_2239() {
    let tests = [
        "(define-data-var a {p: uint} (merge {p: 2} {p: u2})) (var-get a)",
        "(merge {p: 2} {p: u2})",
        "(merge {p: 2} {q: 3})",
        "(define-data-var c {p: uint} {p: u2}) (var-get c)",
        "(define-data-var d {p: uint} (merge {p: u2} {p: u2})) (var-get d)",
        "(define-data-var e {p: int, q: int} {p: 2, q: 3}) (var-get e)",
        "(define-data-var f {p: int, q: int} (merge {q: 2, p: 3} {p: 4})) (var-get f)",
    ];

    let expectations = [
        "(tuple (p u2))",
        "(tuple (p u2))",
        "(tuple (p 2) (q 3))",
        "(tuple (p u2))",
        "(tuple (p u2))",
        "(tuple (p 2) (q 3))",
        "(tuple (p 4) (q 2))",
    ];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| {
            assert_eq!(expectation.to_string(), execute(program).to_string())
        });
}

#[test]
fn test_2053_stacked_user_funcs() {
    let test = "
(define-read-only (identity (n int)) n)
(begin (identity (identity 1)))
";

    let expectation = Value::Int(1);

    assert_eq!(expectation, execute(test));
}

#[test]
fn test_asserts() {
    let tests = [
        "(begin (asserts! (is-eq 1 1) (err 0)) (ok 1))",
        "(begin (asserts! (is-eq 1 1) (err 0)) (asserts! (is-eq 2 2) (err 1)) (ok 2))",
    ];

    let expectations = [
        Value::okay(Value::Int(1)).unwrap(),
        Value::okay(Value::Int(2)).unwrap(),
    ];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| assert_eq!(expectation.clone(), execute(program)));
}

#[test]
fn test_asserts_short_circuit() {
    let tests = [
        "(begin (asserts! (is-eq 1 0) (err 0)) (ok 1))",
        "(begin (asserts! (is-eq 1 1) (err 0)) (asserts! (is-eq 2 1) (err 1)) (ok 2))",
    ];

    let expectations: &[Error] = &[
        Error::ShortReturn(ShortReturnType::AssertionFailed(
            Value::error(Value::Int(0)).unwrap(),
        )),
        Error::ShortReturn(ShortReturnType::AssertionFailed(
            Value::error(Value::Int(1)).unwrap(),
        )),
    ];

    tests
        .iter()
        .zip(expectations.iter())
        .for_each(|(program, expectation)| {
            assert_eq!((*expectation), vm_execute(program).unwrap_err())
        });
}
