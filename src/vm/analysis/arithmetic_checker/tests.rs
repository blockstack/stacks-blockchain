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

use crate::vm::ClarityVersion;
use chainstate::stacks::boot::BOOT_CODE_COSTS;
use vm::analysis::type_checker::tests::mem_type_check;
use vm::analysis::{
    arithmetic_checker::ArithmeticOnlyChecker, arithmetic_checker::Error,
    arithmetic_checker::Error::*, ContractAnalysis,
};
use vm::ast::parse;
use vm::costs::LimitedCostTracker;
use vm::functions::define::DefineFunctions;
use vm::functions::NativeFunctions;
use vm::types::QualifiedContractIdentifier;
use vm::variables::NativeVariables;

/// Checks whether or not a contract only contains arithmetic expressions (for example, defining a
/// map would not pass this check).
/// This check is useful in determining the validity of new potential cost functions.
fn arithmetic_check(contract: &str) -> Result<(), Error> {
    let contract_identifier = QualifiedContractIdentifier::transient();
    let expressions = parse(&contract_identifier, contract).unwrap();

    let analysis = ContractAnalysis::new(
        contract_identifier,
        expressions,
        LimitedCostTracker::new_free(),
        ClarityVersion::Clarity2,
    );

    ArithmeticOnlyChecker::run(&analysis)
}

fn check_good(contract: &str) {
    let analysis = mem_type_check(contract).unwrap().1;
    ArithmeticOnlyChecker::run(&analysis).expect("Should pass arithmetic checks");
}

#[test]
fn test_boot_definitions() {
    check_good(BOOT_CODE_COSTS);
}

#[test]
fn test_bad_defines() {
    let tests = [
        ("(define-public (foo) (ok 1))", DefineTypeForbidden(DefineFunctions::PublicFunction)),
        ("(define-map foo-map ((a uint)) ((b uint))) (define-private (foo) (map-get? foo-map {a: u1}))", DefineTypeForbidden(DefineFunctions::Map)),
        ("(define-data-var foo-var uint u1) (define-private (foo) (var-get foo-var))", DefineTypeForbidden(DefineFunctions::PersistedVariable)),
        ("(define-fungible-token tokaroos u500)", DefineTypeForbidden(DefineFunctions::FungibleToken)),
        ("(define-fungible-token tokaroos)", DefineTypeForbidden(DefineFunctions::FungibleToken)),
        ("(define-non-fungible-token tokaroos uint)", DefineTypeForbidden(DefineFunctions::NonFungibleToken)),
        ("(define-trait foo-trait ((foo (uint)) (response uint uint)))", DefineTypeForbidden(DefineFunctions::Trait)),
    ];

    for (contract, error) in tests.iter() {
        assert_eq!(
            arithmetic_check(contract),
            Err(error.clone()),
            "Check contract:\n {}",
            contract
        );
    }
}

#[test]
fn test_variables_fail_arithmetic_check() {
    let tests = [
        (
            "(define-private (foo) burn-block-height)",
            VariableForbidden(NativeVariables::BurnBlockHeight),
        ),
        (
            "(define-private (foo) block-height)",
            VariableForbidden(NativeVariables::BlockHeight),
        ),
        (
            "(define-private (foo) tx-sender)",
            VariableForbidden(NativeVariables::TxSender),
        ),
        (
            "(define-private (foo) contract-caller)",
            VariableForbidden(NativeVariables::ContractCaller),
        ),
        (
            "(define-private (foo) is-in-regtest)",
            VariableForbidden(NativeVariables::Regtest),
        ),
        (
            "(define-private (foo) stx-liquid-supply)",
            VariableForbidden(NativeVariables::TotalLiquidMicroSTX),
        ),
        (
            "(define-private (foo) tx-sponsor?)",
            VariableForbidden(NativeVariables::TxSponsor),
        ),
    ];

    for (contract, error) in tests.iter() {
        assert_eq!(
            arithmetic_check(contract),
            Err(error.clone()),
            "Check contract:\n {}",
            contract
        );
    }

    let tests = [
        "(define-private (foo) (begin true false none))",
        "(define-private (foo) 1)",
    ];

    for contract in tests.iter() {
        check_good(contract);
    }
}

#[test]
fn test_functions() {
    let bad_tests = [
        ("(define-private (foo) (at-block 0x0202020202020202020202020202020202020202020202020202020202020202 (+ 1 2)))",
         FunctionNotPermitted(NativeFunctions::AtBlock)),
        ("(define-private (foo) (map-get? foo-map {a: u1}))",
         FunctionNotPermitted(NativeFunctions::FetchEntry)),
        ("(define-private (foo) (map-delete foo-map {a: u1}))",
         FunctionNotPermitted(NativeFunctions::DeleteEntry)),
        ("(define-private (foo) (map-set foo-map {a: u1} {b: u2}))",
         FunctionNotPermitted(NativeFunctions::SetEntry)),
        ("(define-private (foo) (map-insert foo-map {a: u1} {b: u2}))",
         FunctionNotPermitted(NativeFunctions::InsertEntry)),
        ("(define-private (foo) (var-get foo-var))",
         FunctionNotPermitted(NativeFunctions::FetchVar)),
        ("(define-private (foo) (var-set foo-var u2))",
         FunctionNotPermitted(NativeFunctions::SetVar)),
        ("(define-private (foo (a principal)) (ft-get-balance tokaroos a))",
         FunctionNotPermitted(NativeFunctions::GetTokenBalance)),
        ("(define-private (foo (a principal)) 
          (ft-transfer? stackaroo u50 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF))",
         FunctionNotPermitted(NativeFunctions::TransferToken)),
        ("(define-private (foo (a principal)) 
          (ft-mint? stackaroo u100 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR))",
         FunctionNotPermitted(NativeFunctions::MintToken)),
        ("(define-private (foo (a principal)) 
           (nft-mint? stackaroo \"Roo\" 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR))",
         FunctionNotPermitted(NativeFunctions::MintAsset)),
        ("(nft-transfer? stackaroo \"Roo\" 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)",
         FunctionNotPermitted(NativeFunctions::TransferAsset)),
        ("(nft-get-owner? stackaroo \"Roo\")",
         FunctionNotPermitted(NativeFunctions::GetAssetOwner)),
        ("(get-block-info? id-header-hash 0)",
         FunctionNotPermitted(NativeFunctions::GetBlockInfo)),
        ("(define-private (foo) (contract-call? .bar outer-call))",
         FunctionNotPermitted(NativeFunctions::ContractCall)),
        ("(stx-get-balance 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)",
         FunctionNotPermitted(NativeFunctions::GetStxBalance)),
        ("(stx-burn? u100 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)",
         FunctionNotPermitted(NativeFunctions::StxBurn)),
        (r#"(stx-transfer? u100 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF 0x00)"#,
         FunctionNotPermitted(NativeFunctions::StxTransfer)),
        ("(define-private (foo (a (list 3 uint)))
           (map log2 a))",
         FunctionNotPermitted(NativeFunctions::Map)),
        ("(define-private (foo (a (list 3 (optional uint))))
           (filter is-none a))",
         FunctionNotPermitted(NativeFunctions::Filter)),
        ("(define-private (foo (a (list 3 uint)))
           (append a u4))",
         FunctionNotPermitted(NativeFunctions::Append)),
        ("(define-private (foo (a (list 3 uint)))
           (concat a a))",
         FunctionNotPermitted(NativeFunctions::Concat)),
        ("(define-private (foo (a (list 3 uint)))
           (as-max-len? a u4))",
         FunctionNotPermitted(NativeFunctions::AsMaxLen)),
        ("(define-private (foo) (print 10))",
         FunctionNotPermitted(NativeFunctions::Print)),
        ("(define-private (foo) (list 3 4 10))",
         FunctionNotPermitted(NativeFunctions::ListCons)),
        ("(define-private (foo) (keccak256 0))",
         FunctionNotPermitted(NativeFunctions::Keccak256)),
        ("(define-private (foo) (hash160 0))",
         FunctionNotPermitted(NativeFunctions::Hash160)),
        ("(define-private (foo) (secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04  0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301))",
         FunctionNotPermitted(NativeFunctions::Secp256k1Recover)),
        ("(define-private (foo) (secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a13
 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110))",
         FunctionNotPermitted(NativeFunctions::Secp256k1Verify)),
        ("(define-private (foo) (sha256 0))",
         FunctionNotPermitted(NativeFunctions::Sha256)),
        ("(define-private (foo) (sha512 0))",
         FunctionNotPermitted(NativeFunctions::Sha512)),
        ("(define-private (foo) (sha512/256 0))",
         FunctionNotPermitted(NativeFunctions::Sha512Trunc256)),
        ("(define-private (foo (a (list 3 uint)))
         (slice a u2 u1))",
         FunctionNotPermitted(NativeFunctions::Slice)),

    ];

    for (contract, error) in bad_tests.iter() {
        eprintln!("{}", contract);
        assert_eq!(
            arithmetic_check(contract),
            Err(error.clone()),
            "Check contract:\n {}",
            contract
        );
    }

    let good_tests = [
        "(match (if (is-eq 0 1) (ok 1) (err 2))
            ok-val (+ 1 ok-val)
            err-val (+ 2 err-val))",
        "(match (if (is-eq 0 1) (some 1) none)
            ok-val (+ 1 ok-val)
            2)",
        "(get a { a: (+ 9 1), b: (if (> 2 3) (* 4 4) (/ 4 2)) })",
        "(define-private (foo)
           (let ((a (+ 3 2 3))) (log2 a)))",
        "(define-private (foo)
           (let ((a (+ 32 3 4)) (b (- 32 1))
                 (c (if (and (< 3 2) (<= 3 2) (>= 4 5) (or (is-eq (mod 5 4) 0) (not (> 3 2))))
                    (pow u2 (log2 (sqrti u100000)))
                    (xor u120 u280)))
                 (d (default-to u0 (some u2))))
             (begin (unwrap! (some u3) u1)
                    (unwrap-err! (err u5) u4)
                    (asserts! true u4)
                    (unwrap-panic (some u3))
                    (unwrap-err-panic (err u5)))))",
        "(define-private (foo) (to-int (to-uint 34)))
         (define-private (bar) (foo))",
        "(define-private (foo) (begin
           (is-some (some 4))
           (is-none (some 4))
           (is-ok (ok 4))
           (is-err (ok 5))
           (try! (some 4))
           (some 5)))
         (define-read-only (bar) (foo))",
    ];

    for contract in good_tests.iter() {
        eprintln!("{}", contract);
        check_good(contract);
    }
}
