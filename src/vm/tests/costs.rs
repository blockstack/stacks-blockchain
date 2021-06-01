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

use crate::types::chainstate::StacksBlockHeader;
use crate::types::chainstate::StacksBlockId;
use crate::types::proof::ClarityMarfTrieId;
use crate::util::boot::boot_code_id;
use crate::{types::chainstate::BlockHeaderHash, vm::database::NULL_BURN_STATE_DB_2_1};
use chainstate::stacks::events::StacksTransactionEvent;
use chainstate::stacks::index::storage::TrieFileStorage;
use clarity_vm::clarity::ClarityInstance;
use core::FIRST_BURNCHAIN_CONSENSUS_HASH;
use core::FIRST_STACKS_BLOCK_HASH;
use util::hash::hex_bytes;
use vm::contexts::Environment;
use vm::contexts::{AssetMap, AssetMapEntry, GlobalContext, OwnedEnvironment};
use vm::contracts::Contract;
use vm::costs::cost_functions::ClarityCostFunction;
use vm::costs::{ClarityCostFunctionReference, ExecutionCost, LimitedCostTracker};
use vm::database::{ClarityDatabase, NULL_BURN_STATE_DB, NULL_HEADER_DB};
use vm::errors::{CheckErrors, Error, RuntimeErrorType};
use vm::execute as vm_execute;
use vm::functions::NativeFunctions;
use vm::representations::SymbolicExpression;
use vm::tests::{
    execute, is_committed, is_err_code, symbols_from_values, with_marfed_environment,
    with_memory_environment,
};
use vm::types::{
    AssetIdentifier, OptionalData, PrincipalData, QualifiedContractIdentifier, ResponseData, Value,
};

use crate::clarity_vm::database::marf::MarfedKV;
use crate::clarity_vm::database::MemoryBackingStore;

lazy_static! {
    static ref COST_VOTING_TESTNET_CONTRACT: QualifiedContractIdentifier =
        boot_code_id("cost-voting", false);
}

pub fn get_simple_test(function: &NativeFunctions) -> &'static str {
    use vm::functions::NativeFunctions::*;
    match function {
        Add => "(+ 1 1)",
        ToUInt => "(to-uint 1)",
        ToInt => "(to-int u1)",
        Subtract => "(- 1 1)",
        Multiply => "(* 1 1)",
        Divide => "(/ 1 1)",
        CmpGeq => "(>= 2 1)",
        CmpLeq => "(<= 2 1)",
        CmpLess => "(< 2 1)",
        CmpGreater => "(> 2 1)",
        Modulo => "(mod 2 1)",
        Power => "(pow 2 3)",
        Sqrti => "(sqrti 81)",
        Log2 => "(log2 8)",
        BitwiseXOR => "(xor 1 2)",
        And => "(and true false)",
        Or => "(or true false)",
        Not => "(not true)",
        Equals => "(is-eq 1 2)",
        If => "(if true (+ 1 2) 2)",
        Let => "(let ((x 1)) x)",
        FetchVar => "(var-get var-foo)",
        SetVar => "(var-set var-foo 1)",
        Map => "(map not list-foo)",
        Filter => "(filter not list-foo)",
        Fold => "(fold + list-bar 0)",
        Append => "(append list-bar 1)",
        Concat => "(concat list-bar list-bar)",
        AsMaxLen => "(as-max-len? list-bar u3)",
        Len => "(len list-bar)",
        ElementAt => "(element-at list-bar u2)",
        IndexOf => "(index-of list-bar 1)",
        ListCons => "(list 1 2 3 4)",
        FetchEntry => "(map-get? map-foo {a: 1})",
        SetEntry => "(map-set map-foo {a: 1} {b: 2})",
        InsertEntry => "(map-insert map-foo {a: 2} {b: 2})",
        DeleteEntry => "(map-delete map-foo {a: 1})",
        TupleCons => "(tuple (a 1))",
        TupleGet => "(get a tuple-foo)",
        TupleMerge => "(merge {a: 1, b: 2} {b: 1})",
        Begin => "(begin 1)",
        Hash160 => "(hash160 1)",
        Sha256 => "(sha256 1)",
        Sha512 => "(sha512 1)",
        Sha512Trunc256 => "(sha512/256 1)",
        Keccak256 => "(keccak256 1)",
        Secp256k1Recover => "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)",
        Secp256k1Verify => "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        Print => "(print 1)",
        ContractCall => "(contract-call? .contract-other foo-exec 1)",
        ContractOf => "(contract-of contract)",
        PrincipalOf => "(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)",
        AsContract => "(as-contract 1)",
        GetBlockInfo => "(get-block-info? time u1)",
        ConsOkay => "(ok 1)",
        ConsError => "(err 1)",
        ConsSome => "(some 1)",
        DefaultTo => "(default-to 1 none)",
        Asserts => "(asserts! true (err 1))",
        UnwrapRet => "(unwrap! (ok 1) (err 1))",
        UnwrapErrRet => "(unwrap-err! (err 1) (ok 1))",
        Unwrap => "(unwrap-panic (ok 1))",
        UnwrapErr => "(unwrap-err-panic (err 1))",
        Match => "(match (some 1) x (+ x 1) 1)",
        TryRet => "(try! (if true (ok 1) (err 1)))",
        IsOkay => "(is-ok (ok 1))",
        IsNone => "(is-none none)",
        IsErr => "(is-err (err 1))",
        IsSome => "(is-some (some 1))",
        MintAsset => "(ft-mint? ft-foo u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        MintToken => "(nft-mint? nft-foo 1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        GetTokenBalance => "(ft-get-balance ft-foo 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        GetAssetOwner => "(nft-get-owner? nft-foo 1)",
        TransferToken => "(ft-transfer? ft-foo u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        TransferAsset => "(nft-transfer? nft-foo 1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        BurnToken => "(ft-burn? ft-foo u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        BurnAsset => "(nft-burn? nft-foo 1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        GetTokenSupply => "(ft-get-supply ft-foo)",
        AtBlock => "(at-block 0x55c9861be5cff984a20ce6d99d4aa65941412889bdc665094136429b84f8c2ee 1)",   // first stacksblockid
        GetStxBalance => "(stx-get-balance 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        StxTransfer => r#"(stx-transfer? u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 0x89995432)"#,
        StxBurn => "(stx-burn? u1 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        StxGetAccount => "(stx-account 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)",
        Slice => "(slice list-bar u1 u1)",
    }
}

fn execute_transaction(
    env: &mut OwnedEnvironment,
    issuer: PrincipalData,
    contract_identifier: &QualifiedContractIdentifier,
    tx: &str,
    args: &[SymbolicExpression],
) -> Result<(Value, AssetMap, Vec<StacksTransactionEvent>), Error> {
    env.execute_transaction(issuer, None, contract_identifier.clone(), tx, args)
}

fn test_tracked_costs(prog: &str) -> ExecutionCost {
    let contract_trait = "(define-trait trait-1 (
                            (foo-exec (int) (response int int))
                          ))";
    let contract_other = "(impl-trait .contract-trait.trait-1)
                          (define-map map-foo { a: int } { b: int })
                          (define-public (foo-exec (a int)) (ok 1))";

    let contract_self = format!(
        "(define-map map-foo {{ a: int }} {{ b: int }})
        (define-non-fungible-token nft-foo int)
        (define-fungible-token ft-foo)
        (define-data-var var-foo int 0)
        (define-constant tuple-foo (tuple (a 1)))
        (define-constant list-foo (list true))
        (define-constant list-bar (list 1))
        (use-trait trait-1 .contract-trait.trait-1)
        (define-public (execute (contract <trait-1>)) (ok {}))",
        prog
    );

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let self_contract_id = QualifiedContractIdentifier::new(p1_principal.clone(), "self".into());
    let other_contract_id =
        QualifiedContractIdentifier::new(p1_principal.clone(), "contract-other".into());
    let trait_contract_id =
        QualifiedContractIdentifier::new(p1_principal.clone(), "contract-trait".into());

    let marf_kv = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, marf_kv, ExecutionCost::max_value());
    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            ),
            &NULL_HEADER_DB,
            &NULL_BURN_STATE_DB,
        )
        .commit_block();

    let mut marf_kv = clarity_instance.destroy();

    let mut store = marf_kv.begin(
        &StacksBlockHeader::make_index_block_hash(
            &FIRST_BURNCHAIN_CONSENSUS_HASH,
            &FIRST_STACKS_BLOCK_HASH,
        ),
        &StacksBlockId([1 as u8; 32]),
    );

    let mut owned_env = OwnedEnvironment::new_max_limit(
        store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB_2_1),
    );

    owned_env
        .initialize_contract(trait_contract_id.clone(), contract_trait, None)
        .unwrap();
    owned_env
        .initialize_contract(other_contract_id.clone(), contract_other, None)
        .unwrap();
    owned_env
        .initialize_contract(self_contract_id.clone(), &contract_self, None)
        .unwrap();

    let target_contract = Value::from(PrincipalData::Contract(other_contract_id));

    eprintln!("{}", &contract_self);
    execute_transaction(
        &mut owned_env,
        p2_principal,
        &self_contract_id,
        "execute",
        &symbols_from_values(vec![target_contract]),
    )
    .unwrap();

    let (_db, tracker) = owned_env.destruct().unwrap();
    tracker.get_total()
}

#[test]
fn test_all() {
    let baseline = test_tracked_costs("1");

    for f in NativeFunctions::ALL.iter() {
        let test = get_simple_test(f);
        let cost = test_tracked_costs(test);
        assert!(cost.exceeds(&baseline));
    }
}

#[test]
fn test_cost_contract_short_circuits() {
    let marf_kv = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, marf_kv, ExecutionCost::max_value());
    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            ),
            &NULL_HEADER_DB,
            &NULL_BURN_STATE_DB,
        )
        .commit_block();

    let marf_kv = clarity_instance.destroy();

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let cost_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "cost-definer".into());
    let intercepted = QualifiedContractIdentifier::new(p1_principal.clone(), "intercepted".into());
    let caller = QualifiedContractIdentifier::new(p1_principal.clone(), "caller".into());

    let mut marf_kv = {
        let mut clarity_inst = ClarityInstance::new(false, marf_kv, ExecutionCost::max_value());
        let mut block_conn = clarity_inst.begin_block(
            &StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            ),
            &StacksBlockId([1 as u8; 32]),
            &NULL_HEADER_DB,
            &NULL_BURN_STATE_DB,
        );

        let cost_definer_src = "
    (define-read-only (cost-definition (size uint))
       {
         runtime: u1, write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    ";

        let intercepted_src = "
    (define-read-only (intercepted-function (a uint))
       (if (>= a u10)
           (+ (+ a a) (+ a a)
              (+ a a) (+ a a))
           u0))
    ";

        let caller_src = "
    (define-public (execute (a uint))
       (ok (contract-call? .intercepted intercepted-function a)))
    ";

        for (contract_name, contract_src) in [
            (&cost_definer, cost_definer_src),
            (&intercepted, intercepted_src),
            (&caller, caller_src),
        ]
        .iter()
        {
            block_conn.as_transaction(|tx| {
                let (ast, analysis) = tx
                    .analyze_smart_contract(contract_name, contract_src)
                    .unwrap();
                tx.initialize_smart_contract(contract_name, &ast, contract_src, None, |_, _| false)
                    .unwrap();
                tx.save_analysis(contract_name, &analysis).unwrap();
            });
        }

        block_conn.commit_block();
        clarity_inst.destroy()
    };

    let without_interposing_5 = {
        let mut store = marf_kv.begin(&StacksBlockId([1 as u8; 32]), &StacksBlockId([2 as u8; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB),
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        store.test_commit();
        tracker.get_total()
    };

    let without_interposing_10 = {
        let mut store = marf_kv.begin(&StacksBlockId([2 as u8; 32]), &StacksBlockId([3 as u8; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB),
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(10)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        store.test_commit();
        tracker.get_total()
    };

    {
        let mut store = marf_kv.begin(&StacksBlockId([3 as u8; 32]), &StacksBlockId([4 as u8; 32]));
        let mut db = store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB);
        db.begin();
        db.set_variable_unknown_descriptor(
            &COST_VOTING_TESTNET_CONTRACT,
            "confirmed-proposal-count",
            Value::UInt(1),
        )
        .unwrap();
        let value = format!(
            "{{  function-contract: '{},
                 function-name: {},
                 cost-function-contract: '{},
                 cost-function-name: {},
                 confirmed-height: u1 }}",
            intercepted, "\"intercepted-function\"", cost_definer, "\"cost-definition\""
        );
        db.set_entry_unknown_descriptor(
            &COST_VOTING_TESTNET_CONTRACT,
            "confirmed-proposals",
            execute("{ confirmed-id: u0 }"),
            execute(&value),
        )
        .unwrap();
        db.commit();
        store.test_commit();
    }

    let with_interposing_5 = {
        let mut store = marf_kv.begin(&StacksBlockId([4 as u8; 32]), &StacksBlockId([5 as u8; 32]));

        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB),
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        store.test_commit();
        tracker.get_total()
    };

    let with_interposing_10 = {
        let mut store = marf_kv.begin(&StacksBlockId([5 as u8; 32]), &StacksBlockId([6 as u8; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB),
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute",
            &symbols_from_values(vec![Value::UInt(10)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        tracker.get_total()
    };

    assert!(without_interposing_5.exceeds(&with_interposing_5));
    assert!(without_interposing_10.exceeds(&with_interposing_10));

    assert_eq!(with_interposing_5, with_interposing_10);
    assert!(without_interposing_5 != without_interposing_10);
}

#[test]
fn test_cost_voting_integration() {
    let marf_kv = MarfedKV::temporary();
    let mut clarity_instance = ClarityInstance::new(false, marf_kv, ExecutionCost::max_value());
    clarity_instance
        .begin_test_genesis_block(
            &StacksBlockId::sentinel(),
            &StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            ),
            &NULL_HEADER_DB,
            &NULL_BURN_STATE_DB,
        )
        .commit_block();

    let marf_kv = clarity_instance.destroy();

    let p1 = execute("'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR");
    let p2 = execute("'SM2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQVX8X0G");

    let p1_principal = match p1 {
        Value::Principal(PrincipalData::Standard(ref data)) => data.clone(),
        _ => panic!(),
    };
    let p2_principal = match p2 {
        Value::Principal(ref data) => data.clone(),
        _ => panic!(),
    };

    let cost_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "cost-definer".into());
    let bad_cost_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "bad-cost-definer".into());
    let bad_cost_args_definer =
        QualifiedContractIdentifier::new(p1_principal.clone(), "bad-cost-args-definer".into());
    let intercepted = QualifiedContractIdentifier::new(p1_principal.clone(), "intercepted".into());
    let caller = QualifiedContractIdentifier::new(p1_principal.clone(), "caller".into());

    let mut marf_kv = {
        let mut clarity_inst = ClarityInstance::new(false, marf_kv, ExecutionCost::max_value());
        let mut block_conn = clarity_inst.begin_block(
            &StacksBlockHeader::make_index_block_hash(
                &FIRST_BURNCHAIN_CONSENSUS_HASH,
                &FIRST_STACKS_BLOCK_HASH,
            ),
            &StacksBlockId([1 as u8; 32]),
            &NULL_HEADER_DB,
            &NULL_BURN_STATE_DB,
        );

        let cost_definer_src = "
    (define-read-only (cost-definition (size uint))
       {
         runtime: u1, write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    (define-read-only (cost-definition-le (size uint))
       {
         runtime: u0, write_length: u0, write_count: u0, read_count: u0, read_length: u0
       })
    (define-read-only (cost-definition-multi-arg (a uint) (b uint) (c uint))
       {
         runtime: u1, write_length: u0, write_count: u0, read_count: u0, read_length: u0
       })

    ";

        let bad_cost_definer_src = "
    (define-data-var my-var uint u10)
    (define-read-only (cost-definition (size uint))
       {
         runtime: (var-get my-var), write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    ";

        let bad_cost_args_definer_src = "
    (define-read-only (cost-definition (a uint) (b uint))
       {
         runtime: u1, write_length: u1, write_count: u1, read_count: u1, read_length: u1
       })
    ";

        let intercepted_src = "
    (define-read-only (intercepted-function (a uint))
       (if (>= a u10)
           (+ (+ a a) (+ a a)
              (+ a a) (+ a a))
           u0))

    (define-read-only (intercepted-function2 (a uint) (b uint) (c uint))
       (- (+ a b) c))

    (define-public (non-read-only) (ok (+ 1 2 3)))
    ";

        let caller_src = "
    (define-public (execute (a uint))
       (ok (contract-call? .intercepted intercepted-function a)))
    (define-public (execute-2 (a uint))
       (ok (< a a)))
    ";

        for (contract_name, contract_src) in [
            (&cost_definer, cost_definer_src),
            (&intercepted, intercepted_src),
            (&caller, caller_src),
            (&bad_cost_definer, bad_cost_definer_src),
            (&bad_cost_args_definer, bad_cost_args_definer_src),
        ]
        .iter()
        {
            block_conn.as_transaction(|tx| {
                let (ast, analysis) = tx
                    .analyze_smart_contract(contract_name, contract_src)
                    .unwrap();
                tx.initialize_smart_contract(contract_name, &ast, contract_src, None, |_, _| false)
                    .unwrap();
                tx.save_analysis(contract_name, &analysis).unwrap();
            });
        }

        block_conn.commit_block();
        clarity_inst.destroy()
    };

    let bad_cases = vec![
        // non existent "replacement target"
        (
            PrincipalData::from(QualifiedContractIdentifier::local("non-existent").unwrap()),
            "non-existent-func",
            PrincipalData::from(cost_definer.clone()),
            "cost-definition",
        ),
        // replacement target isn't a contract principal
        (
            p1_principal.clone().into(),
            "non-existent-func",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // cost defining contract isn't a contract principal
        (
            intercepted.clone().into(),
            "intercepted-function",
            p1_principal.clone().into(),
            "cost-definition",
        ),
        // replacement function doesn't exist
        (
            intercepted.clone().into(),
            "non-existent-func",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // replacement function isn't read-only
        (
            intercepted.clone().into(),
            "non-read-only",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // "boot cost" function doesn't exist
        (
            boot_code_id("costs", false).into(),
            "non-existent-func",
            cost_definer.clone().into(),
            "cost-definition",
        ),
        // cost defining contract doesn't exist
        (
            intercepted.clone().into(),
            "intercepted-function",
            QualifiedContractIdentifier::local("non-existent")
                .unwrap()
                .into(),
            "cost-definition",
        ),
        // cost defining function doesn't exist
        (
            intercepted.clone().into(),
            "intercepted-function",
            cost_definer.clone().into(),
            "cost-definition-2",
        ),
        // cost defining contract isn't arithmetic-only
        (
            intercepted.clone().into(),
            "intercepted-function",
            bad_cost_definer.clone().into(),
            "cost-definition",
        ),
        // cost defining contract has incorrect number of arguments
        (
            intercepted.clone().into(),
            "intercepted-function",
            bad_cost_args_definer.clone().into(),
            "cost-definition",
        ),
    ];

    let bad_proposals = bad_cases.len();

    {
        let mut store = marf_kv.begin(&StacksBlockId([1 as u8; 32]), &StacksBlockId([2 as u8; 32]));

        let mut db = store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB);
        db.begin();

        db.set_variable_unknown_descriptor(
            &COST_VOTING_TESTNET_CONTRACT,
            "confirmed-proposal-count",
            Value::UInt(bad_proposals as u128),
        )
        .unwrap();

        for (ix, (intercepted_ct, intercepted_f, cost_ct, cost_f)) in
            bad_cases.into_iter().enumerate()
        {
            let value = format!(
                "{{  function-contract: '{},
                     function-name: \"{}\",
                     cost-function-contract: '{},
                     cost-function-name: \"{}\",
                     confirmed-height: u1 }}",
                intercepted_ct, intercepted_f, cost_ct, cost_f
            );
            db.set_entry_unknown_descriptor(
                &COST_VOTING_TESTNET_CONTRACT,
                "confirmed-proposals",
                execute(&format!("{{ confirmed-id: u{} }}", ix)),
                execute(&value),
            )
            .unwrap();
        }
        db.commit();
        store.test_commit();
    }

    let le_cost_without_interception = {
        let mut store = marf_kv.begin(&StacksBlockId([2 as u8; 32]), &StacksBlockId([3 as u8; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB),
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute-2",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        assert!(
            tracker.contract_call_circuits().is_empty(),
            "No contract call circuits should have been processed"
        );
        for (target, referenced_function) in tracker.cost_function_references().into_iter() {
            assert_eq!(
                &referenced_function.contract_id,
                &boot_code_id("costs", false),
                "All cost functions should still point to the boot costs"
            );
            assert_eq!(
                &referenced_function.function_name,
                target.get_name_str(),
                "All cost functions should still point to the boot costs"
            );
        }
        store.test_commit();

        tracker.get_total()
    };

    let good_cases = vec![
        (
            intercepted.clone(),
            "intercepted-function",
            cost_definer.clone(),
            "cost-definition",
        ),
        (
            boot_code_id("costs", false),
            "cost_le",
            cost_definer.clone(),
            "cost-definition-le",
        ),
        (
            intercepted.clone(),
            "intercepted-function2",
            cost_definer.clone(),
            "cost-definition-multi-arg",
        ),
    ];

    {
        let mut store = marf_kv.begin(&StacksBlockId([3 as u8; 32]), &StacksBlockId([4 as u8; 32]));

        let mut db = store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB);
        db.begin();

        let good_proposals = good_cases.len() as u128;
        db.set_variable_unknown_descriptor(
            &COST_VOTING_TESTNET_CONTRACT,
            "confirmed-proposal-count",
            Value::UInt(bad_proposals as u128 + good_proposals),
        )
        .unwrap();

        for (ix, (intercepted_ct, intercepted_f, cost_ct, cost_f)) in
            good_cases.into_iter().enumerate()
        {
            let value = format!(
                "{{ function-contract: '{},
                    function-name: \"{}\",
                    cost-function-contract: '{},
                    cost-function-name: \"{}\",
                    confirmed-height: u1 }}",
                intercepted_ct, intercepted_f, cost_ct, cost_f
            );
            db.set_entry_unknown_descriptor(
                &COST_VOTING_TESTNET_CONTRACT,
                "confirmed-proposals",
                execute(&format!("{{ confirmed-id: u{} }}", ix + bad_proposals)),
                execute(&value),
            )
            .unwrap();
        }
        db.commit();

        store.test_commit();
    }

    {
        let mut store = marf_kv.begin(&StacksBlockId([4 as u8; 32]), &StacksBlockId([5 as u8; 32]));
        let mut owned_env = OwnedEnvironment::new_max_limit(
            store.as_clarity_db(&NULL_HEADER_DB, &NULL_BURN_STATE_DB),
        );

        execute_transaction(
            &mut owned_env,
            p2_principal.clone(),
            &caller,
            "execute-2",
            &symbols_from_values(vec![Value::UInt(5)]),
        )
        .unwrap();

        let (_db, tracker) = owned_env.destruct().unwrap();

        // cost of `le` should be less now, because the proposal made it free
        assert!(le_cost_without_interception.exceeds(&tracker.get_total()));

        let circuits = tracker.contract_call_circuits();
        assert_eq!(circuits.len(), 2);

        let circuit1 = circuits.get(&(intercepted.clone(), "intercepted-function".into()));
        let circuit2 = circuits.get(&(intercepted.clone(), "intercepted-function2".into()));

        assert!(circuit1.is_some());
        assert!(circuit2.is_some());

        assert_eq!(circuit1.unwrap().contract_id, cost_definer);
        assert_eq!(circuit1.unwrap().function_name, "cost-definition");

        assert_eq!(circuit2.unwrap().contract_id, cost_definer);
        assert_eq!(circuit2.unwrap().function_name, "cost-definition-multi-arg");

        for (target, referenced_function) in tracker.cost_function_references().into_iter() {
            if target == &ClarityCostFunction::Le {
                assert_eq!(&referenced_function.contract_id, &cost_definer);
                assert_eq!(&referenced_function.function_name, "cost-definition-le");
            } else {
                assert_eq!(
                    &referenced_function.contract_id,
                    &boot_code_id("costs", false),
                    "Cost function should still point to the boot costs"
                );
                assert_eq!(
                    &referenced_function.function_name,
                    target.get_name_str(),
                    "Cost function should still point to the boot costs"
                );
            }
        }
        store.test_commit();
    };
}
