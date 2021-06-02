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

use vm::types::signatures::{ListTypeData, SequenceSubtype};
use vm::types::TypeSignature::{BoolType, IntType, SequenceType, UIntType};
use vm::types::{TypeSignature, Value};

use std::convert::TryInto;
use vm::analysis::errors::CheckError;
use vm::errors::{CheckErrors, Error, RuntimeErrorType};
use vm::execute;

#[test]
fn test_simple_list_admission() {
    let defines = "(define-private (square (x int)) (* x x))
         (define-private (square-list (x (list 4 int))) (map square x))";
    let t1 = format!("{} (square-list (list 1 2 3 4))", defines);
    let t2 = format!("{} (square-list (list))", defines);
    let t3 = format!("{} (square-list (list 1 2 3 4 5))", defines);

    let expected = Value::list_from(vec![
        Value::Int(1),
        Value::Int(4),
        Value::Int(9),
        Value::Int(16),
    ])
    .unwrap();

    assert_eq!(expected, execute(&t1).unwrap().unwrap());
    assert_eq!(
        Value::list_from(vec![]).unwrap(),
        execute(&t2).unwrap().unwrap()
    );
    let err = execute(&t3).unwrap_err();
    assert!(match err {
        Error::Unchecked(CheckErrors::TypeValueError(_, _)) => true,
        _ => {
            eprintln!("Expected TypeError, but found: {:?}", err);
            false
        }
    });
}

#[test]
fn test_index_of() {
    let good = [
        "(index-of (list 1 2 3 4 5 4) 100)",
        "(index-of (list 1 2 3 4 5 4) 4)",
        "(index-of \"abcd\" \"a\")",
        "(index-of u\"abcd\" u\"a\")",
        "(index-of 0xfedb 0xdb)",
        "(index-of \"abcd\" \"\")",
        "(index-of u\"abcd\" u\"\")",
        "(index-of 0xfedb 0x)",
        "(index-of \"abcd\" \"z\")",
        "(index-of u\"abcd\" u\"e\")",
        "(index-of 0xfedb 0x01)",
    ];

    let expected = [
        "none",
        "(some u3)",
        "(some u0)",
        "(some u0)",
        "(some u1)",
        "none",
        "none",
        "none",
        "none",
        "none",
        "none",
    ];

    for (good_test, expected) in good.iter().zip(expected.iter()) {
        assert_eq!(
            expected,
            &format!("{}", execute(&good_test).unwrap().unwrap())
        );
    }

    let bad = [
        "(index-of 3 \"a\")",
        "(index-of 0xfedb \"a\")",
        "(index-of u\"a\" \"a\")",
        "(index-of \"a\" u\"a\")",
    ];

    let bad_expected = [
        CheckErrors::ExpectedSequence(TypeSignature::IntType),
        CheckErrors::TypeValueError(
            TypeSignature::min_buffer(),
            execute("\"a\"").unwrap().unwrap(),
        ),
        CheckErrors::TypeValueError(
            TypeSignature::min_string_utf8(),
            execute("\"a\"").unwrap().unwrap(),
        ),
        CheckErrors::TypeValueError(
            TypeSignature::min_string_ascii(),
            execute("u\"a\"").unwrap().unwrap(),
        ),
    ];

    for (bad_test, expected) in bad.iter().zip(bad_expected.iter()) {
        match execute(&bad_test).unwrap_err() {
            Error::Unchecked(check_error) => {
                assert_eq!(&check_error, expected);
            }
            _ => unreachable!("Should have raised unchecked errors"),
        }
    }
}

#[test]
fn test_element_at() {
    let good = [
        "(element-at (list 1 2 3 4 5) u100)",
        "(element-at \"abcd\" u100)",
        "(element-at 0xfedb u100)",
        "(element-at u\"abcd\" u100)",
        "(element-at (list 1 2 3 4 5) u0)",
        "(element-at (list 1 2 3 4 5) u1)",
        "(element-at \"abcd\" u1)",
        "(element-at 0xfedb u1)",
        "(element-at u\"abcd\" u1)",
    ];

    let expected = [
        "none",
        "none",
        "none",
        "none",
        "(some 1)",
        "(some 2)",
        "(some \"b\")",
        "(some 0xdb)",
        "(some u\"b\")",
    ];

    for (good_test, expected) in good.iter().zip(expected.iter()) {
        assert_eq!(
            expected,
            &format!("{}", execute(&good_test).unwrap().unwrap())
        );
    }

    let bad = ["(element-at 3 u1)", "(element-at (list 1 2 3) 1)"];

    let bad_expected = [
        CheckErrors::ExpectedSequence(TypeSignature::IntType),
        CheckErrors::TypeValueError(TypeSignature::UIntType, Value::Int(1)),
    ];

    for (bad_test, expected) in bad.iter().zip(bad_expected.iter()) {
        match execute(&bad_test).unwrap_err() {
            Error::Unchecked(check_error) => {
                assert_eq!(&check_error, expected);
            }
            _ => unreachable!("Should have raised unchecked errors"),
        }
    }
}

#[test]
fn test_string_ascii_admission() {
    let defines = "(define-private (set-name (x (string-ascii 11))) x)";
    let t1 = format!("{} (set-name \"hello world\")", defines);

    let expected = Value::string_ascii_from_bytes("hello world".into()).unwrap();

    assert_eq!(expected, execute(&t1).unwrap().unwrap());
}

#[test]
fn test_string_utf8_admission() {
    let defines = "(define-private (set-name (x (string-utf8 14))) x)";
    let t1 = format!("{} (set-name u\"my 2 \\u{{c2a2}} (cents)\")", defines);

    let expected =
        Value::string_utf8_from_string_utf8_literal("my 2 \\u{c2a2} (cents)".into()).unwrap();

    assert_eq!(expected, execute(&t1).unwrap().unwrap());
}

#[test]
fn test_string_ascii_map() {
    let defines =
        "(define-private (replace-a-with-b (c (string-ascii 1))) (if (is-eq \"a\" c) \"b\" c))";
    let t1 = format!("{} (map replace-a-with-b \"ababab\")", defines);

    let expected = Value::list_from(vec![
        Value::string_ascii_from_bytes("b".into()).unwrap(),
        Value::string_ascii_from_bytes("b".into()).unwrap(),
        Value::string_ascii_from_bytes("b".into()).unwrap(),
        Value::string_ascii_from_bytes("b".into()).unwrap(),
        Value::string_ascii_from_bytes("b".into()).unwrap(),
        Value::string_ascii_from_bytes("b".into()).unwrap(),
    ])
    .unwrap();

    assert_eq!(expected, execute(&t1).unwrap().unwrap());
}

#[test]
fn test_string_utf8_map() {
    let defines =
        "(define-private (replace-dog-with-fox (c (string-utf8 1))) (if (is-eq u\"\\u{1F436}\" c) u\"\\u{1F98A}\" c))";
    let t1 = format!(
        "{} (map replace-dog-with-fox u\"fox \\u{{1F436}}\")",
        defines
    );

    let expected = Value::list_from(vec![
        Value::string_utf8_from_bytes("f".into()).unwrap(),
        Value::string_utf8_from_bytes("o".into()).unwrap(),
        Value::string_utf8_from_bytes("x".into()).unwrap(),
        Value::string_utf8_from_bytes(" ".into()).unwrap(),
        Value::string_utf8_from_bytes("🦊".into()).unwrap(),
    ])
    .unwrap();

    assert_eq!(expected, execute(&t1).unwrap().unwrap());
}

#[test]
fn test_string_ascii_filter() {
    let defines = "(define-private (remove-a (c (string-ascii 1))) (not (is-eq \"a\" c)))";
    let t1 = format!("{} (filter remove-a \"ababab\")", defines);

    let expected = Value::string_ascii_from_bytes("bbb".into()).unwrap();

    assert_eq!(expected, execute(&t1).unwrap().unwrap());
}

#[test]
fn test_string_utf8_filter() {
    let defines = "(define-private (keep-dog (c (string-utf8 1))) (is-eq u\"\\u{1F436}\" c))";
    let t1 = format!(
        "{} (filter keep-dog u\"fox \\u{{1F98A}} \\u{{1F436}}\")",
        defines
    );

    let expected = Value::string_utf8_from_bytes("🐶".into()).unwrap();

    assert_eq!(expected, execute(&t1).unwrap().unwrap());
}

#[test]
fn test_string_ascii_fold() {
    let test1 =
        "(define-private (merge-str (x (string-ascii 1)) (acc (string-ascii 5))) (concat acc x))
        (fold merge-str (list \"A\" \"B\" \"C\" \"D\" \"E\") \"\")";

    let expected = Value::string_ascii_from_bytes("ABCDE".into()).unwrap();

    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_string_utf8_fold() {
    let test1 =
        "(define-private (build-face-palm (x (string-utf8 1)) (acc (string-utf8 5))) (concat acc x))
         (fold build-face-palm (list u\"\\u{1F926}\" u\"\\u{1F3FC}\" u\"\\u{200D}\" u\"\\u{2642}\" u\"\\u{FE0F}\") u\"\")";

    let expected = Value::string_utf8_from_bytes("🤦🏼‍♂️".into()).unwrap();

    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_string_ascii_concat() {
    let test1 = "(concat (concat \"A\" \"B\") \"C\")";

    let expected = Value::string_ascii_from_bytes("ABC".into()).unwrap();

    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_string_utf8_concat() {
    let test1 =
        "(concat (concat (concat (concat u\"\\u{1F926}\" u\"\\u{1F3FC}\") u\"\\u{200D}\") u\"\\u{2642}\") u\"\\u{FE0F}\")";

    let expected = Value::string_utf8_from_bytes("🤦🏼‍♂️".into()).unwrap();

    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_string_ascii_get_len() {
    let test1 = "(len \"ABCDE\")";
    let expected = Value::UInt(5);
    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_string_utf8_get_len() {
    let test1 = "(len u\"ABCDE\\u{1F926}\\u{1F3FC}\\u{200D}\\u{2642}\\u{FE0F}\")";
    let expected = Value::UInt(10);
    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_string_ascii_max_len() {
    let tests = [
        "(as-max-len? \"ABC\" u3)",
        "(as-max-len? \"ABC\" u2)",
        "(as-max-len? \"ABC\" u4)",
    ];

    let expected = [
        Value::some(Value::string_ascii_from_bytes("ABC".into()).unwrap()).unwrap(),
        Value::none(),
        Value::some(Value::string_ascii_from_bytes("ABC".into()).unwrap()).unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }
}

#[test]
fn test_string_utf8_max_len() {
    let tests = [
        "(as-max-len? u\"ABCDE\\u{1F926}\\u{1F3FC}\\u{200D}\\u{2642}\\u{FE0F}\" u10)",
        "(as-max-len? u\"ABCDE\\u{1F926}\\u{1F3FC}\\u{200D}\\u{2642}\\u{FE0F}\" u9)",
        "(as-max-len? u\"ABCDE\\u{1F926}\\u{1F3FC}\\u{200D}\\u{2642}\\u{FE0F}\" u11)",
    ];

    let expected = [
        Value::some(Value::string_utf8_from_bytes("ABCDE🤦🏼‍♂️".into()).unwrap()).unwrap(),
        Value::none(),
        Value::some(Value::string_utf8_from_bytes("ABCDE🤦🏼‍♂️".into()).unwrap()).unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }
}

#[test]
fn test_simple_map_list() {
    let test1 = "(define-private (square (x int)) (* x x))
         (map square (list 1 2 3 4))";

    let expected = Value::list_from(vec![
        Value::Int(1),
        Value::Int(4),
        Value::Int(9),
        Value::Int(16),
    ])
    .unwrap();

    assert_eq!(expected, execute(test1).unwrap().unwrap());

    // let's test lists of lists.
    let test2 = "(define-private (multiply (x int) (acc int)) (* x acc))
                 (define-private (multiply-all (x (list 10 int))) (fold multiply x 1))
                 (map multiply-all (list (list 1 1 1) (list 2 2 1) (list 3 3) (list 2 2 2 2)))";
    assert_eq!(expected, execute(test2).unwrap().unwrap());

    // let's test empty lists.
    let test2 = "(define-private (double (x int)) (* x 2))
                 (map double (list))";
    assert_eq!(
        Value::list_from(vec![]).unwrap(),
        execute(test2).unwrap().unwrap()
    );
}

#[test]
fn test_variadic_map_list() {
    let test = "(define-private (area (w int) (h int)) (* w h))
         (map area (list 5 10 1 2) (list 5 2 30 3))";

    let expected = Value::list_from(vec![
        Value::Int(25),
        Value::Int(20),
        Value::Int(30),
        Value::Int(6),
    ])
    .unwrap();
    assert_eq!(expected, execute(test).unwrap().unwrap());

    let test = "(define-private (u+ (a uint) (b int)) (+ a (to-uint b)))
    (map u+ (list u5 u10 u1 u2) (list 5 2 30 3))";

    let expected = Value::list_from(vec![
        Value::UInt(10),
        Value::UInt(12),
        Value::UInt(31),
        Value::UInt(5),
    ])
    .unwrap();
    assert_eq!(expected, execute(test).unwrap().unwrap());

    let test = "(map + (list 5 10) (list 5 2 30 3))";

    let expected = Value::list_from(vec![Value::Int(10), Value::Int(12)]).unwrap();
    assert_eq!(expected, execute(test).unwrap().unwrap());

    let test = "(map pow (list 2 2 2 2) (list 1 2 3 4 5 6 7))";

    let expected = Value::list_from(vec![
        Value::Int(2),
        Value::Int(4),
        Value::Int(8),
        Value::Int(16),
    ])
    .unwrap();
    assert_eq!(expected, execute(test).unwrap().unwrap());
}

#[test]
fn test_simple_map_append() {
    let tests = [
        "(append (list 1 2) 6)",
        "(append (list) 1)",
        "(append (append (list) 1) 2)",
    ];

    let expected = [
        Value::list_from(vec![Value::Int(1), Value::Int(2), Value::Int(6)]).unwrap(),
        Value::list_from(vec![Value::Int(1)]).unwrap(),
        Value::list_from(vec![Value::Int(1), Value::Int(2)]).unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }

    assert_eq!(
        execute("(append (append (list) 1) u2)").unwrap_err(),
        CheckErrors::TypeValueError(IntType, Value::UInt(2)).into()
    );
}

#[test]
fn test_slice_list() {
    let tests = [
        "(slice (list 2 3 4 5 6 7 8) u0 u3)",
        "(slice (list u0 u1 u2 u3 u4) u3 u2)",
        // "(append (append (list) 1) 2)",
    ];

    let expected = [
        Value::some(Value::list_from(vec![Value::Int(2), Value::Int(3), Value::Int(4)]).unwrap())
            .unwrap(),
        Value::some(Value::list_from(vec![Value::UInt(3), Value::UInt(4)]).unwrap()).unwrap(),
        // Value::list_from(vec![Value::Int(1), Value::Int2)]).unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }

    // assert_eq!(
    //     execute("(append (append (list) 1) u2)").unwrap_err(),
    //     CheckErrors::TypeValueError(IntType, Value::UInt(2)).into()
    // );
}

// #[test]
// fn test_slice_list() {
//     let good = ["(slice (list 2 3 4 5 6 7 8) u0 u3)", "(slice (list u0 u1 u2 u3 u4) u3 u2)"];
//     let expected = ["(list 3 int)", "(list 2 uint)"];

//     for (good_test, expected) in good.iter().zip(expected.iter()) {
//         assert_eq!(
//             expected,
//             &format!("{}", type_check_helper(&good_test).unwrap())
//         );
//     }

//     let bad = [
//         "(slice (list 2 3) 3 u4)",
//         "(slice (list 2 3) u3 4)",
//         "(slice (list u0) u1)",
//     ];

//     let bad_expected = [
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::IncorrectArgumentCount(3, 2),
//     ];
//     for (bad_test, expected) in bad.iter().zip(bad_expected.iter()) {
//         assert_eq!(expected, &type_check_helper(&bad_test).unwrap_err().err);
//     }
// }

// #[test]
// fn test_slice_buff() {
//     let good = ["(slice 0x000102030405 u0 u3)", "(slice 0x000102030405 u3 u2)"];
//     let expected = ["(buff 3)", "(buff 2)"];

//     for (good_test, expected) in good.iter().zip(expected.iter()) {
//         assert_eq!(
//             expected,
//             &format!("{}", type_check_helper(&good_test).unwrap())
//         );
//     }

//     let bad = [
//         "(slice 0x000102030405 3 u4)",
//         "(slice 0x000102030405 u3 4)",
//         "(slice 0x000102030405 u1)",
//     ];

//     let bad_expected = [
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::IncorrectArgumentCount(3, 2),
//     ];
//     for (bad_test, expected) in bad.iter().zip(bad_expected.iter()) {
//         assert_eq!(expected, &type_check_helper(&bad_test).unwrap_err().err);
//     }
// }

// #[test]
// fn test_slice_ascii() {
//     let good = ["(slice \"blockstack\" u4 u5)", "(slice \"blockstack\" u0 u5)"];
//     let expected = ["(string-ascii 5)", "(string-ascii 5)"];

//     for (good_test, expected) in good.iter().zip(expected.iter()) {
//         assert_eq!(
//             expected,
//             &format!("{}", type_check_helper(&good_test).unwrap())
//         );
//     }

//     let bad = [
//         "(slice \"blockstack\" 3 u4)",
//         "(slice \"blockstack\" u3 4)",
//         "(slice \"blockstack\" u1)",
//     ];

//     let bad_expected = [
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::IncorrectArgumentCount(3, 2),
//     ];
//     for (bad_test, expected) in bad.iter().zip(bad_expected.iter()) {
//         assert_eq!(expected, &type_check_helper(&bad_test).unwrap_err().err);
//     }
// }

// #[test]
// fn test_slice_utf8() {
//     let good = ["(slice u\"blockstack\" u4 u5)", "(slice u\"blockstack\" u4 u5)"];
//     let expected = ["(string-utf8 5)", "(string-utf8 5)"];

//     for (good_test, expected) in good.iter().zip(expected.iter()) {
//         assert_eq!(
//             expected,
//             &format!("{}", type_check_helper(&good_test).unwrap())
//         );
//     }

//     let bad = [
//         "(slice u\"blockstack\" 3 u4)",
//         "(slice u\"blockstack\" u3 4)",
//         "(slice u\"blockstack\" u1)",
//     ];

//     let bad_expected = [
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::TypeError(UIntType, IntType),
//         CheckErrors::IncorrectArgumentCount(3, 2),
//     ];
//     for (bad_test, expected) in bad.iter().zip(bad_expected.iter()) {
//         assert_eq!(expected, &type_check_helper(&bad_test).unwrap_err().err);
//     }
// }

#[test]
fn test_simple_list_concat() {
    let tests = [
        "(concat (list 1 2) (list 4 8))",
        "(concat (list 1) (list 4 8))",
        "(concat (list 1 9 0) (list))",
        "(concat (list) (list))",
        "(concat (list (list 1) (list 2)) (list (list 3)))",
    ];

    let expected = [
        Value::list_from(vec![
            Value::Int(1),
            Value::Int(2),
            Value::Int(4),
            Value::Int(8),
        ])
        .unwrap(),
        Value::list_from(vec![Value::Int(1), Value::Int(4), Value::Int(8)]).unwrap(),
        Value::list_from(vec![Value::Int(1), Value::Int(9), Value::Int(0)]).unwrap(),
        Value::list_from(vec![]).unwrap(),
        Value::list_from(vec![
            Value::list_from(vec![Value::Int(1)]).unwrap(),
            Value::list_from(vec![Value::Int(2)]).unwrap(),
            Value::list_from(vec![Value::Int(3)]).unwrap(),
        ])
        .unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }

    assert_eq!(
        execute("(concat (list 1) (list u4 u8))").unwrap_err(),
        CheckErrors::TypeError(IntType, UIntType).into()
    );

    assert_eq!(
        execute("(concat (list 1) 3)").unwrap_err(),
        RuntimeErrorType::BadTypeConstruction.into()
    );

    assert_eq!(
        execute("(concat (list 1) \"1\")").unwrap_err(),
        RuntimeErrorType::BadTypeConstruction.into()
    );
}

#[test]
fn test_simple_buff_concat() {
    let tests = [
        "(concat 0x303132 0x3334)",
        "(concat 0x00 0x00)",
        "(concat 0x00 0x31)",
        "(concat 0x31 0x00)",
    ];

    let expected = [
        Value::buff_from(vec![48, 49, 50, 51, 52]).unwrap(),
        Value::buff_from(vec![0, 0]).unwrap(),
        Value::buff_from(vec![0, 49]).unwrap(),
        Value::buff_from(vec![49, 0]).unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }

    assert_eq!(
        execute("(concat 0x31 3)").unwrap_err(),
        RuntimeErrorType::BadTypeConstruction.into()
    );

    assert_eq!(
        execute("(concat 0x31 (list 1))").unwrap_err(),
        RuntimeErrorType::BadTypeConstruction.into()
    );
}

#[test]
fn test_simple_buff_assert_max_len() {
    let tests = [
        "(as-max-len? 0x313233 u3)",
        "(as-max-len? 0x313233 u2)",
        "(as-max-len? 0x313233 u5)",
    ];

    let expected = [
        Value::some(Value::buff_from(vec![49, 50, 51]).unwrap()).unwrap(),
        Value::none(),
        Value::some(Value::buff_from(vec![49, 50, 51]).unwrap()).unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }

    assert_eq!(
        execute("(as-max-len? 0x313233)").unwrap_err(),
        CheckErrors::IncorrectArgumentCount(2, 1).into()
    );

    assert_eq!(
        execute("(as-max-len? 0x313233 3)").unwrap_err(),
        CheckErrors::TypeError(UIntType, IntType).into()
    );

    assert_eq!(
        execute("(as-max-len? 1 u3)").unwrap_err(),
        CheckErrors::ExpectedSequence(IntType).into()
    );

    assert_eq!(
        execute("(as-max-len? 0x313233 0x31)").unwrap_err(),
        CheckErrors::TypeError(
            UIntType,
            SequenceType(SequenceSubtype::BufferType(1_u32.try_into().unwrap()))
        )
        .into()
    );
}

#[test]
fn test_simple_list_assert_max_len() {
    let tests = [
        "(as-max-len? (list 1 2 3) u3)",
        "(as-max-len? (list 1 2 3) u2)",
        "(as-max-len? (list 1 2 3) u5)",
    ];

    let expected = [
        Value::some(Value::list_from(vec![Value::Int(1), Value::Int(2), Value::Int(3)]).unwrap())
            .unwrap(),
        Value::none(),
        Value::some(Value::list_from(vec![Value::Int(1), Value::Int(2), Value::Int(3)]).unwrap())
            .unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }
}

#[test]
fn test_simple_map_buffer() {
    let test1 = "(define-private (incr (x (buff 1))) 0x31)
         (map incr 0x30303030)";

    let expected = Value::list_from(vec![
        Value::buff_from(vec![49]).unwrap(),
        Value::buff_from(vec![49]).unwrap(),
        Value::buff_from(vec![49]).unwrap(),
        Value::buff_from(vec![49]).unwrap(),
    ])
    .unwrap();
    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_simple_filter_list() {
    let test1 = "(define-private (test (x int)) (is-eq 0 (mod x 2)))
                 (filter test (list 1 2 3 4 5))";

    let bad_tests = [
        "(filter 123 (list 123))",   // must have function name supplied
        "(filter not (list 123) 3)", // must be 2 args
        "(filter +)",                // must be 2 args
        "(filter not false)",        // must supply list
        "(filter - (list 1 2 3))",
    ]; // must return bool

    let expected = Value::list_from(vec![Value::Int(2), Value::Int(4)]).unwrap();

    assert_eq!(expected, execute(test1).unwrap().unwrap());

    for t in bad_tests.iter() {
        execute(t).unwrap_err();
    }
}

#[test]
fn test_simple_filter_buffer() {
    let test1 = "(define-private (test (x (buff 1))) (not (is-eq x 0x30)))
                 (filter test 0x303030313233)";

    let expected = Value::buff_from(vec![49, 50, 51]).unwrap();
    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_list_tuple_admission() {
    let test = "(define-private (bufferize (x int)) (if (is-eq x 1) 0x616263 0x6162))
         (define-private (tuplize (x int))
           (tuple (value (bufferize x))))
         (map tuplize (list 0 1 0 1 0 1))";

    let expected_type = "(list (tuple (value 0x303132))
               (tuple (value 0x303132))
               (tuple (value 0x303132))
               (tuple (value 0x303132))
               (tuple (value 0x303132))
               (tuple (value 0x303132)))";

    let not_expected_type = "(list (tuple (value 0x3031))
               (tuple (value 0x3032))
               (tuple (value 0x3132))
               (tuple (value 0x3132))
               (tuple (value 0x3031))
               (tuple (value 0x3032)))";

    let result_type = TypeSignature::type_of(&execute(test).unwrap().unwrap());
    let expected_type = TypeSignature::type_of(&execute(expected_type).unwrap().unwrap());
    let testing_value = &execute(not_expected_type).unwrap().unwrap();
    let not_expected_type = TypeSignature::type_of(testing_value);

    assert_eq!(expected_type, result_type);
    assert!(not_expected_type != result_type);
    assert!(result_type.admits(&testing_value));
}

#[test]
fn test_simple_folds_list() {
    let test1 = "(define-private (multiply-all (x int) (acc int)) (* x acc))
         (fold multiply-all (list 1 2 3 4) 1)";

    let expected = Value::Int(24);

    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_simple_folds_string() {
    let tests =
        ["(define-private (get-len (x (string-ascii 1)) (acc int)) (+ acc 1))
         (fold get-len \"blockstack\" 0)",
        "(define-private (slice-v1 (x (string-ascii 1)) (acc (tuple (limit uint) (cursor uint) (data (string-ascii 10)))))
            (if (< (get cursor acc) (get limit acc))
                (let ((data (default-to (get data acc) (as-max-len? (concat (get data acc) x) u10))))
                    (tuple (limit (get limit acc)) (cursor (+ u1 (get cursor acc))) (data data))) 
                acc))
        (get data (fold slice-v1 \"0123456789\" (tuple (limit u5) (cursor u0) (data \"\"))))"];

    let expected = [
        Value::Int(10),
        Value::string_ascii_from_bytes(vec![48, 49, 50, 51, 52]).unwrap(),
    ];

    for (test, expected) in tests.iter().zip(expected.iter()) {
        assert_eq!(expected.clone(), execute(test).unwrap().unwrap());
    }
}

#[test]
fn test_native_len() {
    let test1 = "(len (list 1 2 3 4))";
    let expected = Value::UInt(4);
    assert_eq!(expected, execute(test1).unwrap().unwrap());
}

#[test]
fn test_buff_len() {
    let test1 = "(len \"blockstack\")";
    let expected = Value::UInt(10);
    assert_eq!(expected, execute(test1).unwrap().unwrap());

    let test2 = "(len 0x)";
    let expected = Value::UInt(0);
    assert_eq!(expected, execute(test2).unwrap().unwrap());
}

#[test]
fn test_construct_bad_list() {
    let test1 = "(list 1 2 3 true)";
    assert_eq!(
        execute(test1).unwrap_err(),
        CheckErrors::TypeError(IntType, BoolType).into()
    );

    let test2 = "(define-private (bad-function (x int)) (if (is-eq x 1) true x))
                 (map bad-function (list 0 1 2 3))";
    assert_eq!(
        execute(test2).unwrap_err(),
        CheckErrors::TypeError(IntType, BoolType).into()
    );

    let bad_2d_list = "(list (list 1 2 3) (list true false true))";
    let bad_high_order_list = "(list (list 1 2 3) (list (list 1 2 3)))";

    assert_eq!(
        execute(bad_2d_list).unwrap_err(),
        CheckErrors::TypeError(IntType, BoolType).into()
    );
    assert_eq!(
        execute(bad_high_order_list).unwrap_err(),
        CheckErrors::TypeError(IntType, TypeSignature::from("(list 3 int)")).into()
    );
}

#[test]
fn test_eval_func_arg_panic() {
    let test1 = "(fold (lambda (x y) (* x y)) (list 1 2 3 4) 1)";
    let e: Error = CheckErrors::ExpectedName.into();
    assert_eq!(e, execute(test1).unwrap_err());

    let test2 = "(map (lambda (x) (* x x)) (list 1 2 3 4))";
    let e: Error = CheckErrors::ExpectedName.into();
    assert_eq!(e, execute(test2).unwrap_err());

    let test3 = "(map square (list 1 2 3 4) 2)";
    let e: Error = CheckErrors::UndefinedFunction("square".to_string()).into();
    assert_eq!(e, execute(test3).unwrap_err());

    let test4 = "(define-private (multiply-all (x int) (acc int)) (* x acc))
         (fold multiply-all (list 1 2 3 4))";
    let e: Error = CheckErrors::IncorrectArgumentCount(3, 2).into();
    assert_eq!(e, execute(test4).unwrap_err());

    let test5 = "(map + (list 1 2 3 4) 2)";
    let e: Error = CheckErrors::ExpectedSequence(IntType).into();
    assert_eq!(e, execute(test5).unwrap_err());
}
