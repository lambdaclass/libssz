#![no_main]

//! Fuzz hash_tree_root for union (enum with enum_behaviour = "union").
//! Tests no-panic, determinism, and decode-then-hash correctness.

extern crate libssz as ssz;
extern crate libssz_merkle as ssz_merkle;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::SszDecode;
use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_merkle::HashTreeRoot;

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(enum_behaviour = "union")]
enum TestUnion {
    U64Val(u64),
    BoolVal(bool),
    Bytes32Val([u8; 32]),
    VecU8Val(Vec<u8>),
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    u64_val: u64,
    bool_val: bool,
    bytes32_val: [u8; 32],
    vec_u8_val: Vec<u8>,
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap VecU8Val for performance
    let vec_u8: Vec<u8> = input.vec_u8_val.into_iter().take(1024).collect();

    // Construct each variant and hash — must not panic
    let u64_variant = TestUnion::U64Val(input.u64_val);
    let bool_variant = TestUnion::BoolVal(input.bool_val);
    let bytes32_variant = TestUnion::Bytes32Val(input.bytes32_val);
    let vec_variant = TestUnion::VecU8Val(vec_u8);

    let _ = u64_variant.hash_tree_root();
    let _ = bool_variant.hash_tree_root();
    let _ = bytes32_variant.hash_tree_root();
    let _ = vec_variant.hash_tree_root();

    // Verify determinism: same input → same root
    let root1 = TestUnion::U64Val(input.u64_val).hash_tree_root();
    let root2 = TestUnion::U64Val(input.u64_val).hash_tree_root();
    assert_eq!(root1, root2, "U64Val HTR not deterministic");

    let root1 = TestUnion::BoolVal(input.bool_val).hash_tree_root();
    let root2 = TestUnion::BoolVal(input.bool_val).hash_tree_root();
    assert_eq!(root1, root2, "BoolVal HTR not deterministic");

    let root1 = TestUnion::Bytes32Val(input.bytes32_val).hash_tree_root();
    let root2 = TestUnion::Bytes32Val(input.bytes32_val).hash_tree_root();
    assert_eq!(root1, root2, "Bytes32Val HTR not deterministic");

    // Decode from raw bytes; if successful, hash_tree_root must not panic
    if let Ok(val) = TestUnion::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
});
