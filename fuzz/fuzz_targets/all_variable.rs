#![no_main]

//! Fuzz target for all-variable-field SSZ containers: stresses offset-only fixed section.

extern crate libssz as ssz;
extern crate libssz_merkle as ssz_merkle;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct AllVariable {
    a: Vec<u8>,
    b: Vec<u64>,
    c: Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct AllVariableLarge {
    f1: Vec<u8>,
    f2: Vec<u8>,
    f3: Vec<u64>,
    f4: Vec<u8>,
    f5: Vec<u64>,
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    a: Vec<u8>,
    b: Vec<u64>,
    c: Vec<u8>,
    f1: Vec<u8>,
    f2: Vec<u8>,
    f3: Vec<u64>,
    f4: Vec<u8>,
    f5: Vec<u64>,
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap sizes for performance
    let a: Vec<u8> = input.a[..input.a.len().min(512)].to_vec();
    let b: Vec<u64> = input.b[..input.b.len().min(128)].to_vec();
    let c: Vec<u8> = input.c[..input.c.len().min(512)].to_vec();
    let f1: Vec<u8> = input.f1[..input.f1.len().min(512)].to_vec();
    let f2: Vec<u8> = input.f2[..input.f2.len().min(512)].to_vec();
    let f3: Vec<u64> = input.f3[..input.f3.len().min(128)].to_vec();
    let f4: Vec<u8> = input.f4[..input.f4.len().min(512)].to_vec();
    let f5: Vec<u64> = input.f5[..input.f5.len().min(128)].to_vec();

    // -- No-panic decode from raw bytes --
    let _ = AllVariable::from_ssz_bytes(&input.raw);
    let _ = AllVariableLarge::from_ssz_bytes(&input.raw);

    // -- Structured roundtrip: AllVariable --
    let av = AllVariable { a, b, c };
    let encoded = av.to_ssz();
    let decoded = AllVariable::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, av, "AllVariable roundtrip");

    // -- Structured roundtrip: AllVariableLarge --
    let avl = AllVariableLarge { f1, f2, f3, f4, f5 };
    let encoded = avl.to_ssz();
    let decoded = AllVariableLarge::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, avl, "AllVariableLarge roundtrip");
});
