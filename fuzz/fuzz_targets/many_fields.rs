#![no_main]

//! Fuzz target for containers with many fields — stresses the derive macro's field-count handling.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct ManyFields {
    f1: u64,
    f2: Vec<u8>,
    f3: bool,
    f4: [u8; 32],
    f5: Vec<u64>,
    f6: u32,
    f7: Vec<u8>,
    f8: u64,
    f9: bool,
    f10: [u8; 32],
    f11: Vec<u8>,
    f12: u64,
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    f1: u64,
    f2: Vec<u8>,
    f3: bool,
    f4: [u8; 32],
    f5: Vec<u64>,
    f6: u32,
    f7: Vec<u8>,
    f8: u64,
    f9: bool,
    f10: [u8; 32],
    f11: Vec<u8>,
    f12: u64,
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap sizes for performance
    let f2: Vec<u8> = input.f2[..core::cmp::min(input.f2.len(), 256)].to_vec();
    let f5: Vec<u64> = input.f5[..core::cmp::min(input.f5.len(), 64)].to_vec();
    let f7: Vec<u8> = input.f7[..core::cmp::min(input.f7.len(), 256)].to_vec();
    let f11: Vec<u8> = input.f11[..core::cmp::min(input.f11.len(), 256)].to_vec();

    // -- No-panic decode from raw bytes --
    let _ = ManyFields::from_ssz_bytes(&input.raw);

    // -- Structured roundtrip --
    let mf = ManyFields {
        f1: input.f1,
        f2,
        f3: input.f3,
        f4: input.f4,
        f5,
        f6: input.f6,
        f7,
        f8: input.f8,
        f9: input.f9,
        f10: input.f10,
        f11,
        f12: input.f12,
    };
    let encoded = mf.to_ssz();
    let decoded = ManyFields::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, mf, "ManyFields roundtrip");
});
