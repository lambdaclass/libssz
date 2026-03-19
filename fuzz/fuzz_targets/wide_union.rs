#![no_main]

//! Fuzz target for wide unions (8+ variants): stresses selector byte logic near boundary 127.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
#[ssz(enum_behaviour = "union")]
enum WideUnion {
    V0(u64),
    V1(bool),
    V2([u8; 32]),
    V3(Vec<u8>),
    V4(u8),
    V5(u16),
    V6(u32),
    V7(u128),
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    payload: Vec<u8>,
    // Fields for constructing each variant
    v0: u64,
    v1: bool,
    v2: [u8; 32],
    v3: Vec<u8>,
    v4: u8,
    v5: u16,
    v6: u32,
    v7: u128,
}

fuzz_target!(|input: FuzzInput| {
    let v3: Vec<u8> = input.v3[..input.v3.len().min(512)].to_vec();

    // -- No-panic decode from raw bytes (covers all selector values 0-255) --
    let raw = &input.payload;
    let _ = WideUnion::from_ssz_bytes(raw);

    // -- Explicit boundary selector tests: must not panic --
    for selector in [126u8, 127, 128, 255] {
        let mut bytes = vec![selector];
        if input.payload.len() > 1 {
            bytes.extend_from_slice(&input.payload[1..input.payload.len().min(64)]);
        }
        let _ = WideUnion::from_ssz_bytes(&bytes);
    }

    // -- Structured roundtrip for each variant --
    let variants: [WideUnion; 8] = [
        WideUnion::V0(input.v0),
        WideUnion::V1(input.v1),
        WideUnion::V2(input.v2),
        WideUnion::V3(v3),
        WideUnion::V4(input.v4),
        WideUnion::V5(input.v5),
        WideUnion::V6(input.v6),
        WideUnion::V7(input.v7),
    ];
    for variant in variants {
        let encoded = variant.to_ssz();
        let decoded = WideUnion::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, variant, "WideUnion roundtrip");
    }
});
