#![no_main]

//! Fuzz target for variable-size SSZ containers: roundtrip encode/decode and no-panic decode.

extern crate libssz as ssz;
extern crate libssz_merkle as ssz_merkle;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct VariableContainer {
    id: u64,
    data: Vec<u8>,
    flag: bool,
    extra: Vec<u64>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct MixedContainer {
    fixed_field: [u8; 32],
    items: Vec<u8>,
    count: u64,
    labels: Vec<u8>,
    active: bool,
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    id: u64,
    data: Vec<u8>,
    flag: bool,
    extra: Vec<u64>,
    fixed_field: [u8; 32],
    items: Vec<u8>,
    count: u64,
    labels: Vec<u8>,
    active: bool,
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap sizes for performance
    let data: Vec<u8> = if input.data.len() > 1024 {
        input.data[..1024].to_vec()
    } else {
        input.data.clone()
    };
    let extra: Vec<u64> = if input.extra.len() > 256 {
        input.extra[..256].to_vec()
    } else {
        input.extra.clone()
    };
    let items: Vec<u8> = if input.items.len() > 1024 {
        input.items[..1024].to_vec()
    } else {
        input.items.clone()
    };
    let labels: Vec<u8> = if input.labels.len() > 1024 {
        input.labels[..1024].to_vec()
    } else {
        input.labels.clone()
    };

    // -- No-panic decode from raw bytes --
    let _ = VariableContainer::from_ssz_bytes(&input.raw);
    let _ = MixedContainer::from_ssz_bytes(&input.raw);

    // -- Structured roundtrip: VariableContainer --
    let vc = VariableContainer {
        id: input.id,
        data,
        flag: input.flag,
        extra,
    };
    let encoded = vc.to_ssz();
    let decoded = VariableContainer::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, vc, "VariableContainer roundtrip");

    // -- Structured roundtrip: MixedContainer --
    let mc = MixedContainer {
        fixed_field: input.fixed_field,
        items,
        count: input.count,
        labels,
        active: input.active,
    };
    let encoded = mc.to_ssz();
    let decoded = MixedContainer::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, mc, "MixedContainer roundtrip");
});
