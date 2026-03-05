#![no_main]

//! Fuzz transparent wrapper types: roundtrip, no-panic decode, and
//! verify that transparent encoding equals inner type encoding.

extern crate libssz as ssz;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
#[ssz(transparent)]
struct Slot(u64);

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
#[ssz(transparent)]
struct Root([u8; 32]);

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
#[ssz(transparent)]
struct WrappedVec(Vec<u8>);

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    slot_val: u64,
    root_val: [u8; 32],
    wrapped_vec: Vec<u8>,
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap WrappedVec for performance
    let wrapped_vec: Vec<u8> = input.wrapped_vec.into_iter().take(1024).collect();

    // Roundtrip: Slot
    let slot = Slot(input.slot_val);
    let encoded = slot.to_ssz();
    let decoded = Slot::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(slot, decoded, "Slot roundtrip mismatch");

    // Roundtrip: Root
    let root = Root(input.root_val);
    let encoded = root.to_ssz();
    let decoded = Root::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(root, decoded, "Root roundtrip mismatch");

    // Roundtrip: WrappedVec
    let wv = WrappedVec(wrapped_vec.clone());
    let encoded = wv.to_ssz();
    let decoded = WrappedVec::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(wv, decoded, "WrappedVec roundtrip mismatch");

    // No-panic decode from raw bytes
    let _ = Slot::from_ssz_bytes(&input.raw);
    let _ = Root::from_ssz_bytes(&input.raw);
    let _ = WrappedVec::from_ssz_bytes(&input.raw);

    // Transparent encoding equals inner type encoding
    assert_eq!(
        Slot(input.slot_val).to_ssz(),
        input.slot_val.to_ssz(),
        "Slot transparent encoding mismatch"
    );
    assert_eq!(
        Root(input.root_val).to_ssz(),
        input.root_val.to_ssz(),
        "Root transparent encoding mismatch"
    );
    assert_eq!(
        WrappedVec(wrapped_vec.clone()).to_ssz(),
        wrapped_vec.to_ssz(),
        "WrappedVec transparent encoding mismatch"
    );
});
