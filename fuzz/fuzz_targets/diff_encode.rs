#![no_main]

//! Differential encoding fuzzer: encode the same data with libssz and lighthouse_ssz,
//! then assert byte-identical output.

extern crate libssz as ssz;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    val_bool: bool,
    val_u8: u8,
    val_u16: u16,
    val_u32: u32,
    val_u64: u64,
    val_u128: u128,
    val_bytes32: [u8; 32],
    val_bytes4: [u8; 4],
    val_bytes20: [u8; 20],
    val_bytes48: [u8; 48],
    val_bytes96: [u8; 96],
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
    vec_u64: Vec<u64>,
}

/// Encode with our library.
fn ours<T: libssz::SszEncode>(val: &T) -> Vec<u8> {
    val.to_ssz()
}

/// Encode with Lighthouse's library.
fn lighthouse<T: lighthouse_ssz::Encode>(val: &T) -> Vec<u8> {
    val.as_ssz_bytes()
}

fuzz_target!(|input: FuzzInput| {
    // -- Primitives --
    assert_eq!(ours(&input.val_bool), lighthouse(&input.val_bool), "bool");
    assert_eq!(ours(&input.val_u8), lighthouse(&input.val_u8), "u8");
    assert_eq!(ours(&input.val_u16), lighthouse(&input.val_u16), "u16");
    assert_eq!(ours(&input.val_u32), lighthouse(&input.val_u32), "u32");
    assert_eq!(ours(&input.val_u64), lighthouse(&input.val_u64), "u64");
    assert_eq!(ours(&input.val_u128), lighthouse(&input.val_u128), "u128");
    assert_eq!(ours(&input.val_bytes32), lighthouse(&input.val_bytes32), "[u8;32]");
    assert_eq!(ours(&input.val_bytes4), lighthouse(&input.val_bytes4), "[u8;4]");
    assert_eq!(ours(&input.val_bytes20), lighthouse(&input.val_bytes20), "[u8;20]");
    assert_eq!(ours(&input.val_bytes48), lighthouse(&input.val_bytes48), "[u8;48]");
    assert_eq!(ours(&input.val_bytes96), lighthouse(&input.val_bytes96), "[u8;96]");

    // -- Container (BeaconBlockHeader — all fixed, encoding = concatenated fields) --
    let our_header = {
        let mut buf = Vec::new();
        <u64 as libssz::SszEncode>::ssz_append(&input.slot, &mut buf);
        <u64 as libssz::SszEncode>::ssz_append(&input.proposer_index, &mut buf);
        <[u8; 32] as libssz::SszEncode>::ssz_append(&input.parent_root, &mut buf);
        <[u8; 32] as libssz::SszEncode>::ssz_append(&input.state_root, &mut buf);
        <[u8; 32] as libssz::SszEncode>::ssz_append(&input.body_root, &mut buf);
        buf
    };
    let lh_header = {
        let mut buf = Vec::new();
        <u64 as lighthouse_ssz::Encode>::ssz_append(&input.slot, &mut buf);
        <u64 as lighthouse_ssz::Encode>::ssz_append(&input.proposer_index, &mut buf);
        <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.parent_root, &mut buf);
        <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.state_root, &mut buf);
        <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.body_root, &mut buf);
        buf
    };
    assert_eq!(our_header, lh_header, "BeaconBlockHeader");

    // -- Vec<u64> (cap for perf) --
    let vec: Vec<u64> = if input.vec_u64.len() > 1024 {
        input.vec_u64[..1024].to_vec()
    } else {
        input.vec_u64.clone()
    };
    assert_eq!(ours(&vec), lighthouse(&vec), "Vec<u64>");
});
