#![no_main]

//! Differential hash_tree_root fuzzer: compute hash_tree_root with libssz,
//! tree_hash (Lighthouse), and ssz_rs, then assert identical 32-byte roots.
//! Note: tree_hash and ssz_rs don't implement HTR for u128, so we skip that.

extern crate libssz as ssz;
extern crate libssz_merkle as ssz_merkle;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    val_bool: bool,
    val_u8: u8,
    val_u16: u16,
    val_u32: u32,
    val_u64: u64,
    val_bytes32: [u8; 32],
}

/// Hash with our library.
fn ours<T: libssz_merkle::HashTreeRoot>(val: &T) -> [u8; 32] {
    val.hash_tree_root()
}

/// Hash with Lighthouse's tree_hash.
fn lighthouse<T: tree_hash::TreeHash>(val: &T) -> [u8; 32] {
    val.tree_hash_root().0
}

/// Hash with ssz_rs (requires &mut self, so we clone).
fn ssz_rs_htr<T: ssz_rs::Merkleized + Clone>(val: &T) -> [u8; 32] {
    let node = val.clone().hash_tree_root().unwrap();
    let bytes: &[u8] = node.as_ref();
    bytes.try_into().unwrap()
}

fuzz_target!(|input: FuzzInput| {
    // ours vs lighthouse
    assert_eq!(ours(&input.val_bool), lighthouse(&input.val_bool), "bool");
    assert_eq!(ours(&input.val_u8), lighthouse(&input.val_u8), "u8");
    assert_eq!(ours(&input.val_u16), lighthouse(&input.val_u16), "u16");
    assert_eq!(ours(&input.val_u32), lighthouse(&input.val_u32), "u32");
    assert_eq!(ours(&input.val_u64), lighthouse(&input.val_u64), "u64");
    assert_eq!(ours(&input.val_bytes32), lighthouse(&input.val_bytes32), "[u8;32]");

    // ours vs ssz_rs
    assert_eq!(ours(&input.val_bool), ssz_rs_htr(&input.val_bool), "bool ssz_rs");
    assert_eq!(ours(&input.val_u8), ssz_rs_htr(&input.val_u8), "u8 ssz_rs");
    assert_eq!(ours(&input.val_u16), ssz_rs_htr(&input.val_u16), "u16 ssz_rs");
    assert_eq!(ours(&input.val_u32), ssz_rs_htr(&input.val_u32), "u32 ssz_rs");
    assert_eq!(ours(&input.val_u64), ssz_rs_htr(&input.val_u64), "u64 ssz_rs");
    assert_eq!(ours(&input.val_bytes32), ssz_rs_htr(&input.val_bytes32), "[u8;32] ssz_rs");
});
