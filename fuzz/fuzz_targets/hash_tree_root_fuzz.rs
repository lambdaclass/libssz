#![no_main]

//! Fuzz hash_tree_root for no-panic on adversarial inputs.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::SszDecode;
use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_merkle::HashTreeRoot;
use libssz_types::{SszBitlist, SszBitvector, SszList, SszVector};

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
struct BeaconBlockHeader {
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    val_u64: u64,
    val_bool: bool,
    val_bytes32: [u8; 32],
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // Primitives
    let _ = input.val_u64.hash_tree_root();
    let _ = input.val_bool.hash_tree_root();
    let _ = input.val_bytes32.hash_tree_root();

    // Container
    let header = BeaconBlockHeader {
        slot: input.slot,
        proposer_index: input.proposer_index,
        parent_root: input.parent_root,
        state_root: input.state_root,
        body_root: input.body_root,
    };
    let _ = header.hash_tree_root();

    // Decode-then-hash from raw bytes (cap sizes for performance)
    if let Ok(val) = Vec::<u64>::from_ssz_bytes(&input.raw) {
        if val.len() <= 4096 {
            let _ = val.hash_tree_root();
        }
    }
    if let Ok(val) = SszList::<u64, 1_048_576>::from_ssz_bytes(&input.raw) {
        if val.len() <= 4096 {
            let _ = val.hash_tree_root();
        }
    }
    if let Ok(val) = SszVector::<[u8; 32], 64>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitlist::<2048>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitvector::<512>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }

    // -- Additional bitfield sizes --
    if let Ok(val) = SszBitlist::<8>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitlist::<64>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitvector::<8>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitvector::<64>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }

    // -- Non-byte-aligned bitvector sizes for excess bit validation --
    if let Ok(val) = SszBitvector::<3>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitvector::<7>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitvector::<9>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }
    if let Ok(val) = SszBitvector::<15>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }

    // -- Boundary collections --
    if let Ok(val) = SszVector::<u64, 1>::from_ssz_bytes(&input.raw) {
        let _ = val.hash_tree_root();
    }

    // -- Empty collection HTR --
    let _ = Vec::<u64>::new().hash_tree_root();
    if let Ok(bl) = SszBitlist::<2048>::from_ssz_bytes(&[1u8]) {
        let _ = bl.hash_tree_root();
    }
});
