#![no_main]

//! Differential hash_tree_root fuzzer: compute hash_tree_root with libssz,
//! tree_hash (Lighthouse), and ssz_rs, then assert identical 32-byte roots.
//! Note: tree_hash and ssz_rs don't implement HTR for u128, so we skip that.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};

#[derive(Debug, SszEncode, SszDecode, HashTreeRoot)]
struct OurFork {
    previous_version: [u8; 4],
    current_version: [u8; 4],
    epoch: u64,
}

#[derive(Debug, SszEncode, SszDecode, HashTreeRoot)]
struct OurCheckpoint {
    epoch: u64,
    root: [u8; 32],
}

#[derive(Debug, SszEncode, SszDecode, HashTreeRoot)]
struct OurEth1Data {
    deposit_root: [u8; 32],
    deposit_count: u64,
    block_hash: [u8; 32],
}

#[derive(Debug, SszEncode, SszDecode, HashTreeRoot)]
struct OurCheckpointInner {
    epoch: u64,
    root: [u8; 32],
}

#[derive(Debug, SszEncode, SszDecode, HashTreeRoot)]
struct OurAttestationData {
    slot: u64,
    index: u64,
    beacon_block_root: [u8; 32],
    source: OurCheckpointInner,
    target: OurCheckpointInner,
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    val_bool: bool,
    val_u8: u8,
    val_u16: u16,
    val_u32: u32,
    val_u64: u64,
    val_bytes32: [u8; 32],
    // Fork
    prev_version: [u8; 4],
    cur_version: [u8; 4],
    fork_epoch: u64,
    // Checkpoint
    checkpoint_epoch: u64,
    checkpoint_root: [u8; 32],
    // Eth1Data
    deposit_root: [u8; 32],
    deposit_count: u64,
    eth1_block_hash: [u8; 32],
    // AttestationData
    att_slot: u64,
    att_index: u64,
    att_beacon_block_root: [u8; 32],
    source_epoch: u64,
    source_root: [u8; 32],
    target_epoch: u64,
    target_root: [u8; 32],
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

    // No-panic HTR for Fork
    let fork = OurFork {
        previous_version: input.prev_version,
        current_version: input.cur_version,
        epoch: input.fork_epoch,
    };
    let _ = ours(&fork);

    // No-panic HTR for Checkpoint
    let checkpoint = OurCheckpoint {
        epoch: input.checkpoint_epoch,
        root: input.checkpoint_root,
    };
    let _ = ours(&checkpoint);

    // No-panic HTR for Eth1Data
    let eth1data = OurEth1Data {
        deposit_root: input.deposit_root,
        deposit_count: input.deposit_count,
        block_hash: input.eth1_block_hash,
    };
    let _ = ours(&eth1data);

    // No-panic HTR for AttestationData
    let att_data = OurAttestationData {
        slot: input.att_slot,
        index: input.att_index,
        beacon_block_root: input.att_beacon_block_root,
        source: OurCheckpointInner {
            epoch: input.source_epoch,
            root: input.source_root,
        },
        target: OurCheckpointInner {
            epoch: input.target_epoch,
            root: input.target_root,
        },
    };
    let _ = ours(&att_data);
});
