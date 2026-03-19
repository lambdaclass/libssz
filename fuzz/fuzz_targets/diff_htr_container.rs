#![no_main]

//! Differential hash_tree_root fuzzer for containers and collections.
//! tree_hash doesn't implement TreeHash for Vec, so collection tests are no-panic only
//! for lighthouse. ssz_rs supports HTR for List, so we can differential-test collections
//! using SszList (which carries the limit) instead of Vec.
//! Also tests no-panic HTR for a BeaconBlockHeader container with our derive.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};

#[derive(Debug, SszEncode, SszDecode, HashTreeRoot)]
struct OurHeader {
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
}

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
    vec_u64: Vec<u64>,
    vec_bytes32: Vec<[u8; 32]>,
    val_u64: u64,
    val_bytes32: [u8; 32],
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
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
    // Differential: u64 HTR must match between all three libraries
    assert_eq!(
        ours(&input.val_u64),
        lighthouse(&input.val_u64),
        "u64 HTR mismatch (lighthouse)"
    );
    assert_eq!(
        ours(&input.val_u64),
        ssz_rs_htr(&input.val_u64),
        "u64 HTR mismatch (ssz_rs)"
    );

    // Differential: [u8;32] HTR must match between all three libraries
    assert_eq!(
        ours(&input.val_bytes32),
        lighthouse(&input.val_bytes32),
        "[u8;32] HTR mismatch (lighthouse)"
    );
    assert_eq!(
        ours(&input.val_bytes32),
        ssz_rs_htr(&input.val_bytes32),
        "[u8;32] HTR mismatch (ssz_rs)"
    );

    // List<u64> — differential with ssz_rs using SszList (both carry limit=256)
    let vec_u64: Vec<u64> = input.vec_u64.into_iter().take(256).collect();
    let our_list: libssz_types::SszList<u64, 256> = vec_u64.clone().try_into().unwrap();
    let our_htr = ours(&our_list);
    let mut ssz_rs_list: ssz_rs::List<u64, 256> = vec_u64.clone().try_into().unwrap();
    let ssz_rs_node = ssz_rs::Merkleized::hash_tree_root(&mut ssz_rs_list).unwrap();
    let ssz_rs_bytes: [u8; 32] = ssz_rs_node.as_ref().try_into().unwrap();
    assert_eq!(
        our_htr, ssz_rs_bytes,
        "List<u64, 256> HTR mismatch (ssz_rs)"
    );

    // No-panic HTR for Vec<u64> (no limit — can't differential-test against ssz_rs)
    let _ = ours(&vec_u64);

    // No-panic HTR for Vec<[u8;32]> collection
    let vec_bytes32: Vec<[u8; 32]> = input.vec_bytes32.into_iter().take(256).collect();
    let _ = ours(&vec_bytes32);

    // No-panic HTR for BeaconBlockHeader container
    let header = OurHeader {
        slot: input.slot,
        proposer_index: input.proposer_index,
        parent_root: input.parent_root,
        state_root: input.state_root,
        body_root: input.body_root,
    };
    let _ = ours(&header);

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
