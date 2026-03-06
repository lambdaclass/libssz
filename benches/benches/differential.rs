use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ssz::{SszDecode, SszEncode};
use ssz_bench::fixtures::{
    make_attestation_data, make_beacon_state, make_checkpoint, make_eth1_data, make_fork,
    make_header, make_vec_u64, pre_encode, AttestationData, BeaconBlockHeader, BeaconState,
    Checkpoint, Eth1Data, Fork,
};
use ssz_merkle::HashTreeRoot;

// ===========================================================================
// Lighthouse-native consensus types
// ===========================================================================
//
// Lighthouse (github.com/sigp/lighthouse) does not publish consensus types
// (Fork, Checkpoint, Validator, BeaconState, etc.) as standalone crates.
// They live in lighthouse/consensus/types/ which depends on the full
// lighthouse workspace. To enable three-way differential benchmarks we
// recreate them here using the same derive macros and collection types
// that Lighthouse uses:
//   - ethereum_ssz::{Encode, Decode}        (re-exported as lighthouse_ssz)
//   - ethereum_ssz_derive::{Encode, Decode}  (re-exported as lighthouse_ssz_derive)
//   - ssz_types::{VariableList, FixedVector, BitList, BitVector}
//   - tree_hash::TreeHash + tree_hash_derive::TreeHash
//   - typenum for type-level integers
//
// Source: https://github.com/sigp/lighthouse/blob/stable/consensus/types/src/
// ===========================================================================

mod lighthouse_types {
    // The lighthouse_ssz_derive macros generate code that references `ssz::*`
    // (the crate name Lighthouse uses internally). We re-export lighthouse_ssz
    // as `ssz` here so the generated code resolves correctly.
    use lighthouse_ssz as ssz;
    use lighthouse_ssz_derive::{Decode, Encode};
    use lighthouse_ssz_types::{BitList, BitVector, FixedVector, VariableList};
    use tree_hash_derive::TreeHash;
    use typenum::{U1099511627776, U16777216, U2048, U4, U4096, U65536, U8192};

    #[derive(Clone, Debug, Default, PartialEq, Encode, Decode, TreeHash)]
    pub struct Fork {
        pub previous_version: [u8; 4],
        pub current_version: [u8; 4],
        pub epoch: u64,
    }

    #[derive(Clone, Debug, Default, PartialEq, Encode, Decode, TreeHash)]
    pub struct Checkpoint {
        pub epoch: u64,
        pub root: [u8; 32],
    }

    #[derive(Clone, Debug, Default, PartialEq, Encode, Decode, TreeHash)]
    pub struct Eth1Data {
        pub deposit_root: [u8; 32],
        pub deposit_count: u64,
        pub block_hash: [u8; 32],
    }

    #[derive(Clone, Debug, Default, PartialEq, Encode, Decode, TreeHash)]
    pub struct AttestationData {
        pub slot: u64,
        pub index: u64,
        pub beacon_block_root: [u8; 32],
        pub source: Checkpoint,
        pub target: Checkpoint,
    }

    #[derive(Clone, Debug, Default, PartialEq, Encode, Decode, TreeHash)]
    pub struct BeaconBlockHeader {
        pub slot: u64,
        pub proposer_index: u64,
        pub parent_root: [u8; 32],
        pub state_root: [u8; 32],
        pub body_root: [u8; 32],
    }

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    pub struct Validator {
        pub pubkey: [u8; 48],
        pub withdrawal_credentials: [u8; 32],
        pub effective_balance: u64,
        pub slashed: bool,
        pub activation_eligibility_epoch: u64,
        pub activation_epoch: u64,
        pub exit_epoch: u64,
        pub withdrawable_epoch: u64,
    }

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    pub struct PendingAttestation {
        pub aggregation_bits: BitList<U2048>,
        pub data: AttestationData,
        pub inclusion_delay: u64,
        pub proposer_index: u64,
    }

    /// Phase 0 BeaconState — 21 fields.
    /// Source: lighthouse/consensus/types/src/beacon_state.rs
    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    pub struct BeaconState {
        pub genesis_time: u64,
        pub genesis_validators_root: [u8; 32],
        pub slot: u64,
        pub fork: Fork,
        pub latest_block_header: BeaconBlockHeader,
        pub block_roots: FixedVector<[u8; 32], U8192>,
        pub state_roots: FixedVector<[u8; 32], U8192>,
        pub historical_roots: VariableList<[u8; 32], U16777216>,
        pub eth1_data: Eth1Data,
        pub eth1_data_votes: VariableList<Eth1Data, U2048>,
        pub eth1_deposit_index: u64,
        pub validators: VariableList<Validator, U1099511627776>,
        pub balances: VariableList<u64, U1099511627776>,
        pub randao_mixes: FixedVector<[u8; 32], U65536>,
        pub slashings: FixedVector<u64, U8192>,
        pub previous_epoch_attestations: VariableList<PendingAttestation, U4096>,
        pub current_epoch_attestations: VariableList<PendingAttestation, U4096>,
        pub justification_bits: BitVector<U4>,
        pub previous_justified_checkpoint: Checkpoint,
        pub current_justified_checkpoint: Checkpoint,
        pub finalized_checkpoint: Checkpoint,
    }
}

// ===========================================================================
// ssz_rs-native consensus types
// ===========================================================================
//
// ssz_rs (github.com/ralexstokes/ssz-rs) does not ship consensus types.
// We recreate them here using ssz_rs::SimpleSerialize derive and its
// collection types: List, Vector, Bitlist, Bitvector (all const-generic).
//
// Note: ssz_rs only implements SimpleSerialize for [T; N] up to N=32.
// For BLS pubkeys ([u8; 48]) and signatures ([u8; 96]) we use
// ssz_rs::Vector<u8, 48> / Vector<u8, 96> instead.
//
// Source: https://github.com/ralexstokes/ssz-rs
// ===========================================================================

mod ssz_rs_types {
    use ssz_rs::prelude::*;

    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct Fork {
        pub previous_version: [u8; 4],
        pub current_version: [u8; 4],
        pub epoch: u64,
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct Checkpoint {
        pub epoch: u64,
        pub root: [u8; 32],
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct Eth1Data {
        pub deposit_root: [u8; 32],
        pub deposit_count: u64,
        pub block_hash: [u8; 32],
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct AttestationData {
        pub slot: u64,
        pub index: u64,
        pub beacon_block_root: [u8; 32],
        pub source: Checkpoint,
        pub target: Checkpoint,
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct BeaconBlockHeader {
        pub slot: u64,
        pub proposer_index: u64,
        pub parent_root: [u8; 32],
        pub state_root: [u8; 32],
        pub body_root: [u8; 32],
    }

    /// Uses Vector<u8, 48> for pubkey since ssz_rs doesn't support [u8; 48].
    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct Validator {
        pub pubkey: Vector<u8, 48>,
        pub withdrawal_credentials: [u8; 32],
        pub effective_balance: u64,
        pub slashed: bool,
        pub activation_eligibility_epoch: u64,
        pub activation_epoch: u64,
        pub exit_epoch: u64,
        pub withdrawable_epoch: u64,
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct PendingAttestation {
        pub aggregation_bits: Bitlist<2048>,
        pub data: AttestationData,
        pub inclusion_delay: u64,
        pub proposer_index: u64,
    }

    /// Phase 0 BeaconState — 21 fields.
    #[derive(Clone, Debug, Default, PartialEq, Eq, SimpleSerialize)]
    pub struct BeaconState {
        pub genesis_time: u64,
        pub genesis_validators_root: [u8; 32],
        pub slot: u64,
        pub fork: Fork,
        pub latest_block_header: BeaconBlockHeader,
        pub block_roots: Vector<[u8; 32], 8192>,
        pub state_roots: Vector<[u8; 32], 8192>,
        pub historical_roots: List<[u8; 32], 16_777_216>,
        pub eth1_data: Eth1Data,
        pub eth1_data_votes: List<Eth1Data, 2048>,
        pub eth1_deposit_index: u64,
        pub validators: List<Validator, 1_099_511_627_776>,
        pub balances: List<u64, 1_099_511_627_776>,
        pub randao_mixes: Vector<[u8; 32], 65536>,
        pub slashings: Vector<u64, 8192>,
        pub previous_epoch_attestations: List<PendingAttestation, 4096>,
        pub current_epoch_attestations: List<PendingAttestation, 4096>,
        pub justification_bits: Bitvector<4>,
        pub previous_justified_checkpoint: Checkpoint,
        pub current_justified_checkpoint: Checkpoint,
        pub finalized_checkpoint: Checkpoint,
    }
}

// ===========================================================================
// Conversion helpers: libssz fixtures → Lighthouse/ssz_rs native types
// ===========================================================================

fn to_lighthouse_beacon_state(
    state: &ssz_bench::fixtures::BeaconState,
) -> lighthouse_types::BeaconState {
    use lighthouse_ssz_types::{BitList, BitVector, FixedVector, VariableList};

    let validators: Vec<lighthouse_types::Validator> = state
        .validators
        .iter()
        .map(|v| lighthouse_types::Validator {
            pubkey: v.pubkey,
            withdrawal_credentials: v.withdrawal_credentials,
            effective_balance: v.effective_balance,
            slashed: v.slashed,
            activation_eligibility_epoch: v.activation_eligibility_epoch,
            activation_epoch: v.activation_epoch,
            exit_epoch: v.exit_epoch,
            withdrawable_epoch: v.withdrawable_epoch,
        })
        .collect();

    let eth1_data_votes: Vec<lighthouse_types::Eth1Data> = state
        .eth1_data_votes
        .iter()
        .map(|e| lighthouse_types::Eth1Data {
            deposit_root: e.deposit_root,
            deposit_count: e.deposit_count,
            block_hash: e.block_hash,
        })
        .collect();

    let prev_atts: Vec<lighthouse_types::PendingAttestation> = state
        .previous_epoch_attestations
        .iter()
        .map(|a| {
            let mut bits = BitList::with_capacity(a.aggregation_bits.len()).unwrap();
            for i in 0..a.aggregation_bits.len() {
                bits.set(i, a.aggregation_bits.get(i).unwrap()).unwrap();
            }
            lighthouse_types::PendingAttestation {
                aggregation_bits: bits,
                data: lighthouse_types::AttestationData {
                    slot: a.data.slot,
                    index: a.data.index,
                    beacon_block_root: a.data.beacon_block_root,
                    source: lighthouse_types::Checkpoint {
                        epoch: a.data.source.epoch,
                        root: a.data.source.root,
                    },
                    target: lighthouse_types::Checkpoint {
                        epoch: a.data.target.epoch,
                        root: a.data.target.root,
                    },
                },
                inclusion_delay: a.inclusion_delay,
                proposer_index: a.proposer_index,
            }
        })
        .collect();

    let cur_atts: Vec<lighthouse_types::PendingAttestation> = state
        .current_epoch_attestations
        .iter()
        .map(|a| {
            let mut bits = BitList::with_capacity(a.aggregation_bits.len()).unwrap();
            for i in 0..a.aggregation_bits.len() {
                bits.set(i, a.aggregation_bits.get(i).unwrap()).unwrap();
            }
            lighthouse_types::PendingAttestation {
                aggregation_bits: bits,
                data: lighthouse_types::AttestationData {
                    slot: a.data.slot,
                    index: a.data.index,
                    beacon_block_root: a.data.beacon_block_root,
                    source: lighthouse_types::Checkpoint {
                        epoch: a.data.source.epoch,
                        root: a.data.source.root,
                    },
                    target: lighthouse_types::Checkpoint {
                        epoch: a.data.target.epoch,
                        root: a.data.target.root,
                    },
                },
                inclusion_delay: a.inclusion_delay,
                proposer_index: a.proposer_index,
            }
        })
        .collect();

    let mut justification_bits = BitVector::new();
    for i in 0..4 {
        justification_bits
            .set(i, state.justification_bits.get(i).unwrap())
            .unwrap();
    }

    lighthouse_types::BeaconState {
        genesis_time: state.genesis_time,
        genesis_validators_root: state.genesis_validators_root,
        slot: state.slot,
        fork: lighthouse_types::Fork {
            previous_version: state.fork.previous_version,
            current_version: state.fork.current_version,
            epoch: state.fork.epoch,
        },
        latest_block_header: lighthouse_types::BeaconBlockHeader {
            slot: state.latest_block_header.slot,
            proposer_index: state.latest_block_header.proposer_index,
            parent_root: state.latest_block_header.parent_root,
            state_root: state.latest_block_header.state_root,
            body_root: state.latest_block_header.body_root,
        },
        block_roots: FixedVector::new(state.block_roots.iter().copied().collect()).unwrap(),
        state_roots: FixedVector::new(state.state_roots.iter().copied().collect()).unwrap(),
        historical_roots: VariableList::new(state.historical_roots.iter().copied().collect())
            .unwrap(),
        eth1_data: lighthouse_types::Eth1Data {
            deposit_root: state.eth1_data.deposit_root,
            deposit_count: state.eth1_data.deposit_count,
            block_hash: state.eth1_data.block_hash,
        },
        eth1_data_votes: VariableList::new(eth1_data_votes).unwrap(),
        eth1_deposit_index: state.eth1_deposit_index,
        validators: VariableList::new(validators).unwrap(),
        balances: VariableList::new(state.balances.iter().copied().collect()).unwrap(),
        randao_mixes: FixedVector::new(state.randao_mixes.iter().copied().collect()).unwrap(),
        slashings: FixedVector::new(state.slashings.iter().copied().collect()).unwrap(),
        previous_epoch_attestations: VariableList::new(prev_atts).unwrap(),
        current_epoch_attestations: VariableList::new(cur_atts).unwrap(),
        justification_bits,
        previous_justified_checkpoint: lighthouse_types::Checkpoint {
            epoch: state.previous_justified_checkpoint.epoch,
            root: state.previous_justified_checkpoint.root,
        },
        current_justified_checkpoint: lighthouse_types::Checkpoint {
            epoch: state.current_justified_checkpoint.epoch,
            root: state.current_justified_checkpoint.root,
        },
        finalized_checkpoint: lighthouse_types::Checkpoint {
            epoch: state.finalized_checkpoint.epoch,
            root: state.finalized_checkpoint.root,
        },
    }
}

fn to_ssz_rs_beacon_state(state: &ssz_bench::fixtures::BeaconState) -> ssz_rs_types::BeaconState {
    use ssz_rs::prelude::*;

    let validators: Vec<ssz_rs_types::Validator> = state
        .validators
        .iter()
        .map(|v| ssz_rs_types::Validator {
            pubkey: Vector::try_from(v.pubkey.to_vec()).unwrap(),
            withdrawal_credentials: v.withdrawal_credentials,
            effective_balance: v.effective_balance,
            slashed: v.slashed,
            activation_eligibility_epoch: v.activation_eligibility_epoch,
            activation_epoch: v.activation_epoch,
            exit_epoch: v.exit_epoch,
            withdrawable_epoch: v.withdrawable_epoch,
        })
        .collect();

    let eth1_data_votes: Vec<ssz_rs_types::Eth1Data> = state
        .eth1_data_votes
        .iter()
        .map(|e| ssz_rs_types::Eth1Data {
            deposit_root: e.deposit_root,
            deposit_count: e.deposit_count,
            block_hash: e.block_hash,
        })
        .collect();

    let prev_atts: Vec<ssz_rs_types::PendingAttestation> = state
        .previous_epoch_attestations
        .iter()
        .map(|a| {
            let bits_vec: Vec<bool> = (0..a.aggregation_bits.len())
                .map(|i| a.aggregation_bits.get(i).unwrap())
                .collect();
            ssz_rs_types::PendingAttestation {
                aggregation_bits: Bitlist::try_from(bits_vec.as_slice()).unwrap(),
                data: ssz_rs_types::AttestationData {
                    slot: a.data.slot,
                    index: a.data.index,
                    beacon_block_root: a.data.beacon_block_root,
                    source: ssz_rs_types::Checkpoint {
                        epoch: a.data.source.epoch,
                        root: a.data.source.root,
                    },
                    target: ssz_rs_types::Checkpoint {
                        epoch: a.data.target.epoch,
                        root: a.data.target.root,
                    },
                },
                inclusion_delay: a.inclusion_delay,
                proposer_index: a.proposer_index,
            }
        })
        .collect();

    let cur_atts: Vec<ssz_rs_types::PendingAttestation> = state
        .current_epoch_attestations
        .iter()
        .map(|a| {
            let bits_vec: Vec<bool> = (0..a.aggregation_bits.len())
                .map(|i| a.aggregation_bits.get(i).unwrap())
                .collect();
            ssz_rs_types::PendingAttestation {
                aggregation_bits: Bitlist::try_from(bits_vec.as_slice()).unwrap(),
                data: ssz_rs_types::AttestationData {
                    slot: a.data.slot,
                    index: a.data.index,
                    beacon_block_root: a.data.beacon_block_root,
                    source: ssz_rs_types::Checkpoint {
                        epoch: a.data.source.epoch,
                        root: a.data.source.root,
                    },
                    target: ssz_rs_types::Checkpoint {
                        epoch: a.data.target.epoch,
                        root: a.data.target.root,
                    },
                },
                inclusion_delay: a.inclusion_delay,
                proposer_index: a.proposer_index,
            }
        })
        .collect();

    let justification_bits_vec: Vec<bool> = (0..4)
        .map(|i| state.justification_bits.get(i).unwrap())
        .collect();

    ssz_rs_types::BeaconState {
        genesis_time: state.genesis_time,
        genesis_validators_root: state.genesis_validators_root,
        slot: state.slot,
        fork: ssz_rs_types::Fork {
            previous_version: state.fork.previous_version,
            current_version: state.fork.current_version,
            epoch: state.fork.epoch,
        },
        latest_block_header: ssz_rs_types::BeaconBlockHeader {
            slot: state.latest_block_header.slot,
            proposer_index: state.latest_block_header.proposer_index,
            parent_root: state.latest_block_header.parent_root,
            state_root: state.latest_block_header.state_root,
            body_root: state.latest_block_header.body_root,
        },
        block_roots: Vector::try_from(state.block_roots.iter().copied().collect::<Vec<_>>())
            .unwrap(),
        state_roots: Vector::try_from(state.state_roots.iter().copied().collect::<Vec<_>>())
            .unwrap(),
        historical_roots: List::try_from(
            state.historical_roots.iter().copied().collect::<Vec<_>>(),
        )
        .unwrap(),
        eth1_data: ssz_rs_types::Eth1Data {
            deposit_root: state.eth1_data.deposit_root,
            deposit_count: state.eth1_data.deposit_count,
            block_hash: state.eth1_data.block_hash,
        },
        eth1_data_votes: List::try_from(eth1_data_votes).unwrap(),
        eth1_deposit_index: state.eth1_deposit_index,
        validators: List::try_from(validators).unwrap(),
        balances: List::try_from(state.balances.iter().copied().collect::<Vec<_>>()).unwrap(),
        randao_mixes: Vector::try_from(state.randao_mixes.iter().copied().collect::<Vec<_>>())
            .unwrap(),
        slashings: Vector::try_from(state.slashings.iter().copied().collect::<Vec<_>>()).unwrap(),
        previous_epoch_attestations: List::try_from(prev_atts).unwrap(),
        current_epoch_attestations: List::try_from(cur_atts).unwrap(),
        justification_bits: Bitvector::try_from(justification_bits_vec.as_slice()).unwrap(),
        previous_justified_checkpoint: ssz_rs_types::Checkpoint {
            epoch: state.previous_justified_checkpoint.epoch,
            root: state.previous_justified_checkpoint.root,
        },
        current_justified_checkpoint: ssz_rs_types::Checkpoint {
            epoch: state.current_justified_checkpoint.epoch,
            root: state.current_justified_checkpoint.root,
        },
        finalized_checkpoint: ssz_rs_types::Checkpoint {
            epoch: state.finalized_checkpoint.epoch,
            root: state.finalized_checkpoint.root,
        },
    }
}

// ---------------------------------------------------------------------------
// Lighthouse helpers for BeaconBlockHeader (our type, not lighthouse-derived)
// ---------------------------------------------------------------------------

fn lighthouse_encode_header(h: &BeaconBlockHeader) -> Vec<u8> {
    let mut buf = Vec::new();
    <u64 as lighthouse_ssz::Encode>::ssz_append(&h.slot, &mut buf);
    <u64 as lighthouse_ssz::Encode>::ssz_append(&h.proposer_index, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&h.parent_root, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&h.state_root, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&h.body_root, &mut buf);
    buf
}

fn lighthouse_decode_header(bytes: &[u8]) -> (u64, u64, [u8; 32], [u8; 32], [u8; 32]) {
    let slot = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..8]).unwrap();
    let proposer_index = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..16]).unwrap();
    let parent_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[16..48]).unwrap();
    let state_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[48..80]).unwrap();
    let body_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[80..112]).unwrap();
    (slot, proposer_index, parent_root, state_root, body_root)
}

// ---------------------------------------------------------------------------
// ssz_rs helpers for BeaconBlockHeader
// ---------------------------------------------------------------------------

fn ssz_rs_encode_header(h: &BeaconBlockHeader) -> Vec<u8> {
    let mut buf = Vec::new();
    ssz_rs::Serialize::serialize(&h.slot, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&h.proposer_index, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&h.parent_root, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&h.state_root, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&h.body_root, &mut buf).unwrap();
    buf
}

fn ssz_rs_decode_header(bytes: &[u8]) -> (u64, u64, [u8; 32], [u8; 32], [u8; 32]) {
    let slot = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[0..8]).unwrap();
    let proposer_index = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[8..16]).unwrap();
    let parent_root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[16..48]).unwrap();
    let state_root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[48..80]).unwrap();
    let body_root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[80..112]).unwrap();
    (slot, proposer_index, parent_root, state_root, body_root)
}

// ---------------------------------------------------------------------------
// Lighthouse helpers for consensus containers
// ---------------------------------------------------------------------------

fn lighthouse_encode_fork(f: &Fork) -> Vec<u8> {
    let mut buf = Vec::new();
    <[u8; 4] as lighthouse_ssz::Encode>::ssz_append(&f.previous_version, &mut buf);
    <[u8; 4] as lighthouse_ssz::Encode>::ssz_append(&f.current_version, &mut buf);
    <u64 as lighthouse_ssz::Encode>::ssz_append(&f.epoch, &mut buf);
    buf
}

fn lighthouse_decode_fork(bytes: &[u8]) -> ([u8; 4], [u8; 4], u64) {
    let previous_version =
        <[u8; 4] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..4]).unwrap();
    let current_version =
        <[u8; 4] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[4..8]).unwrap();
    let epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..16]).unwrap();
    (previous_version, current_version, epoch)
}

fn lighthouse_encode_checkpoint(cp: &Checkpoint) -> Vec<u8> {
    let mut buf = Vec::new();
    <u64 as lighthouse_ssz::Encode>::ssz_append(&cp.epoch, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&cp.root, &mut buf);
    buf
}

fn lighthouse_decode_checkpoint(bytes: &[u8]) -> (u64, [u8; 32]) {
    let epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..8]).unwrap();
    let root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..40]).unwrap();
    (epoch, root)
}

fn lighthouse_encode_eth1_data(e: &Eth1Data) -> Vec<u8> {
    let mut buf = Vec::new();
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&e.deposit_root, &mut buf);
    <u64 as lighthouse_ssz::Encode>::ssz_append(&e.deposit_count, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&e.block_hash, &mut buf);
    buf
}

fn lighthouse_decode_eth1_data(bytes: &[u8]) -> ([u8; 32], u64, [u8; 32]) {
    let deposit_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..32]).unwrap();
    let deposit_count = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[32..40]).unwrap();
    let block_hash = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[40..72]).unwrap();
    (deposit_root, deposit_count, block_hash)
}

fn lighthouse_encode_attestation_data(a: &AttestationData) -> Vec<u8> {
    let mut buf = Vec::new();
    <u64 as lighthouse_ssz::Encode>::ssz_append(&a.slot, &mut buf);
    <u64 as lighthouse_ssz::Encode>::ssz_append(&a.index, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&a.beacon_block_root, &mut buf);
    <u64 as lighthouse_ssz::Encode>::ssz_append(&a.source.epoch, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&a.source.root, &mut buf);
    <u64 as lighthouse_ssz::Encode>::ssz_append(&a.target.epoch, &mut buf);
    <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&a.target.root, &mut buf);
    buf
}

fn lighthouse_decode_attestation_data(
    bytes: &[u8],
) -> (u64, u64, [u8; 32], u64, [u8; 32], u64, [u8; 32]) {
    let slot = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..8]).unwrap();
    let index = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..16]).unwrap();
    let beacon_block_root =
        <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[16..48]).unwrap();
    let source_epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[48..56]).unwrap();
    let source_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[56..88]).unwrap();
    let target_epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[88..96]).unwrap();
    let target_root =
        <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[96..128]).unwrap();
    (
        slot,
        index,
        beacon_block_root,
        source_epoch,
        source_root,
        target_epoch,
        target_root,
    )
}

// ---------------------------------------------------------------------------
// ssz_rs helpers for consensus containers
// ---------------------------------------------------------------------------

fn ssz_rs_encode_fork(f: &Fork) -> Vec<u8> {
    let mut buf = Vec::new();
    ssz_rs::Serialize::serialize(&f.previous_version, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&f.current_version, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&f.epoch, &mut buf).unwrap();
    buf
}

fn ssz_rs_decode_fork(bytes: &[u8]) -> ([u8; 4], [u8; 4], u64) {
    let previous_version = <[u8; 4] as ssz_rs::Deserialize>::deserialize(&bytes[0..4]).unwrap();
    let current_version = <[u8; 4] as ssz_rs::Deserialize>::deserialize(&bytes[4..8]).unwrap();
    let epoch = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[8..16]).unwrap();
    (previous_version, current_version, epoch)
}

fn ssz_rs_encode_checkpoint(cp: &Checkpoint) -> Vec<u8> {
    let mut buf = Vec::new();
    ssz_rs::Serialize::serialize(&cp.epoch, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&cp.root, &mut buf).unwrap();
    buf
}

fn ssz_rs_decode_checkpoint(bytes: &[u8]) -> (u64, [u8; 32]) {
    let epoch = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[0..8]).unwrap();
    let root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[8..40]).unwrap();
    (epoch, root)
}

fn ssz_rs_encode_eth1_data(e: &Eth1Data) -> Vec<u8> {
    let mut buf = Vec::new();
    ssz_rs::Serialize::serialize(&e.deposit_root, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&e.deposit_count, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&e.block_hash, &mut buf).unwrap();
    buf
}

fn ssz_rs_decode_eth1_data(bytes: &[u8]) -> ([u8; 32], u64, [u8; 32]) {
    let deposit_root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[0..32]).unwrap();
    let deposit_count = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[32..40]).unwrap();
    let block_hash = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[40..72]).unwrap();
    (deposit_root, deposit_count, block_hash)
}

fn ssz_rs_encode_attestation_data(a: &AttestationData) -> Vec<u8> {
    let mut buf = Vec::new();
    ssz_rs::Serialize::serialize(&a.slot, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&a.index, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&a.beacon_block_root, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&a.source.epoch, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&a.source.root, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&a.target.epoch, &mut buf).unwrap();
    ssz_rs::Serialize::serialize(&a.target.root, &mut buf).unwrap();
    buf
}

fn ssz_rs_decode_attestation_data(
    bytes: &[u8],
) -> (u64, u64, [u8; 32], u64, [u8; 32], u64, [u8; 32]) {
    let slot = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[0..8]).unwrap();
    let index = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[8..16]).unwrap();
    let beacon_block_root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[16..48]).unwrap();
    let source_epoch = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[48..56]).unwrap();
    let source_root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[56..88]).unwrap();
    let target_epoch = <u64 as ssz_rs::Deserialize>::deserialize(&bytes[88..96]).unwrap();
    let target_root = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes[96..128]).unwrap();
    (
        slot,
        index,
        beacon_block_root,
        source_epoch,
        source_root,
        target_epoch,
        target_root,
    )
}

// ---------------------------------------------------------------------------
// Encode benchmarks
// ---------------------------------------------------------------------------

fn diff_encode_primitives(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/primitives");

    macro_rules! bench_encode {
        ($name:expr, $val:expr) => {
            let val = $val;
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| black_box(&val).to_ssz())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(&val)))
            });
            group.bench_function(concat!("ssz_rs/", $name), |b| {
                b.iter(|| {
                    let mut buf = Vec::new();
                    ssz_rs::Serialize::serialize(black_box(&val), &mut buf).unwrap();
                    buf
                })
            });
        };
    }

    macro_rules! bench_encode_no_ssz_rs {
        ($name:expr, $val:expr) => {
            let val = $val;
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| black_box(&val).to_ssz())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(&val)))
            });
        };
    }

    bench_encode!("bool", true);
    bench_encode!("u8", 0xABu8);
    bench_encode!("u16", 0xABCDu16);
    bench_encode!("u32", 0xDEAD_BEEFu32);
    bench_encode!("u64", 0x1234_5678_9ABC_DEF0u64);
    bench_encode_no_ssz_rs!("u128", u128::MAX);
    group.finish();
}

fn diff_encode_byte_arrays(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/byte_arrays");

    macro_rules! bench_encode_bytes {
        ($name:expr, $val:expr) => {
            let val = $val;
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| black_box(&val).to_ssz())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(&val)))
            });
            group.bench_function(concat!("ssz_rs/", $name), |b| {
                b.iter(|| {
                    let mut buf = Vec::new();
                    ssz_rs::Serialize::serialize(black_box(&val), &mut buf).unwrap();
                    buf
                })
            });
        };
    }

    // ssz_rs only supports arrays up to [T; 32], so bytes48 and bytes96 skip ssz_rs
    macro_rules! bench_encode_bytes_no_ssz_rs {
        ($name:expr, $val:expr) => {
            let val = $val;
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| black_box(&val).to_ssz())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(&val)))
            });
        };
    }

    bench_encode_bytes!("bytes32", [0xABu8; 32]);
    bench_encode_bytes_no_ssz_rs!("bytes48", [0xABu8; 48]);
    bench_encode_bytes_no_ssz_rs!("bytes96", [0xABu8; 96]);
    group.finish();
}

fn diff_encode_vec_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/vec_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        let ssz_rs_list: ssz_rs::List<u64, 1_000_000> =
            data.clone().try_into().expect("fits in List");
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::new("libssz", size), &data, |b, data| {
            b.iter(|| black_box(data).to_ssz());
        });
        group.bench_with_input(BenchmarkId::new("lighthouse", size), &data, |b, data| {
            b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(data)));
        });
        group.bench_with_input(BenchmarkId::new("ssz_rs", size), &ssz_rs_list, |b, list| {
            b.iter(|| {
                let mut buf = Vec::new();
                ssz_rs::Serialize::serialize(black_box(list), &mut buf).unwrap();
                buf
            });
        });
    }
    group.finish();
}

fn diff_encode_header(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/header");
    let header = make_header(42);
    group.bench_function("libssz", |b| b.iter(|| black_box(&header).to_ssz()));
    group.bench_function("lighthouse", |b| {
        b.iter(|| lighthouse_encode_header(black_box(&header)))
    });
    group.bench_function("ssz_rs", |b| {
        b.iter(|| ssz_rs_encode_header(black_box(&header)))
    });
    group.finish();
}

// ---------------------------------------------------------------------------
// Decode benchmarks
// ---------------------------------------------------------------------------

fn diff_decode_primitives(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/primitives");

    macro_rules! bench_decode {
        ($name:expr, $ty:ty, $val:expr) => {
            let bytes = pre_encode(&$val);
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| <$ty as SszDecode>::from_ssz_bytes(black_box(&bytes)).unwrap())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| {
                    <$ty as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(&bytes)).unwrap()
                })
            });
            group.bench_function(concat!("ssz_rs/", $name), |b| {
                b.iter(|| <$ty as ssz_rs::Deserialize>::deserialize(black_box(&bytes)).unwrap())
            });
        };
    }

    macro_rules! bench_decode_no_ssz_rs {
        ($name:expr, $ty:ty, $val:expr) => {
            let bytes = pre_encode(&$val);
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| <$ty as SszDecode>::from_ssz_bytes(black_box(&bytes)).unwrap())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| {
                    <$ty as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(&bytes)).unwrap()
                })
            });
        };
    }

    bench_decode!("bool", bool, true);
    bench_decode!("u8", u8, 0xABu8);
    bench_decode!("u16", u16, 0xABCDu16);
    bench_decode!("u32", u32, 0xDEAD_BEEFu32);
    bench_decode!("u64", u64, 0x1234_5678_9ABC_DEF0u64);
    bench_decode_no_ssz_rs!("u128", u128, u128::MAX);
    group.finish();
}

fn diff_decode_byte_arrays(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/byte_arrays");

    macro_rules! bench_decode_bytes {
        ($name:expr, $ty:ty, $val:expr) => {
            let bytes = pre_encode(&$val);
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| <$ty as SszDecode>::from_ssz_bytes(black_box(&bytes)).unwrap())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| {
                    <$ty as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(&bytes)).unwrap()
                })
            });
            group.bench_function(concat!("ssz_rs/", $name), |b| {
                b.iter(|| <$ty as ssz_rs::Deserialize>::deserialize(black_box(&bytes)).unwrap())
            });
        };
    }

    macro_rules! bench_decode_bytes_no_ssz_rs {
        ($name:expr, $ty:ty, $val:expr) => {
            let bytes = pre_encode(&$val);
            group.bench_function(concat!("libssz/", $name), |b| {
                b.iter(|| <$ty as SszDecode>::from_ssz_bytes(black_box(&bytes)).unwrap())
            });
            group.bench_function(concat!("lighthouse/", $name), |b| {
                b.iter(|| {
                    <$ty as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(&bytes)).unwrap()
                })
            });
        };
    }

    bench_decode_bytes!("bytes32", [u8; 32], [0xABu8; 32]);
    bench_decode_bytes_no_ssz_rs!("bytes48", [u8; 48], [0xABu8; 48]);
    bench_decode_bytes_no_ssz_rs!("bytes96", [u8; 96], [0xABu8; 96]);
    group.finish();
}

fn diff_decode_vec_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/vec_u64");
    for &size in &[100, 1_000, 100_000] {
        let data = make_vec_u64(size);
        let bytes = pre_encode(&data);
        group.throughput(Throughput::Bytes((size * 8) as u64));
        group.bench_with_input(BenchmarkId::new("libssz", size), &bytes, |b, bytes| {
            b.iter(|| <Vec<u64> as SszDecode>::from_ssz_bytes(black_box(bytes)).unwrap());
        });
        group.bench_with_input(BenchmarkId::new("lighthouse", size), &bytes, |b, bytes| {
            b.iter(|| {
                <Vec<u64> as lighthouse_ssz::Decode>::from_ssz_bytes(black_box(bytes)).unwrap()
            });
        });
        group.bench_with_input(BenchmarkId::new("ssz_rs", size), &bytes, |b, bytes| {
            b.iter(|| {
                <ssz_rs::List<u64, 1_000_000> as ssz_rs::Deserialize>::deserialize(black_box(bytes))
                    .unwrap()
            });
        });
    }
    group.finish();
}

fn diff_decode_header(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/header");
    let header = make_header(42);
    let bytes = pre_encode(&header);
    group.bench_function("libssz", |b| {
        b.iter(|| BeaconBlockHeader::from_ssz_bytes(black_box(&bytes)).unwrap())
    });
    group.bench_function("lighthouse", |b| {
        b.iter(|| lighthouse_decode_header(black_box(&bytes)))
    });
    group.bench_function("ssz_rs", |b| {
        b.iter(|| ssz_rs_decode_header(black_box(&bytes)))
    });
    group.finish();
}

// ---------------------------------------------------------------------------
// Hash tree root benchmarks
// ---------------------------------------------------------------------------

fn diff_htr(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/htr");

    // bool
    group.bench_function("libssz/bool", |b| {
        b.iter(|| black_box(true).hash_tree_root())
    });
    group.bench_function("lighthouse/bool", |b| {
        b.iter(|| tree_hash::TreeHash::tree_hash_root(black_box(&true)).0)
    });
    group.bench_function("ssz_rs/bool", |b| {
        b.iter(|| {
            let mut val = *black_box(&true);
            ssz_rs::Merkleized::hash_tree_root(&mut val).unwrap()
        })
    });

    // u64
    let val_u64 = 0x1234_5678_9ABC_DEF0u64;
    group.bench_function("libssz/u64", |b| {
        b.iter(|| black_box(val_u64).hash_tree_root())
    });
    group.bench_function("lighthouse/u64", |b| {
        b.iter(|| tree_hash::TreeHash::tree_hash_root(black_box(&val_u64)).0)
    });
    group.bench_function("ssz_rs/u64", |b| {
        b.iter(|| {
            let mut val = *black_box(&val_u64);
            ssz_rs::Merkleized::hash_tree_root(&mut val).unwrap()
        })
    });

    // [u8; 32]
    let val_bytes32 = [0xABu8; 32];
    group.bench_function("libssz/bytes32", |b| {
        b.iter(|| black_box(&val_bytes32).hash_tree_root())
    });
    group.bench_function("lighthouse/bytes32", |b| {
        b.iter(|| tree_hash::TreeHash::tree_hash_root(black_box(&val_bytes32)).0)
    });
    group.bench_function("ssz_rs/bytes32", |b| {
        b.iter(|| {
            let mut val = *black_box(&val_bytes32);
            ssz_rs::Merkleized::hash_tree_root(&mut val).unwrap()
        })
    });

    // Note: tree_hash and ssz_rs do NOT support u128, so we skip it for HTR.

    group.finish();
}

// ---------------------------------------------------------------------------
// Three-way encode benchmarks for consensus containers
// ---------------------------------------------------------------------------

fn diff_encode_consensus_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/consensus_containers");

    let fork = make_fork();
    group.bench_function("libssz/fork", |b| b.iter(|| black_box(&fork).to_ssz()));
    group.bench_function("lighthouse/fork", |b| {
        b.iter(|| lighthouse_encode_fork(black_box(&fork)))
    });
    group.bench_function("ssz_rs/fork", |b| {
        b.iter(|| ssz_rs_encode_fork(black_box(&fork)))
    });

    let checkpoint = make_checkpoint(42);
    group.bench_function("libssz/checkpoint", |b| {
        b.iter(|| black_box(&checkpoint).to_ssz())
    });
    group.bench_function("lighthouse/checkpoint", |b| {
        b.iter(|| lighthouse_encode_checkpoint(black_box(&checkpoint)))
    });
    group.bench_function("ssz_rs/checkpoint", |b| {
        b.iter(|| ssz_rs_encode_checkpoint(black_box(&checkpoint)))
    });

    let eth1_data = make_eth1_data(42);
    group.bench_function("libssz/eth1_data", |b| {
        b.iter(|| black_box(&eth1_data).to_ssz())
    });
    group.bench_function("lighthouse/eth1_data", |b| {
        b.iter(|| lighthouse_encode_eth1_data(black_box(&eth1_data)))
    });
    group.bench_function("ssz_rs/eth1_data", |b| {
        b.iter(|| ssz_rs_encode_eth1_data(black_box(&eth1_data)))
    });

    let attestation_data = make_attestation_data(42);
    group.bench_function("libssz/attestation_data", |b| {
        b.iter(|| black_box(&attestation_data).to_ssz())
    });
    group.bench_function("lighthouse/attestation_data", |b| {
        b.iter(|| lighthouse_encode_attestation_data(black_box(&attestation_data)))
    });
    group.bench_function("ssz_rs/attestation_data", |b| {
        b.iter(|| ssz_rs_encode_attestation_data(black_box(&attestation_data)))
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Three-way decode benchmarks for consensus containers
// ---------------------------------------------------------------------------

fn diff_decode_consensus_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/consensus_containers");

    let fork_bytes = pre_encode(&make_fork());
    group.bench_function("libssz/fork", |b| {
        b.iter(|| Fork::from_ssz_bytes(black_box(&fork_bytes)).unwrap())
    });
    group.bench_function("lighthouse/fork", |b| {
        b.iter(|| lighthouse_decode_fork(black_box(&fork_bytes)))
    });
    group.bench_function("ssz_rs/fork", |b| {
        b.iter(|| ssz_rs_decode_fork(black_box(&fork_bytes)))
    });

    let checkpoint_bytes = pre_encode(&make_checkpoint(42));
    group.bench_function("libssz/checkpoint", |b| {
        b.iter(|| Checkpoint::from_ssz_bytes(black_box(&checkpoint_bytes)).unwrap())
    });
    group.bench_function("lighthouse/checkpoint", |b| {
        b.iter(|| lighthouse_decode_checkpoint(black_box(&checkpoint_bytes)))
    });
    group.bench_function("ssz_rs/checkpoint", |b| {
        b.iter(|| ssz_rs_decode_checkpoint(black_box(&checkpoint_bytes)))
    });

    let eth1_data_bytes = pre_encode(&make_eth1_data(42));
    group.bench_function("libssz/eth1_data", |b| {
        b.iter(|| Eth1Data::from_ssz_bytes(black_box(&eth1_data_bytes)).unwrap())
    });
    group.bench_function("lighthouse/eth1_data", |b| {
        b.iter(|| lighthouse_decode_eth1_data(black_box(&eth1_data_bytes)))
    });
    group.bench_function("ssz_rs/eth1_data", |b| {
        b.iter(|| ssz_rs_decode_eth1_data(black_box(&eth1_data_bytes)))
    });

    let attestation_data_bytes = pre_encode(&make_attestation_data(42));
    group.bench_function("libssz/attestation_data", |b| {
        b.iter(|| AttestationData::from_ssz_bytes(black_box(&attestation_data_bytes)).unwrap())
    });
    group.bench_function("lighthouse/attestation_data", |b| {
        b.iter(|| lighthouse_decode_attestation_data(black_box(&attestation_data_bytes)))
    });
    group.bench_function("ssz_rs/attestation_data", |b| {
        b.iter(|| ssz_rs_decode_attestation_data(black_box(&attestation_data_bytes)))
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// libssz-only HTR benchmarks for consensus containers
// ---------------------------------------------------------------------------

fn diff_htr_consensus_containers(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/htr/consensus_containers");

    let fork = make_fork();
    group.bench_function("libssz/fork", |b| {
        b.iter(|| black_box(&fork).hash_tree_root())
    });

    let checkpoint = make_checkpoint(42);
    group.bench_function("libssz/checkpoint", |b| {
        b.iter(|| black_box(&checkpoint).hash_tree_root())
    });

    let eth1_data = make_eth1_data(42);
    group.bench_function("libssz/eth1_data", |b| {
        b.iter(|| black_box(&eth1_data).hash_tree_root())
    });

    let attestation_data = make_attestation_data(42);
    group.bench_function("libssz/attestation_data", |b| {
        b.iter(|| black_box(&attestation_data).hash_tree_root())
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Three-way BeaconState encode benchmarks
// ---------------------------------------------------------------------------

fn diff_encode_beacon_state(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/encode/beacon_state");
    group.sample_size(10);

    for &n_validators in &[16_384usize, 100_000, 300_000, 1_000_000] {
        let state = make_beacon_state(n_validators);
        let lh_state = to_lighthouse_beacon_state(&state);
        let ssz_rs_state = to_ssz_rs_beacon_state(&state);

        group.bench_with_input(
            BenchmarkId::new("libssz", n_validators),
            &state,
            |b, state| {
                b.iter(|| black_box(state).to_ssz());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("lighthouse", n_validators),
            &lh_state,
            |b, state| {
                b.iter(|| lighthouse_ssz::Encode::as_ssz_bytes(black_box(state)));
            },
        );
        group.bench_with_input(
            BenchmarkId::new("ssz_rs", n_validators),
            &ssz_rs_state,
            |b, state| {
                b.iter(|| {
                    let mut buf = Vec::new();
                    ssz_rs::Serialize::serialize(black_box(state), &mut buf).unwrap();
                    buf
                });
            },
        );
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Three-way BeaconState decode benchmarks
// ---------------------------------------------------------------------------

fn diff_decode_beacon_state(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/decode/beacon_state");
    group.sample_size(10);

    for &n_validators in &[16_384usize, 100_000, 300_000, 1_000_000] {
        let state = make_beacon_state(n_validators);
        let bytes = pre_encode(&state);
        // Lighthouse and ssz_rs decode from the same SSZ bytes (format is canonical).
        let lh_bytes = lighthouse_ssz::Encode::as_ssz_bytes(&to_lighthouse_beacon_state(&state));
        let ssz_rs_state = to_ssz_rs_beacon_state(&state);
        let mut ssz_rs_bytes = Vec::new();
        ssz_rs::Serialize::serialize(&ssz_rs_state, &mut ssz_rs_bytes).unwrap();

        group.bench_with_input(
            BenchmarkId::new("libssz", n_validators),
            &bytes,
            |b, bytes| {
                b.iter(|| BeaconState::from_ssz_bytes(black_box(bytes)).unwrap());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("lighthouse", n_validators),
            &lh_bytes,
            |b, bytes| {
                b.iter(|| {
                    <lighthouse_types::BeaconState as lighthouse_ssz::Decode>::from_ssz_bytes(
                        black_box(bytes),
                    )
                    .unwrap()
                });
            },
        );
        group.bench_with_input(
            BenchmarkId::new("ssz_rs", n_validators),
            &ssz_rs_bytes,
            |b, bytes| {
                b.iter(|| {
                    <ssz_rs_types::BeaconState as ssz_rs::Deserialize>::deserialize(black_box(
                        bytes,
                    ))
                    .unwrap()
                });
            },
        );
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Three-way BeaconState HTR benchmarks (headline benchmark)
// ---------------------------------------------------------------------------

fn diff_htr_beacon_state(c: &mut Criterion) {
    let mut group = c.benchmark_group("diff/htr/beacon_state");
    group.sample_size(10);

    for &n_validators in &[16_384usize, 100_000, 300_000, 1_000_000] {
        let state = make_beacon_state(n_validators);
        let lh_state = to_lighthouse_beacon_state(&state);
        let ssz_rs_state = to_ssz_rs_beacon_state(&state);

        group.bench_with_input(
            BenchmarkId::new("libssz", n_validators),
            &state,
            |b, state| {
                b.iter(|| black_box(state).hash_tree_root());
            },
        );
        group.bench_with_input(
            BenchmarkId::new("lighthouse", n_validators),
            &lh_state,
            |b, state| {
                b.iter(|| tree_hash::TreeHash::tree_hash_root(black_box(state)));
            },
        );
        // ssz_rs::Merkleized::hash_tree_root takes &mut self
        group.bench_with_input(
            BenchmarkId::new("ssz_rs", n_validators),
            &ssz_rs_state,
            |b, state| {
                b.iter(|| {
                    let mut s = state.clone();
                    ssz_rs::Merkleized::hash_tree_root(&mut s).unwrap()
                });
            },
        );
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Criterion harness
// ---------------------------------------------------------------------------

criterion_group!(
    benches,
    diff_encode_primitives,
    diff_encode_byte_arrays,
    diff_encode_vec_u64,
    diff_encode_header,
    diff_decode_primitives,
    diff_decode_byte_arrays,
    diff_decode_vec_u64,
    diff_decode_header,
    diff_htr,
    diff_encode_consensus_containers,
    diff_decode_consensus_containers,
    diff_htr_consensus_containers,
    diff_encode_beacon_state,
    diff_decode_beacon_state,
    diff_htr_beacon_state,
);
criterion_main!(benches);
