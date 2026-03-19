use ssz::SszEncode;
use ssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use ssz_merkle::{merkleize, mix_in_length, HashTreeRoot, Node};
use ssz_types::{SszBitlist, SszBitvector, SszList, SszVector};

/// Ethereum consensus Validator (121 bytes, all fixed-size fields).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
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

/// Ethereum consensus BeaconBlockHeader (112 bytes, all fixed-size fields).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BeaconBlockHeader {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body_root: [u8; 32],
}

/// Ethereum consensus Fork (16 bytes, all fixed-size fields).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Fork {
    pub previous_version: [u8; 4],
    pub current_version: [u8; 4],
    pub epoch: u64,
}

/// Ethereum consensus Checkpoint (40 bytes, all fixed-size fields).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Checkpoint {
    pub epoch: u64,
    pub root: [u8; 32],
}

/// Ethereum consensus Eth1Data (72 bytes, all fixed-size fields).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Eth1Data {
    pub deposit_root: [u8; 32],
    pub deposit_count: u64,
    pub block_hash: [u8; 32],
}

/// Ethereum consensus AttestationData (128 bytes, all fixed-size fields).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AttestationData {
    pub slot: u64,
    pub index: u64,
    pub beacon_block_root: [u8; 32],
    pub source: Checkpoint,
    pub target: Checkpoint,
}

/// Ethereum consensus PendingAttestation (variable-size, contains Bitlist).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PendingAttestation {
    pub aggregation_bits: SszBitlist<2048>,
    pub data: AttestationData,
    pub inclusion_delay: u64,
    pub proposer_index: u64,
}

/// Ethereum consensus BeaconState Phase 0 (21 fields, variable-size).
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BeaconState {
    pub genesis_time: u64,
    pub genesis_validators_root: [u8; 32],
    pub slot: u64,
    pub fork: Fork,
    pub latest_block_header: BeaconBlockHeader,
    pub block_roots: SszVector<[u8; 32], 8192>,
    pub state_roots: SszVector<[u8; 32], 8192>,
    pub historical_roots: SszList<[u8; 32], 16_777_216>,
    pub eth1_data: Eth1Data,
    pub eth1_data_votes: SszList<Eth1Data, 2048>,
    pub eth1_deposit_index: u64,
    pub validators: SszList<Validator, 1_099_511_627_776>,
    pub balances: SszList<u64, 1_099_511_627_776>,
    pub randao_mixes: SszVector<[u8; 32], 65536>,
    pub slashings: SszVector<u64, 8192>,
    pub previous_epoch_attestations: SszList<PendingAttestation, 4096>,
    pub current_epoch_attestations: SszList<PendingAttestation, 4096>,
    pub justification_bits: SszBitvector<4>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
}

/// Create a deterministic Validator from a seed.
pub fn make_validator(seed: u64) -> Validator {
    let seed_bytes = seed.to_le_bytes();
    let mut pubkey = [0u8; 48];
    for (i, chunk) in pubkey.chunks_mut(8).enumerate() {
        let val = seed.wrapping_add(i as u64);
        chunk.copy_from_slice(&val.to_le_bytes());
    }
    let mut withdrawal_credentials = [0u8; 32];
    for (i, chunk) in withdrawal_credentials.chunks_mut(8).enumerate() {
        let val = seed.wrapping_mul(31).wrapping_add(i as u64);
        chunk.copy_from_slice(&val.to_le_bytes());
    }
    Validator {
        pubkey,
        withdrawal_credentials,
        effective_balance: 32_000_000_000,
        slashed: seed_bytes[0] & 1 == 1,
        activation_eligibility_epoch: seed,
        activation_epoch: seed.wrapping_add(1),
        exit_epoch: u64::MAX,
        withdrawable_epoch: u64::MAX,
    }
}

/// Create a deterministic BeaconBlockHeader from a seed.
pub fn make_header(seed: u64) -> BeaconBlockHeader {
    let mut parent_root = [0u8; 32];
    let mut state_root = [0u8; 32];
    let mut body_root = [0u8; 32];
    for (i, chunk) in parent_root.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_add(i as u64).to_le_bytes());
    }
    for (i, chunk) in state_root.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_mul(7).wrapping_add(i as u64).to_le_bytes());
    }
    for (i, chunk) in body_root.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_mul(13).wrapping_add(i as u64).to_le_bytes());
    }
    BeaconBlockHeader {
        slot: seed,
        proposer_index: seed.wrapping_mul(3),
        parent_root,
        state_root,
        body_root,
    }
}

/// Create a deterministic Fork.
pub fn make_fork() -> Fork {
    Fork {
        previous_version: [0x00, 0x00, 0x00, 0x00],
        current_version: [0x01, 0x00, 0x00, 0x00],
        epoch: 100,
    }
}

/// Create a deterministic Checkpoint from a seed.
pub fn make_checkpoint(seed: u64) -> Checkpoint {
    let mut root = [0u8; 32];
    for (i, chunk) in root.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_mul(17).wrapping_add(i as u64).to_le_bytes());
    }
    Checkpoint { epoch: seed, root }
}

/// Create a deterministic Eth1Data from a seed.
pub fn make_eth1_data(seed: u64) -> Eth1Data {
    let mut deposit_root = [0u8; 32];
    let mut block_hash = [0u8; 32];
    for (i, chunk) in deposit_root.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_mul(11).wrapping_add(i as u64).to_le_bytes());
    }
    for (i, chunk) in block_hash.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_mul(23).wrapping_add(i as u64).to_le_bytes());
    }
    Eth1Data {
        deposit_root,
        deposit_count: seed.wrapping_mul(5),
        block_hash,
    }
}

/// Create a deterministic AttestationData from a seed.
pub fn make_attestation_data(seed: u64) -> AttestationData {
    let mut beacon_block_root = [0u8; 32];
    for (i, chunk) in beacon_block_root.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_mul(29).wrapping_add(i as u64).to_le_bytes());
    }
    AttestationData {
        slot: seed,
        index: seed.wrapping_mul(3),
        beacon_block_root,
        source: make_checkpoint(seed),
        target: make_checkpoint(seed.wrapping_add(1)),
    }
}

/// Create a deterministic PendingAttestation from a seed.
pub fn make_pending_attestation(seed: u64) -> PendingAttestation {
    let mut bl = SszBitlist::<2048>::with_length(2048).expect("valid length");
    for i in (0..2048).step_by(3) {
        bl.set(i, true).unwrap();
    }
    PendingAttestation {
        aggregation_bits: bl,
        data: make_attestation_data(seed),
        inclusion_delay: seed.wrapping_add(1),
        proposer_index: seed.wrapping_mul(7),
    }
}

fn make_bytes32(seed: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, chunk) in b.chunks_mut(8).enumerate() {
        chunk.copy_from_slice(&seed.wrapping_add(i as u64).to_le_bytes());
    }
    b
}

/// Create a deterministic BeaconState with n_validators validators.
pub fn make_beacon_state(n_validators: usize) -> BeaconState {
    let block_roots: Vec<[u8; 32]> = (0..8192).map(|i| make_bytes32(i as u64)).collect();
    let state_roots: Vec<[u8; 32]> = (0..8192).map(|i| make_bytes32(i as u64 + 10000)).collect();
    let historical_roots: Vec<[u8; 32]> = (0..16).map(|i| make_bytes32(i as u64 + 20000)).collect();
    let eth1_data_votes: Vec<Eth1Data> = (0..16).map(|i| make_eth1_data(i as u64)).collect();
    let validators: Vec<Validator> = (0..n_validators)
        .map(|i| make_validator(i as u64))
        .collect();
    let balances: Vec<u64> = (0..n_validators).map(|_| 32_000_000_000u64).collect();
    let randao_mixes: Vec<[u8; 32]> = (0..65536).map(|i| make_bytes32(i as u64 + 30000)).collect();
    let slashings: Vec<u64> = vec![0u64; 8192];
    let prev_attestations: Vec<PendingAttestation> = (0..16)
        .map(|i| make_pending_attestation(i as u64))
        .collect();
    let cur_attestations: Vec<PendingAttestation> = (0..16)
        .map(|i| make_pending_attestation(i as u64 + 100))
        .collect();

    let mut justification_bits = SszBitvector::<4>::new();
    justification_bits.set(0, true).unwrap();
    justification_bits.set(1, true).unwrap();

    BeaconState {
        genesis_time: 1606824023,
        genesis_validators_root: make_bytes32(42),
        slot: 1000,
        fork: make_fork(),
        latest_block_header: make_header(999),
        block_roots: SszVector::try_from(block_roots).expect("exact size"),
        state_roots: SszVector::try_from(state_roots).expect("exact size"),
        historical_roots: SszList::try_from(historical_roots).expect("fits"),
        eth1_data: make_eth1_data(0),
        eth1_data_votes: SszList::try_from(eth1_data_votes).expect("fits"),
        eth1_deposit_index: 1000,
        validators: SszList::try_from(validators).expect("fits"),
        balances: SszList::try_from(balances).expect("fits"),
        randao_mixes: SszVector::try_from(randao_mixes).expect("exact size"),
        slashings: SszVector::try_from(slashings).expect("exact size"),
        previous_epoch_attestations: SszList::try_from(prev_attestations).expect("fits"),
        current_epoch_attestations: SszList::try_from(cur_attestations).expect("fits"),
        justification_bits,
        previous_justified_checkpoint: make_checkpoint(99),
        current_justified_checkpoint: make_checkpoint(100),
        finalized_checkpoint: make_checkpoint(98),
    }
}

/// Create a list of validators (SszList with limit 1_048_576 = VALIDATOR_REGISTRY_LIMIT).
pub fn make_validator_list(n: usize) -> SszList<Validator, 1_048_576> {
    let validators: Vec<Validator> = (0..n).map(|i| make_validator(i as u64)).collect();
    SszList::try_from(validators).expect("n <= 1_048_576")
}

/// Create a `Vec<u64>` of given length.
pub fn make_vec_u64(n: usize) -> Vec<u64> {
    (0..n).map(|i| i as u64).collect()
}

/// Create a SszVector of [u8; 32] with given count.
pub fn make_vector_bytes32<const N: usize>() -> SszVector<[u8; 32], N> {
    let items: Vec<[u8; 32]> = (0..N)
        .map(|i| {
            let mut b = [0u8; 32];
            b[..8].copy_from_slice(&(i as u64).to_le_bytes());
            b
        })
        .collect();
    SszVector::try_from(items).expect("exact size")
}

/// Create a Bitlist with 2048 bits (MAX_VALIDATORS_PER_COMMITTEE).
pub fn make_bitlist_2048() -> SszBitlist<2048> {
    let mut bl = SszBitlist::<2048>::with_length(2048).expect("valid length");
    // Set every third bit
    for i in (0..2048).step_by(3) {
        bl.set(i, true).unwrap();
    }
    bl
}

/// Create a Bitvector with 512 bits (SYNC_COMMITTEE_SIZE).
pub fn make_bitvector_512() -> SszBitvector<512> {
    let mut bv = SszBitvector::<512>::new();
    // Set every other bit
    for i in (0..512).step_by(2) {
        bv.set(i, true).unwrap();
    }
    bv
}

// ── Union type ──

#[derive(Clone, Debug, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(enum_behaviour = "union")]
pub enum BenchUnion {
    U64(u64),
    Bytes32([u8; 32]),
    Header(BeaconBlockHeader),
    VarBytes(Vec<u8>),
}

// ── Mixed fixed + variable container ──

#[derive(Clone, Debug, SszEncode, SszDecode, HashTreeRoot)]
pub struct VariableContainer {
    pub fixed_field: u64,
    pub var_field: Vec<u8>,
    pub fixed_field2: [u8; 32],
    pub var_field2: Vec<u64>,
}

// ── Container with nested list of containers ──

#[derive(Clone, Debug, SszEncode, SszDecode)]
pub struct NestedContainer {
    pub header: BeaconBlockHeader,
    pub validators: Vec<Validator>,
    pub extra: u64,
}

impl HashTreeRoot for NestedContainer {
    fn hash_tree_root(&self) -> Node {
        let header_root = self.header.hash_tree_root();
        let validator_roots: Vec<Node> =
            self.validators.iter().map(|v| v.hash_tree_root()).collect();
        let validators_data_root = if validator_roots.is_empty() {
            merkleize(&[[0u8; 32]], None)
        } else {
            merkleize(&validator_roots, None)
        };
        let validators_root = mix_in_length(&validators_data_root, self.validators.len());
        let extra_root = self.extra.hash_tree_root();
        merkleize(&[header_root, validators_root, extra_root], None)
    }
}

// ── Fixture builders ──

pub fn make_bench_union(variant: usize) -> BenchUnion {
    match variant {
        0 => BenchUnion::U64(0xDEAD_BEEF),
        1 => {
            let mut b = [0u8; 32];
            b[..8].copy_from_slice(&42u64.to_le_bytes());
            BenchUnion::Bytes32(b)
        }
        2 => BenchUnion::Header(make_header(99)),
        _ => BenchUnion::VarBytes(vec![0xAB; 256]),
    }
}

pub fn make_variable_container(var_size: usize) -> VariableContainer {
    let mut fixed_field2 = [0u8; 32];
    fixed_field2[..8].copy_from_slice(&7u64.to_le_bytes());
    VariableContainer {
        fixed_field: 42,
        var_field: vec![0xCC; var_size],
        fixed_field2,
        var_field2: (0..var_size).map(|i| i as u64).collect(),
    }
}

pub fn make_nested_container(n_validators: usize) -> NestedContainer {
    NestedContainer {
        header: make_header(42),
        validators: (0..n_validators)
            .map(|i| make_validator(i as u64))
            .collect(),
        extra: 123,
    }
}

pub fn make_bitlist<const N: usize>(len: usize) -> SszBitlist<N> {
    let mut bl = SszBitlist::<N>::with_length(len).expect("valid length");
    for i in (0..len).step_by(3) {
        bl.set(i, true).unwrap();
    }
    bl
}

pub fn make_bitvector<const N: usize>() -> SszBitvector<N> {
    let mut bv = SszBitvector::<N>::new();
    for i in (0..N).step_by(2) {
        bv.set(i, true).unwrap();
    }
    bv
}

pub fn make_list_u64(n: usize) -> SszList<u64, 1_048_576> {
    let items: Vec<u64> = (0..n).map(|i| i as u64).collect();
    SszList::try_from(items).expect("n <= 1_048_576")
}

/// Pre-encode a value to bytes for decode benchmarks.
pub fn pre_encode<T: SszEncode>(value: &T) -> Vec<u8> {
    value.to_ssz()
}
