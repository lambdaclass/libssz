use ssz::SszEncode;
use ssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use ssz_merkle::{merkleize, mix_in_length, pack, HashTreeRoot, Node};
use ssz_types::{SszBitlist, SszBitvector, SszList, SszVector};

/// Ethereum consensus Validator (121 bytes, all fixed-size fields).
/// HashTreeRoot implemented manually because `[u8; 48]` doesn't implement HashTreeRoot.
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode)]
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

impl HashTreeRoot for Validator {
    fn hash_tree_root(&self) -> Node {
        // Each field is hashed as a leaf: fixed-size fields <= 32 bytes go in a single chunk,
        // [u8; 48] gets packed into two chunks and merkleized.
        let pubkey_root = merkleize(&pack(&self.pubkey), None);
        let roots = [
            pubkey_root,
            self.withdrawal_credentials.hash_tree_root(),
            self.effective_balance.hash_tree_root(),
            self.slashed.hash_tree_root(),
            self.activation_eligibility_epoch.hash_tree_root(),
            self.activation_epoch.hash_tree_root(),
            self.exit_epoch.hash_tree_root(),
            self.withdrawable_epoch.hash_tree_root(),
        ];
        merkleize(&roots, None)
    }
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

/// Create a list of validators (SszList with limit 1_048_576 = VALIDATOR_REGISTRY_LIMIT).
pub fn make_validator_list(n: usize) -> SszList<Validator, 1_048_576> {
    let validators: Vec<Validator> = (0..n).map(|i| make_validator(i as u64)).collect();
    SszList::try_from(validators).expect("n <= 1_048_576")
}

/// Create a Vec<u64> of given length.
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
        bl.set(i, true);
    }
    bl
}

/// Create a Bitvector with 512 bits (SYNC_COMMITTEE_SIZE).
pub fn make_bitvector_512() -> SszBitvector<512> {
    let mut bv = SszBitvector::<512>::new();
    // Set every other bit
    for i in (0..512).step_by(2) {
        bv.set(i, true);
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
        bl.set(i, true);
    }
    bl
}

pub fn make_bitvector<const N: usize>() -> SszBitvector<N> {
    let mut bv = SszBitvector::<N>::new();
    for i in (0..N).step_by(2) {
        bv.set(i, true);
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
