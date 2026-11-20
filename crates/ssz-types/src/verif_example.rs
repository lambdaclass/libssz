//! Example containers for the formal proofs of `hash_tree_root` against the EthLib
//! specification, for types with lists and vectors.
//!
//! These are consensus-layer containers (phase0 and altair, with mainnet sizes) that
//! have `SszList` and `SszVector`, with the `#[derive(HashTreeRoot)]` from `crates/ssz-derive`:
//! Charon translates exactly the `hash_tree_root` the macro generates. `AttestationData` is
//! the one from `libssz_merkle::verif_example`, whose root is already proven.
//!
//! `ExecutionPayload` (capella) has a list of containers (`withdrawals`), a list of
//! lists (`transactions`) and bytes in `SszList<u8>` and `SszVector<u8>`. List items
//! must implement `SszEncode`, so `Withdrawal` derives it.
//!
//! Only compiled with the `verif-example` feature. Not part of the API.

use alloc::vec::Vec;

use libssz::{SszDecode, SszEncode};
use libssz_derive::{HashTreeRoot, SszEncode};
use libssz_merkle::verif_example::{
    AttestationData, BeaconBlockHeader, Checkpoint, Fork, Validator,
};

use crate::{SszBitlist, SszBitvector, SszList, SszVector};

/// phase0: two vectors of roots.
#[derive(HashTreeRoot)]
pub struct HistoricalBatch {
    pub block_roots: SszVector<[u8; 32], 8192>,
    pub state_roots: SszVector<[u8; 32], 8192>,
}

/// phase0: a list of integers and a container.
#[derive(HashTreeRoot, SszEncode)]
pub struct IndexedAttestation {
    pub attesting_indices: SszList<u64, 2048>,
    pub data: AttestationData,
    pub signature: [u8; 96],
}

/// phase0.
#[derive(HashTreeRoot, SszEncode)]
pub struct DepositData {
    pub pubkey: [u8; 48],
    pub withdrawal_credentials: [u8; 32],
    pub amount: u64,
    pub signature: [u8; 96],
}

/// phase0: the deposit's Merkle proof is a vector of 33 roots.
#[derive(HashTreeRoot, SszEncode)]
pub struct Deposit {
    pub proof: SszVector<[u8; 32], 33>,
    pub data: DepositData,
}

/// altair: a vector of composite items (48-byte public keys).
#[derive(HashTreeRoot)]
pub struct SyncCommittee {
    pub pubkeys: SszVector<[u8; 48], 512>,
    pub aggregate_pubkey: [u8; 48],
}

/// Four `BeaconState` fields (phase0), with their limits: vectors and lists of roots and
/// of integers.
///
/// `validators` and `balances` are left out, since their limit is 2^40: the Aeneas model
/// does not fix the width of `usize` (it may be 32 bits), and there 2^40 is not a `usize`.
#[derive(HashTreeRoot)]
pub struct StateLists {
    pub block_roots: SszVector<[u8; 32], 8192>,
    pub historical_roots: SszList<[u8; 32], 16777216>,
    pub randao_mixes: SszVector<[u8; 32], 65536>,
    pub slashings: SszVector<u64, 8192>,
}

/// capella.
#[derive(HashTreeRoot, SszEncode)]
pub struct Withdrawal {
    pub index: u64,
    pub validator_index: u64,
    pub address: [u8; 20],
    pub amount: u64,
}

/// capella, with mainnet sizes. `base_fee_per_gas` is a `uint256` in the
/// specification, stored as its 32 little-endian bytes (as in `spec-tests`).
#[derive(HashTreeRoot)]
pub struct ExecutionPayload {
    pub parent_hash: [u8; 32],
    pub fee_recipient: [u8; 20],
    pub state_root: [u8; 32],
    pub receipts_root: [u8; 32],
    pub logs_bloom: SszVector<u8, 256>,
    pub prev_randao: [u8; 32],
    pub block_number: u64,
    pub gas_limit: u64,
    pub gas_used: u64,
    pub timestamp: u64,
    pub extra_data: SszList<u8, 32>,
    pub base_fee_per_gas: [u8; 32],
    pub block_hash: [u8; 32],
    pub transactions: SszList<SszList<u8, 1073741824>, 1048576>,
    pub withdrawals: SszList<Withdrawal, 16>,
}

/// phase0: the bits of who signed, in an `SszBitlist`.
#[derive(HashTreeRoot, SszEncode)]
pub struct Attestation {
    pub aggregation_bits: SszBitlist<2048>,
    pub data: AttestationData,
    pub signature: [u8; 96],
}

/// phase0: the items of `previous_epoch_attestations` and `current_epoch_attestations` in
/// `BeaconState`.
#[derive(HashTreeRoot, SszEncode)]
pub struct PendingAttestation {
    pub aggregation_bits: SszBitlist<2048>,
    pub data: AttestationData,
    pub inclusion_delay: u64,
    pub proposer_index: u64,
}

/// altair: an `SszBitvector`.
#[derive(HashTreeRoot)]
pub struct SyncAggregate {
    pub sync_committee_bits: SszBitvector<512>,
    pub sync_committee_signature: [u8; 96],
}

/// The `SszEncode` and `SszDecode` methods of the two bitfields, so that the extraction
/// brings their full implementations. Not used anywhere else.
#[allow(clippy::too_many_arguments)]
pub fn bitfield_methods<const N: usize>(
    bl: &SszBitlist<N>,
    bv: &SszBitvector<N>,
    bls: &[SszBitlist<N>],
    bvs: &[SszBitvector<N>],
    bytes: &[u8],
    buf: &mut Vec<u8>,
    out: &mut [u8],
) {
    ssz_encode_methods(bl, bls, buf, out);
    ssz_encode_methods(bv, bvs, buf, out);
    ssz_decode_methods::<SszBitlist<N>>(bytes);
    ssz_decode_methods::<SszBitvector<N>>(bytes);
}

/// Calls each `SszDecode` method once (see `ssz_encode_methods`).
pub fn ssz_decode_methods<T: SszDecode>(bytes: &[u8]) {
    let _ = T::is_fixed_size();
    let _ = T::fixed_size();
    let _ = T::from_ssz_bytes(bytes);
    let _ = T::ssz_decode_fixed_vec(bytes);
}

/// phase0.
#[derive(HashTreeRoot, SszEncode)]
pub struct Eth1Data {
    pub deposit_root: [u8; 32],
    pub deposit_count: u64,
    pub block_hash: [u8; 32],
}

/// phase0.
#[derive(HashTreeRoot, SszEncode)]
pub struct SignedBeaconBlockHeader {
    pub message: BeaconBlockHeader,
    pub signature: [u8; 96],
}

/// phase0.
#[derive(HashTreeRoot, SszEncode)]
pub struct ProposerSlashing {
    pub signed_header_1: SignedBeaconBlockHeader,
    pub signed_header_2: SignedBeaconBlockHeader,
}

/// phase0.
#[derive(HashTreeRoot, SszEncode)]
pub struct AttesterSlashing {
    pub attestation_1: IndexedAttestation,
    pub attestation_2: IndexedAttestation,
}

/// phase0.
#[derive(HashTreeRoot, SszEncode)]
pub struct VoluntaryExit {
    pub epoch: u64,
    pub validator_index: u64,
}

/// phase0.
#[derive(HashTreeRoot, SszEncode)]
pub struct SignedVoluntaryExit {
    pub message: VoluntaryExit,
    pub signature: [u8; 96],
}

/// phase0, with mainnet sizes.
#[derive(HashTreeRoot)]
pub struct BeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, 16>,
    pub attester_slashings: SszList<AttesterSlashing, 2>,
    pub attestations: SszList<Attestation, 128>,
    pub deposits: SszList<Deposit, 16>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, 16>,
}

/// phase0.
#[derive(HashTreeRoot)]
pub struct BeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: BeaconBlockBody,
}

/// phase0, with mainnet sizes but one: the limit of `validators` and `balances`
/// (`VALIDATOR_REGISTRY_LIMIT`, 2^40 on mainnet) is a parameter. In the Aeneas model
/// `usize` may be 32 bits, and there 2^40 is not a `usize`; with the parameter, the theorem
/// holds for every limit, and on 64 bits `BeaconState<1099511627776>` is the mainnet one.
#[derive(HashTreeRoot)]
pub struct BeaconState<const VRL: usize> {
    pub genesis_time: u64,
    pub genesis_validators_root: [u8; 32],
    pub slot: u64,
    pub fork: Fork,
    pub latest_block_header: BeaconBlockHeader,
    pub block_roots: SszVector<[u8; 32], 8192>,
    pub state_roots: SszVector<[u8; 32], 8192>,
    pub historical_roots: SszList<[u8; 32], 16777216>,
    pub eth1_data: Eth1Data,
    pub eth1_data_votes: SszList<Eth1Data, 2048>,
    pub eth1_deposit_index: u64,
    pub validators: SszList<Validator, VRL>,
    pub balances: SszList<u64, VRL>,
    pub randao_mixes: SszVector<[u8; 32], 65536>,
    pub slashings: SszVector<u64, 8192>,
    pub previous_epoch_attestations: SszList<PendingAttestation, 4096>,
    pub current_epoch_attestations: SszList<PendingAttestation, 4096>,
    pub justification_bits: SszBitvector<4>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
}

/// Calls each `SszEncode` method once. Each crate is translated to Lean separately, and
/// Charon copies into a crate's translation only the methods of another crate's trait that
/// the code names. The proofs then link that copy to the full trait from the codec's
/// translation, which needs the copy to be complete: this function names every method, so
/// every implementation brings all of them. Not used anywhere else.
pub fn ssz_encode_methods<T: SszEncode>(x: &T, items: &[T], buf: &mut Vec<u8>, out: &mut [u8]) {
    let _ = T::is_fixed_size();
    let _ = T::fixed_size();
    let _ = x.encoded_len();
    x.ssz_append(buf);
    let _ = x.to_ssz();
    T::ssz_append_fixed_slice(items, buf);
    let _ = T::ssz_has_write_fixed();
    x.ssz_write_fixed(out);
    let _ = T::ssz_fixed_slice_to_vec(items);
}
