//! Gloas types as of consensus-specs v1.7.0-alpha.13.
//!
//! Gloas adopts EIP-7688 (progressive containers and lists) and EIP-7732
//! (enshrined proposer-builder separation), so many containers here are
//! `#[ssz(progressive_container)]` and use `ProgressiveList` where earlier
//! forks used bounded `SszList`.

use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{ProgressiveBitlist, ProgressiveList, SszBitvector, SszList, SszVector};

use super::altair::{SyncAggregate, SyncCommittee};
use super::bellatrix::{BYTES_PER_LOGS_BLOOM, MAX_EXTRA_DATA_BYTES};
use super::capella::{HistoricalSummary, SignedBLSToExecutionChange, Withdrawal};
use super::electra::{
    ConsolidationRequest, DepositRequest, PendingConsolidation, PendingDeposit,
    PendingPartialWithdrawal, WithdrawalRequest, MAX_COMMITTEES_PER_SLOT,
};
use super::phase0::{
    AttestationData, BeaconBlockHeader, Checkpoint, Deposit, Eth1Data, Fork, ProposerSlashing,
    SignedVoluntaryExit, Validator, EPOCHS_PER_ETH1_VOTING_PERIOD, EPOCHS_PER_HISTORICAL_VECTOR,
    EPOCHS_PER_SLASHINGS_VECTOR, HISTORICAL_ROOTS_LIMIT, JUSTIFICATION_BITS_LENGTH,
    SLOTS_PER_EPOCH, SLOTS_PER_HISTORICAL_ROOT,
};

pub const PTC_SIZE: usize = 512;
pub const MIN_SEED_LOOKAHEAD: usize = 1;

const ETH1_DATA_VOTES_LIMIT: usize = EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH;
const PROPOSER_LOOKAHEAD_LEN: usize = (MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH;
const PTC_WINDOW_LEN: usize = (2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH;
const BUILDER_PENDING_PAYMENTS_LEN: usize = 2 * SLOTS_PER_EPOCH;

// Light client branch lengths are `floorlog2` of the corresponding gindex.
// EIP-7688 reshapes `BeaconState`, so these grow relative to Electra.
/// `floorlog2(EXECUTION_BLOCK_HASH_GINDEX_GLOAS)`, where the gindex is 2856.
pub const EXECUTION_BRANCH_LEN: usize = 11;
/// `floorlog2(FINALIZED_ROOT_GINDEX_GLOAS)`, where the gindex is 735.
pub const FINALITY_BRANCH_LEN: usize = 9;
/// `floorlog2(CURRENT_SYNC_COMMITTEE_GINDEX_GLOAS)`, where the gindex is 2945.
pub const CURRENT_SYNC_COMMITTEE_BRANCH_LEN: usize = 11;
/// `floorlog2(NEXT_SYNC_COMMITTEE_GINDEX_GLOAS)`, where the gindex is 2946.
pub const NEXT_SYNC_COMMITTEE_BRANCH_LEN: usize = 11;

/// `Transaction` and `BlockAccessList` are `ProgressiveByteList`, which is a
/// progressive list of bytes.
pub type ProgressiveByteList = ProgressiveList<u8>;

// ── Builder types ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Builder {
    pub pubkey: [u8; 48],
    pub version: u8,
    pub execution_address: [u8; 20],
    pub balance: u64,
    pub deposit_epoch: u64,
    pub withdrawable_epoch: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BuilderPendingWithdrawal {
    pub fee_recipient: [u8; 20],
    pub amount: u64,
    pub builder_index: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BuilderPendingPayment {
    pub weight: u64,
    pub withdrawal: BuilderPendingWithdrawal,
    pub proposer_index: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BuilderDepositRequest {
    pub pubkey: [u8; 48],
    pub withdrawal_credentials: [u8; 32],
    pub amount: u64,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BuilderExitRequest {
    pub source_address: [u8; 20],
    pub pubkey: [u8; 48],
}

// ── Attestations ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct Attestation {
    pub aggregation_bits: ProgressiveBitlist,
    pub data: AttestationData,
    pub signature: [u8; 96],
    pub committee_bits: SszBitvector<MAX_COMMITTEES_PER_SLOT>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct IndexedAttestation {
    pub attesting_indices: ProgressiveList<u64>,
    pub data: AttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AttesterSlashing {
    pub attestation_1: IndexedAttestation,
    pub attestation_2: IndexedAttestation,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AggregateAndProof {
    pub aggregator_index: u64,
    pub aggregate: Attestation,
    pub selection_proof: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedAggregateAndProof {
    pub message: AggregateAndProof,
    pub signature: [u8; 96],
}

// ── Payload attestations ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PayloadAttestationData {
    pub beacon_block_root: [u8; 32],
    pub slot: u64,
    pub payload_present: bool,
    pub blob_data_available: bool,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct PayloadAttestation {
    pub aggregation_bits: SszBitvector<PTC_SIZE>,
    pub data: PayloadAttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PayloadAttestationMessage {
    pub validator_index: u64,
    pub data: PayloadAttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct IndexedPayloadAttestation {
    pub attesting_indices: SszList<u64, PTC_SIZE>,
    pub data: PayloadAttestationData,
    pub signature: [u8; 96],
}

// ── Execution ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct ExecutionRequests {
    pub deposits: ProgressiveList<DepositRequest>,
    pub withdrawals: ProgressiveList<WithdrawalRequest>,
    pub consolidations: ProgressiveList<ConsolidationRequest>,
    pub builder_deposits: ProgressiveList<BuilderDepositRequest>,
    pub builder_exits: ProgressiveList<BuilderExitRequest>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct ExecutionPayload {
    pub parent_hash: [u8; 32],
    pub fee_recipient: [u8; 20],
    pub state_root: [u8; 32],
    pub receipts_root: [u8; 32],
    pub logs_bloom: SszVector<u8, BYTES_PER_LOGS_BLOOM>,
    pub prev_randao: [u8; 32],
    pub block_number: u64,
    pub gas_limit: u64,
    pub gas_used: u64,
    pub timestamp: u64,
    pub extra_data: SszList<u8, MAX_EXTRA_DATA_BYTES>,
    pub base_fee_per_gas: [u8; 32],
    pub block_hash: [u8; 32],
    pub transactions: ProgressiveList<ProgressiveByteList>,
    pub withdrawals: ProgressiveList<Withdrawal>,
    pub blob_gas_used: u64,
    pub excess_blob_gas: u64,
    pub block_access_list: ProgressiveByteList,
    pub slot_number: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct ExecutionPayloadBid {
    pub parent_block_hash: [u8; 32],
    pub parent_block_root: [u8; 32],
    pub block_hash: [u8; 32],
    pub prev_randao: [u8; 32],
    pub fee_recipient: [u8; 20],
    pub gas_limit: u64,
    pub builder_index: u64,
    pub slot: u64,
    pub value: u64,
    pub execution_payment: u64,
    pub blob_kzg_commitments: ProgressiveList<[u8; 48]>,
    pub execution_requests_root: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedExecutionPayloadBid {
    pub message: ExecutionPayloadBid,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct ExecutionPayloadEnvelope {
    pub payload: ExecutionPayload,
    pub execution_requests: ExecutionRequests,
    pub builder_index: u64,
    pub beacon_block_root: [u8; 32],
    pub parent_beacon_block_root: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedExecutionPayloadEnvelope {
    pub message: ExecutionPayloadEnvelope,
    pub signature: [u8; 96],
}

// ── Beacon block and state ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct BeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: ProgressiveList<ProposerSlashing>,
    pub attester_slashings: ProgressiveList<AttesterSlashing>,
    pub attestations: ProgressiveList<Attestation>,
    pub deposits: ProgressiveList<Deposit>,
    pub voluntary_exits: ProgressiveList<SignedVoluntaryExit>,
    pub sync_aggregate: SyncAggregate,
    pub bls_to_execution_changes: ProgressiveList<SignedBLSToExecutionChange>,
    pub signed_execution_payload_bid: SignedExecutionPayloadBid,
    pub payload_attestations: ProgressiveList<PayloadAttestation>,
    pub parent_execution_requests: ExecutionRequests,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: BeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedBeaconBlock {
    pub message: BeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct BeaconState {
    pub genesis_time: u64,
    pub genesis_validators_root: [u8; 32],
    pub slot: u64,
    pub fork: Fork,
    pub latest_block_header: BeaconBlockHeader,
    pub block_roots: SszVector<[u8; 32], SLOTS_PER_HISTORICAL_ROOT>,
    pub state_roots: SszVector<[u8; 32], SLOTS_PER_HISTORICAL_ROOT>,
    pub historical_roots: SszList<[u8; 32], HISTORICAL_ROOTS_LIMIT>,
    pub eth1_data: Eth1Data,
    pub eth1_data_votes: SszList<Eth1Data, ETH1_DATA_VOTES_LIMIT>,
    pub eth1_deposit_index: u64,
    pub validators: ProgressiveList<Validator>,
    pub balances: ProgressiveList<u64>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_participation: ProgressiveList<u8>,
    pub current_epoch_participation: ProgressiveList<u8>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: ProgressiveList<u64>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
    pub latest_block_hash: [u8; 32],
    pub next_withdrawal_index: u64,
    pub next_withdrawal_validator_index: u64,
    pub historical_summaries: SszList<HistoricalSummary, HISTORICAL_ROOTS_LIMIT>,
    pub deposit_requests_start_index: u64,
    pub deposit_balance_to_consume: u64,
    pub exit_balance_to_consume: u64,
    pub earliest_exit_epoch: u64,
    pub consolidation_balance_to_consume: u64,
    pub earliest_consolidation_epoch: u64,
    pub pending_deposits: ProgressiveList<PendingDeposit>,
    pub pending_partial_withdrawals: ProgressiveList<PendingPartialWithdrawal>,
    pub pending_consolidations: ProgressiveList<PendingConsolidation>,
    pub proposer_lookahead: SszVector<u64, PROPOSER_LOOKAHEAD_LEN>,
    pub builders: ProgressiveList<Builder>,
    pub next_withdrawal_builder_index: u64,
    pub execution_payload_availability: SszBitvector<SLOTS_PER_HISTORICAL_ROOT>,
    pub builder_pending_payments: SszVector<BuilderPendingPayment, BUILDER_PENDING_PAYMENTS_LEN>,
    pub builder_pending_withdrawals: ProgressiveList<BuilderPendingWithdrawal>,
    pub latest_execution_payload_bid: ExecutionPayloadBid,
    pub payload_expected_withdrawals: ProgressiveList<Withdrawal>,
    pub ptc_window: SszVector<SszVector<u64, PTC_SIZE>, PTC_WINDOW_LEN>,
}

// ── Data columns ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DataColumnSidecar {
    pub index: u64,
    pub column: ProgressiveList<SszVector<u8, { super::fulu::BYTES_PER_CELL }>>,
    pub kzg_proofs: ProgressiveList<[u8; 48]>,
    pub slot: u64,
    pub beacon_block_root: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PartialDataColumnSidecar {
    pub cells_present_bitmap: ProgressiveBitlist,
    pub partial_column: ProgressiveList<SszVector<u8, { super::fulu::BYTES_PER_CELL }>>,
    pub kzg_proofs: ProgressiveList<[u8; 48]>,
}

/// Unchanged from Fulu.
pub use super::fulu::PartialDataColumnPartsMetadata;

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PartialDataColumnGroupID {
    pub beacon_block_root: [u8; 32],
    pub slot: u64,
}

// ── Proposer preferences ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ProposerPreferences {
    pub dependent_root: [u8; 32],
    pub proposal_slot: u64,
    pub validator_index: u64,
    pub fee_recipient: [u8; 20],
    pub target_gas_limit: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedProposerPreferences {
    pub message: ProposerPreferences,
    pub signature: [u8; 96],
}

// ── Light client ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct LightClientHeader {
    pub beacon: BeaconBlockHeader,
    pub execution_block_hash: [u8; 32],
    pub execution_branch: SszVector<[u8; 32], EXECUTION_BRANCH_LEN>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct LightClientBootstrap {
    pub header: LightClientHeader,
    pub current_sync_committee: SyncCommittee,
    pub current_sync_committee_branch: SszVector<[u8; 32], CURRENT_SYNC_COMMITTEE_BRANCH_LEN>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct LightClientUpdate {
    pub attested_header: LightClientHeader,
    pub next_sync_committee: SyncCommittee,
    pub next_sync_committee_branch: SszVector<[u8; 32], NEXT_SYNC_COMMITTEE_BRANCH_LEN>,
    pub finalized_header: LightClientHeader,
    pub finality_branch: SszVector<[u8; 32], FINALITY_BRANCH_LEN>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct LightClientFinalityUpdate {
    pub attested_header: LightClientHeader,
    pub finalized_header: LightClientHeader,
    pub finality_branch: SszVector<[u8; 32], FINALITY_BRANCH_LEN>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct LightClientOptimisticUpdate {
    pub attested_header: LightClientHeader,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}
