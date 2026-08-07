//! Minimal preset type overrides.
//!
//! Only types whose SSZ layout differs between mainnet and minimal are defined here.
//! All other types are reused from the mainnet modules.

use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{
    ProgressiveBitlist, ProgressiveList, SszBitlist, SszBitvector, SszList, SszVector,
};

use super::phase0::{
    AttestationData, BeaconBlockHeader, Checkpoint, Deposit, Eth1Data, Fork, ProposerSlashing,
    SignedVoluntaryExit, Validator,
};

// ── Minimal preset constants ──

pub const MAX_COMMITTEES_PER_SLOT: usize = 4;
pub const MAX_VALIDATORS_PER_COMMITTEE: usize = 2048;
pub const SLOTS_PER_EPOCH: usize = 8;
pub const EPOCHS_PER_ETH1_VOTING_PERIOD: usize = 4;
pub const SLOTS_PER_HISTORICAL_ROOT: usize = 64;
pub const EPOCHS_PER_HISTORICAL_VECTOR: usize = 64;
pub const EPOCHS_PER_SLASHINGS_VECTOR: usize = 64;
pub const HISTORICAL_ROOTS_LIMIT: usize = 16_777_216;
pub const VALIDATOR_REGISTRY_LIMIT: usize = 1_099_511_627_776;
pub const JUSTIFICATION_BITS_LENGTH: usize = 4;
pub const MAX_PROPOSER_SLASHINGS: usize = 16;
pub const MAX_ATTESTER_SLASHINGS: usize = 2;
pub const MAX_ATTESTATIONS: usize = 128;
pub const MAX_DEPOSITS: usize = 16;
pub const MAX_VOLUNTARY_EXITS: usize = 16;
pub const SYNC_COMMITTEE_SIZE: usize = 32;
pub const SYNC_COMMITTEE_SUBNET_COUNT: usize = 4;
pub const MAX_BLS_TO_EXECUTION_CHANGES: usize = 16;
pub const MAX_WITHDRAWALS_PER_PAYLOAD: usize = 4;
pub const MAX_BLOB_COMMITMENTS_PER_BLOCK: usize = 4096;
pub const MAX_ATTESTER_SLASHINGS_ELECTRA: usize = 1;
pub const MAX_ATTESTATIONS_ELECTRA: usize = 8;
pub const PENDING_DEPOSITS_LIMIT: usize = 134_217_728;
pub const PENDING_PARTIAL_WITHDRAWALS_LIMIT: usize = 64;
pub const PENDING_CONSOLIDATIONS_LIMIT: usize = 64;
pub const PTC_SIZE: usize = 16;

// Derived constants
const ETH1_DATA_VOTES_LIMIT: usize = EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH; // 32
const PENDING_ATTESTATIONS_LIMIT: usize = MAX_ATTESTATIONS * SLOTS_PER_EPOCH; // 1024
const MAX_VALIDATORS_X_COMMITTEES: usize = MAX_VALIDATORS_PER_COMMITTEE * MAX_COMMITTEES_PER_SLOT; // 8192
const SYNC_SUBCOMMITTEE_SIZE: usize = SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT; // 8
const PROPOSER_LOOKAHEAD_LEN: usize = 2 * SLOTS_PER_EPOCH; // 16

// Execution constants (same as mainnet)
use super::bellatrix::{
    BYTES_PER_LOGS_BLOOM, MAX_BYTES_PER_TRANSACTION, MAX_EXTRA_DATA_BYTES,
    MAX_TRANSACTIONS_PER_PAYLOAD,
};

// Reused unchanged types
pub use super::capella::{
    BLSToExecutionChange, HistoricalSummary, SignedBLSToExecutionChange, Withdrawal,
};
pub use super::electra::{
    ConsolidationRequest, DepositRequest, PendingConsolidation, PendingDeposit,
    PendingPartialWithdrawal, WithdrawalRequest,
};
pub use super::gloas::{
    BuilderPendingPayment, BuilderPendingWithdrawal, ExecutionPayloadBid, PayloadAttestationData,
};

// ── Phase 0 types that differ ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HistoricalBatch {
    pub block_roots: SszVector<[u8; 32], SLOTS_PER_HISTORICAL_ROOT>,
    pub state_roots: SszVector<[u8; 32], SLOTS_PER_HISTORICAL_ROOT>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct IndexedAttestation {
    pub attesting_indices: SszList<u64, MAX_VALIDATORS_PER_COMMITTEE>,
    pub data: AttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PendingAttestation {
    pub aggregation_bits: SszBitlist<MAX_VALIDATORS_PER_COMMITTEE>,
    pub data: AttestationData,
    pub inclusion_delay: u64,
    pub proposer_index: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Attestation {
    pub aggregation_bits: SszBitlist<MAX_VALIDATORS_PER_COMMITTEE>,
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

// ── Phase 0 BeaconBlockBody/Block/State ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Phase0BeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, MAX_PROPOSER_SLASHINGS>,
    pub attester_slashings: SszList<AttesterSlashing, MAX_ATTESTER_SLASHINGS>,
    pub attestations: SszList<Attestation, MAX_ATTESTATIONS>,
    pub deposits: SszList<Deposit, MAX_DEPOSITS>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, MAX_VOLUNTARY_EXITS>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Phase0BeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: Phase0BeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Phase0SignedBeaconBlock {
    pub message: Phase0BeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Phase0BeaconState {
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
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_attestations: SszList<PendingAttestation, PENDING_ATTESTATIONS_LIMIT>,
    pub current_epoch_attestations: SszList<PendingAttestation, PENDING_ATTESTATIONS_LIMIT>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
}

// ── Altair types ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SyncAggregate {
    pub sync_committee_bits: SszBitvector<SYNC_COMMITTEE_SIZE>,
    pub sync_committee_signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SyncCommittee {
    pub pubkeys: SszVector<[u8; 48], SYNC_COMMITTEE_SIZE>,
    pub aggregate_pubkey: [u8; 48],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SyncCommitteeContribution {
    pub slot: u64,
    pub beacon_block_root: [u8; 32],
    pub subcommittee_index: u64,
    pub aggregation_bits: SszBitvector<SYNC_SUBCOMMITTEE_SIZE>,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ContributionAndProof {
    pub aggregator_index: u64,
    pub contribution: SyncCommitteeContribution,
    pub selection_proof: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedContributionAndProof {
    pub message: ContributionAndProof,
    pub signature: [u8; 96],
}

// Altair light client
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairLightClientHeader {
    pub beacon: BeaconBlockHeader,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairLightClientBootstrap {
    pub header: AltairLightClientHeader,
    pub current_sync_committee: SyncCommittee,
    pub current_sync_committee_branch: SszVector<[u8; 32], 5>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairLightClientUpdate {
    pub attested_header: AltairLightClientHeader,
    pub next_sync_committee: SyncCommittee,
    pub next_sync_committee_branch: SszVector<[u8; 32], 5>,
    pub finalized_header: AltairLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 6>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairLightClientFinalityUpdate {
    pub attested_header: AltairLightClientHeader,
    pub finalized_header: AltairLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 6>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairLightClientOptimisticUpdate {
    pub attested_header: AltairLightClientHeader,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

// Altair BeaconBlockBody/Block/State
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairBeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, MAX_PROPOSER_SLASHINGS>,
    pub attester_slashings: SszList<AttesterSlashing, MAX_ATTESTER_SLASHINGS>,
    pub attestations: SszList<Attestation, MAX_ATTESTATIONS>,
    pub deposits: SszList<Deposit, MAX_DEPOSITS>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, MAX_VOLUNTARY_EXITS>,
    pub sync_aggregate: SyncAggregate,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairBeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: AltairBeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairSignedBeaconBlock {
    pub message: AltairBeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct AltairBeaconState {
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
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub current_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
}

// ── Bellatrix types ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BellatrixExecutionPayload {
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
    pub transactions: SszList<SszList<u8, MAX_BYTES_PER_TRANSACTION>, MAX_TRANSACTIONS_PER_PAYLOAD>,
}

pub use super::bellatrix::ExecutionPayloadHeader as BellatrixExecutionPayloadHeader;
pub use super::bellatrix::PowBlock;

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BellatrixBeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, MAX_PROPOSER_SLASHINGS>,
    pub attester_slashings: SszList<AttesterSlashing, MAX_ATTESTER_SLASHINGS>,
    pub attestations: SszList<Attestation, MAX_ATTESTATIONS>,
    pub deposits: SszList<Deposit, MAX_DEPOSITS>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, MAX_VOLUNTARY_EXITS>,
    pub sync_aggregate: SyncAggregate,
    pub execution_payload: BellatrixExecutionPayload,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BellatrixBeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: BellatrixBeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BellatrixSignedBeaconBlock {
    pub message: BellatrixBeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BellatrixBeaconState {
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
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub current_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
    pub latest_execution_payload_header: BellatrixExecutionPayloadHeader,
}

// ── Capella types ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaExecutionPayload {
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
    pub transactions: SszList<SszList<u8, MAX_BYTES_PER_TRANSACTION>, MAX_TRANSACTIONS_PER_PAYLOAD>,
    pub withdrawals: SszList<Withdrawal, MAX_WITHDRAWALS_PER_PAYLOAD>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaExecutionPayloadHeader {
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
    pub transactions_root: [u8; 32],
    pub withdrawals_root: [u8; 32],
}

// Capella light client
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaLightClientHeader {
    pub beacon: BeaconBlockHeader,
    pub execution: CapellaExecutionPayloadHeader,
    pub execution_branch: SszVector<[u8; 32], 4>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaLightClientBootstrap {
    pub header: CapellaLightClientHeader,
    pub current_sync_committee: SyncCommittee,
    pub current_sync_committee_branch: SszVector<[u8; 32], 5>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaLightClientUpdate {
    pub attested_header: CapellaLightClientHeader,
    pub next_sync_committee: SyncCommittee,
    pub next_sync_committee_branch: SszVector<[u8; 32], 5>,
    pub finalized_header: CapellaLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 6>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaLightClientFinalityUpdate {
    pub attested_header: CapellaLightClientHeader,
    pub finalized_header: CapellaLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 6>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaLightClientOptimisticUpdate {
    pub attested_header: CapellaLightClientHeader,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaBeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, MAX_PROPOSER_SLASHINGS>,
    pub attester_slashings: SszList<AttesterSlashing, MAX_ATTESTER_SLASHINGS>,
    pub attestations: SszList<Attestation, MAX_ATTESTATIONS>,
    pub deposits: SszList<Deposit, MAX_DEPOSITS>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, MAX_VOLUNTARY_EXITS>,
    pub sync_aggregate: SyncAggregate,
    pub execution_payload: CapellaExecutionPayload,
    pub bls_to_execution_changes: SszList<SignedBLSToExecutionChange, MAX_BLS_TO_EXECUTION_CHANGES>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaBeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: CapellaBeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaSignedBeaconBlock {
    pub message: CapellaBeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct CapellaBeaconState {
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
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub current_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
    pub latest_execution_payload_header: CapellaExecutionPayloadHeader,
    pub next_withdrawal_index: u64,
    pub next_withdrawal_validator_index: u64,
    pub historical_summaries: SszList<HistoricalSummary, HISTORICAL_ROOTS_LIMIT>,
}

// ── Deneb types ──
// ExecutionPayload/Header add blob_gas_used + excess_blob_gas;
// BeaconBlockBody adds blob_kzg_commitments.

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebExecutionPayload {
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
    pub transactions: SszList<SszList<u8, MAX_BYTES_PER_TRANSACTION>, MAX_TRANSACTIONS_PER_PAYLOAD>,
    pub withdrawals: SszList<Withdrawal, MAX_WITHDRAWALS_PER_PAYLOAD>,
    pub blob_gas_used: u64,
    pub excess_blob_gas: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebExecutionPayloadHeader {
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
    pub transactions_root: [u8; 32],
    pub withdrawals_root: [u8; 32],
    pub blob_gas_used: u64,
    pub excess_blob_gas: u64,
}

// BlobSidecar reuses mainnet (no preset-dependent fields)
pub use super::deneb::BlobIdentifier;
pub use super::deneb::BlobSidecar;

// Deneb light client (same branch lengths as capella, but with deneb exec header)
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebLightClientHeader {
    pub beacon: BeaconBlockHeader,
    pub execution: DenebExecutionPayloadHeader,
    pub execution_branch: SszVector<[u8; 32], 4>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebLightClientBootstrap {
    pub header: DenebLightClientHeader,
    pub current_sync_committee: SyncCommittee,
    pub current_sync_committee_branch: SszVector<[u8; 32], 5>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebLightClientUpdate {
    pub attested_header: DenebLightClientHeader,
    pub next_sync_committee: SyncCommittee,
    pub next_sync_committee_branch: SszVector<[u8; 32], 5>,
    pub finalized_header: DenebLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 6>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebLightClientFinalityUpdate {
    pub attested_header: DenebLightClientHeader,
    pub finalized_header: DenebLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 6>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebLightClientOptimisticUpdate {
    pub attested_header: DenebLightClientHeader,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebBeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, MAX_PROPOSER_SLASHINGS>,
    pub attester_slashings: SszList<AttesterSlashing, MAX_ATTESTER_SLASHINGS>,
    pub attestations: SszList<Attestation, MAX_ATTESTATIONS>,
    pub deposits: SszList<Deposit, MAX_DEPOSITS>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, MAX_VOLUNTARY_EXITS>,
    pub sync_aggregate: SyncAggregate,
    pub execution_payload: DenebExecutionPayload,
    pub bls_to_execution_changes: SszList<SignedBLSToExecutionChange, MAX_BLS_TO_EXECUTION_CHANGES>,
    pub blob_kzg_commitments: SszList<[u8; 48], MAX_BLOB_COMMITMENTS_PER_BLOCK>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebBeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: DenebBeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebSignedBeaconBlock {
    pub message: DenebBeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DenebBeaconState {
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
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub current_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
    pub latest_execution_payload_header: DenebExecutionPayloadHeader,
    pub next_withdrawal_index: u64,
    pub next_withdrawal_validator_index: u64,
    pub historical_summaries: SszList<HistoricalSummary, HISTORICAL_ROOTS_LIMIT>,
}

// ── Electra types ──
// Attestation changes: committee_bits, wider bitlists; new ExecutionRequests; BeaconState additions

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraAttestation {
    pub aggregation_bits: SszBitlist<MAX_VALIDATORS_X_COMMITTEES>,
    pub data: AttestationData,
    pub signature: [u8; 96],
    pub committee_bits: SszBitvector<MAX_COMMITTEES_PER_SLOT>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraIndexedAttestation {
    pub attesting_indices: SszList<u64, MAX_VALIDATORS_X_COMMITTEES>,
    pub data: AttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraAttesterSlashing {
    pub attestation_1: ElectraIndexedAttestation,
    pub attestation_2: ElectraIndexedAttestation,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraAggregateAndProof {
    pub aggregator_index: u64,
    pub aggregate: ElectraAttestation,
    pub selection_proof: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraSignedAggregateAndProof {
    pub message: ElectraAggregateAndProof,
    pub signature: [u8; 96],
}

pub use super::electra::{
    ExecutionRequests, SingleAttestation, MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD,
    MAX_DEPOSIT_REQUESTS_PER_PAYLOAD, MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD,
};

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraBeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, MAX_PROPOSER_SLASHINGS>,
    pub attester_slashings: SszList<ElectraAttesterSlashing, MAX_ATTESTER_SLASHINGS_ELECTRA>,
    pub attestations: SszList<ElectraAttestation, MAX_ATTESTATIONS_ELECTRA>,
    pub deposits: SszList<Deposit, MAX_DEPOSITS>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, MAX_VOLUNTARY_EXITS>,
    pub sync_aggregate: SyncAggregate,
    pub execution_payload: DenebExecutionPayload,
    pub bls_to_execution_changes: SszList<SignedBLSToExecutionChange, MAX_BLS_TO_EXECUTION_CHANGES>,
    pub blob_kzg_commitments: SszList<[u8; 48], MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub execution_requests: ExecutionRequests,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraBeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: ElectraBeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraSignedBeaconBlock {
    pub message: ElectraBeaconBlock,
    pub signature: [u8; 96],
}

// Electra light client — updated branch lengths for larger BeaconState
// floorlog2(169) = 7, floorlog2(86) = 6, floorlog2(87) = 6
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraLightClientHeader {
    pub beacon: BeaconBlockHeader,
    pub execution: DenebExecutionPayloadHeader,
    pub execution_branch: SszVector<[u8; 32], 4>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraLightClientBootstrap {
    pub header: ElectraLightClientHeader,
    pub current_sync_committee: SyncCommittee,
    pub current_sync_committee_branch: SszVector<[u8; 32], 6>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraLightClientUpdate {
    pub attested_header: ElectraLightClientHeader,
    pub next_sync_committee: SyncCommittee,
    pub next_sync_committee_branch: SszVector<[u8; 32], 6>,
    pub finalized_header: ElectraLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 7>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraLightClientFinalityUpdate {
    pub attested_header: ElectraLightClientHeader,
    pub finalized_header: ElectraLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], 7>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraLightClientOptimisticUpdate {
    pub attested_header: ElectraLightClientHeader,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ElectraBeaconState {
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
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub current_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
    pub latest_execution_payload_header: DenebExecutionPayloadHeader,
    pub next_withdrawal_index: u64,
    pub next_withdrawal_validator_index: u64,
    pub historical_summaries: SszList<HistoricalSummary, HISTORICAL_ROOTS_LIMIT>,
    pub deposit_requests_start_index: u64,
    pub deposit_balance_to_consume: u64,
    pub exit_balance_to_consume: u64,
    pub earliest_exit_epoch: u64,
    pub consolidation_balance_to_consume: u64,
    pub earliest_consolidation_epoch: u64,
    pub pending_deposits: SszList<PendingDeposit, PENDING_DEPOSITS_LIMIT>,
    pub pending_partial_withdrawals:
        SszList<PendingPartialWithdrawal, PENDING_PARTIAL_WITHDRAWALS_LIMIT>,
    pub pending_consolidations: SszList<PendingConsolidation, PENDING_CONSOLIDATIONS_LIMIT>,
}

// ── Fulu types ──
// Reuse fulu DAS types (preset-independent), add fulu BeaconState with proposer_lookahead
pub use super::fulu::{DataColumnSidecar, DataColumnsByRootIdentifier, MatrixEntry};

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct FuluBeaconState {
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
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    pub balances: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub randao_mixes: SszVector<[u8; 32], EPOCHS_PER_HISTORICAL_VECTOR>,
    pub slashings: SszVector<u64, EPOCHS_PER_SLASHINGS_VECTOR>,
    pub previous_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub current_epoch_participation: SszList<u8, VALIDATOR_REGISTRY_LIMIT>,
    pub justification_bits: SszBitvector<JUSTIFICATION_BITS_LENGTH>,
    pub previous_justified_checkpoint: Checkpoint,
    pub current_justified_checkpoint: Checkpoint,
    pub finalized_checkpoint: Checkpoint,
    pub inactivity_scores: SszList<u64, VALIDATOR_REGISTRY_LIMIT>,
    pub current_sync_committee: SyncCommittee,
    pub next_sync_committee: SyncCommittee,
    pub latest_execution_payload_header: DenebExecutionPayloadHeader,
    pub next_withdrawal_index: u64,
    pub next_withdrawal_validator_index: u64,
    pub historical_summaries: SszList<HistoricalSummary, HISTORICAL_ROOTS_LIMIT>,
    pub deposit_requests_start_index: u64,
    pub deposit_balance_to_consume: u64,
    pub exit_balance_to_consume: u64,
    pub earliest_exit_epoch: u64,
    pub consolidation_balance_to_consume: u64,
    pub earliest_consolidation_epoch: u64,
    pub pending_deposits: SszList<PendingDeposit, PENDING_DEPOSITS_LIMIT>,
    pub pending_partial_withdrawals:
        SszList<PendingPartialWithdrawal, PENDING_PARTIAL_WITHDRAWALS_LIMIT>,
    pub pending_consolidations: SszList<PendingConsolidation, PENDING_CONSOLIDATIONS_LIMIT>,
    pub proposer_lookahead: SszVector<u64, PROPOSER_LOOKAHEAD_LEN>,
}

// ── Gloas types ──
//
// Gloas adopts EIP-7688, so most bounded lists became `ProgressiveList`. Types
// whose bounds all became progressive are preset-independent and reused from
// the mainnet module; only the ones still tied to a preset value are redefined.

pub use super::gloas::{
    AttesterSlashing as GloasAttesterSlashing, Builder, BuilderDepositRequest, BuilderExitRequest,
    DataColumnSidecar as GloasDataColumnSidecar, ExecutionPayload as GloasExecutionPayload,
    ExecutionPayloadEnvelope as GloasExecutionPayloadEnvelope,
    ExecutionRequests as GloasExecutionRequests, IndexedAttestation as GloasIndexedAttestation,
    PartialDataColumnGroupID, PartialDataColumnSidecar, ProposerPreferences,
    SignedExecutionPayloadEnvelope as GloasSignedExecutionPayloadEnvelope,
    SignedProposerPreferences,
};
pub use super::gloas::{PayloadAttestationMessage, SignedExecutionPayloadBid};

// Light client branch lengths are preset-independent, so Gloas and Heze reuse
// the mainnet values along with the gindex derivations documented there.
use super::gloas::{
    CURRENT_SYNC_COMMITTEE_BRANCH_LEN, EXECUTION_BRANCH_LEN, FINALITY_BRANCH_LEN,
    NEXT_SYNC_COMMITTEE_BRANCH_LEN,
};

const GLOAS_PROPOSER_LOOKAHEAD_LEN: usize =
    (super::gloas::MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH;
const GLOAS_PTC_WINDOW_LEN: usize = (2 + super::gloas::MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH;
const GLOAS_BUILDER_PENDING_PAYMENTS_LEN: usize = 2 * SLOTS_PER_EPOCH;

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct GloasAttestation {
    pub aggregation_bits: ProgressiveBitlist,
    pub data: AttestationData,
    pub signature: [u8; 96],
    pub committee_bits: SszBitvector<MAX_COMMITTEES_PER_SLOT>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasAggregateAndProof {
    pub aggregator_index: u64,
    pub aggregate: GloasAttestation,
    pub selection_proof: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasSignedAggregateAndProof {
    pub message: GloasAggregateAndProof,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct GloasPayloadAttestation {
    pub aggregation_bits: SszBitvector<PTC_SIZE>,
    pub data: PayloadAttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct GloasIndexedPayloadAttestation {
    pub attesting_indices: SszList<u64, PTC_SIZE>,
    pub data: PayloadAttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct GloasBeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: ProgressiveList<ProposerSlashing>,
    pub attester_slashings: ProgressiveList<GloasAttesterSlashing>,
    pub attestations: ProgressiveList<GloasAttestation>,
    pub deposits: ProgressiveList<Deposit>,
    pub voluntary_exits: ProgressiveList<SignedVoluntaryExit>,
    pub sync_aggregate: SyncAggregate,
    pub bls_to_execution_changes: ProgressiveList<SignedBLSToExecutionChange>,
    pub signed_execution_payload_bid: SignedExecutionPayloadBid,
    pub payload_attestations: ProgressiveList<GloasPayloadAttestation>,
    pub parent_execution_requests: GloasExecutionRequests,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasBeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: GloasBeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasSignedBeaconBlock {
    pub message: GloasBeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct GloasBeaconState {
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
    pub proposer_lookahead: SszVector<u64, GLOAS_PROPOSER_LOOKAHEAD_LEN>,
    pub builders: ProgressiveList<Builder>,
    pub next_withdrawal_builder_index: u64,
    pub execution_payload_availability: SszBitvector<SLOTS_PER_HISTORICAL_ROOT>,
    pub builder_pending_payments:
        SszVector<BuilderPendingPayment, GLOAS_BUILDER_PENDING_PAYMENTS_LEN>,
    pub builder_pending_withdrawals: ProgressiveList<BuilderPendingWithdrawal>,
    pub latest_execution_payload_bid: ExecutionPayloadBid,
    pub payload_expected_withdrawals: ProgressiveList<Withdrawal>,
    pub ptc_window: SszVector<SszVector<u64, PTC_SIZE>, GLOAS_PTC_WINDOW_LEN>,
}

// ── Gloas light client ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasLightClientHeader {
    pub beacon: BeaconBlockHeader,
    pub execution_block_hash: [u8; 32],
    pub execution_branch: SszVector<[u8; 32], EXECUTION_BRANCH_LEN>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasLightClientBootstrap {
    pub header: GloasLightClientHeader,
    pub current_sync_committee: SyncCommittee,
    pub current_sync_committee_branch: SszVector<[u8; 32], CURRENT_SYNC_COMMITTEE_BRANCH_LEN>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasLightClientUpdate {
    pub attested_header: GloasLightClientHeader,
    pub next_sync_committee: SyncCommittee,
    pub next_sync_committee_branch: SszVector<[u8; 32], NEXT_SYNC_COMMITTEE_BRANCH_LEN>,
    pub finalized_header: GloasLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], FINALITY_BRANCH_LEN>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasLightClientFinalityUpdate {
    pub attested_header: GloasLightClientHeader,
    pub finalized_header: GloasLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], FINALITY_BRANCH_LEN>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct GloasLightClientOptimisticUpdate {
    pub attested_header: GloasLightClientHeader,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

// ── Heze types ──
//
// Preset-independent Heze containers are reused; only those tied to a preset
// value (via `SyncAggregate`, `SyncCommittee`, or a vector length) are redefined.

pub use super::heze::{
    ExecutionPayloadBid as HezeExecutionPayloadBid, InclusionList,
    SignedExecutionPayloadBid as HezeSignedExecutionPayloadBid, SignedInclusionList,
};

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct HezeBeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: ProgressiveList<ProposerSlashing>,
    pub attester_slashings: ProgressiveList<GloasAttesterSlashing>,
    pub attestations: ProgressiveList<GloasAttestation>,
    pub deposits: ProgressiveList<Deposit>,
    pub voluntary_exits: ProgressiveList<SignedVoluntaryExit>,
    pub sync_aggregate: SyncAggregate,
    pub bls_to_execution_changes: ProgressiveList<SignedBLSToExecutionChange>,
    pub signed_execution_payload_bid: HezeSignedExecutionPayloadBid,
    pub payload_attestations: ProgressiveList<GloasPayloadAttestation>,
    pub parent_execution_requests: GloasExecutionRequests,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HezeBeaconBlock {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body: HezeBeaconBlockBody,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HezeSignedBeaconBlock {
    pub message: HezeBeaconBlock,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
pub struct HezeBeaconState {
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
    pub proposer_lookahead: SszVector<u64, GLOAS_PROPOSER_LOOKAHEAD_LEN>,
    pub builders: ProgressiveList<Builder>,
    pub next_withdrawal_builder_index: u64,
    pub execution_payload_availability: SszBitvector<SLOTS_PER_HISTORICAL_ROOT>,
    pub builder_pending_payments:
        SszVector<BuilderPendingPayment, GLOAS_BUILDER_PENDING_PAYMENTS_LEN>,
    pub builder_pending_withdrawals: ProgressiveList<BuilderPendingWithdrawal>,
    pub latest_execution_payload_bid: HezeExecutionPayloadBid,
    pub payload_expected_withdrawals: ProgressiveList<Withdrawal>,
    pub ptc_window: SszVector<SszVector<u64, PTC_SIZE>, GLOAS_PTC_WINDOW_LEN>,
}

// ── Heze light client ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HezeLightClientHeader {
    pub beacon: BeaconBlockHeader,
    pub execution_block_hash: [u8; 32],
    pub execution_branch: SszVector<[u8; 32], EXECUTION_BRANCH_LEN>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HezeLightClientBootstrap {
    pub header: HezeLightClientHeader,
    pub current_sync_committee: SyncCommittee,
    pub current_sync_committee_branch: SszVector<[u8; 32], CURRENT_SYNC_COMMITTEE_BRANCH_LEN>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HezeLightClientUpdate {
    pub attested_header: HezeLightClientHeader,
    pub next_sync_committee: SyncCommittee,
    pub next_sync_committee_branch: SszVector<[u8; 32], NEXT_SYNC_COMMITTEE_BRANCH_LEN>,
    pub finalized_header: HezeLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], FINALITY_BRANCH_LEN>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HezeLightClientFinalityUpdate {
    pub attested_header: HezeLightClientHeader,
    pub finalized_header: HezeLightClientHeader,
    pub finality_branch: SszVector<[u8; 32], FINALITY_BRANCH_LEN>,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct HezeLightClientOptimisticUpdate {
    pub attested_header: HezeLightClientHeader,
    pub sync_aggregate: SyncAggregate,
    pub signature_slot: u64,
}
