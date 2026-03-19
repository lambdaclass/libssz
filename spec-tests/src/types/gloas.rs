use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{SszBitvector, SszList, SszVector};

use super::altair::{SyncAggregate, SyncCommittee};
use super::capella::{
    HistoricalSummary, SignedBLSToExecutionChange, Withdrawal, MAX_BLS_TO_EXECUTION_CHANGES,
    MAX_WITHDRAWALS_PER_PAYLOAD,
};
use super::deneb::MAX_BLOB_COMMITMENTS_PER_BLOCK;
use super::electra::{
    Attestation, AttesterSlashing, ExecutionPayload, ExecutionPayloadHeader, ExecutionRequests,
    PendingConsolidation, PendingDeposit, PendingPartialWithdrawal, MAX_ATTESTATIONS_ELECTRA,
    MAX_ATTESTER_SLASHINGS_ELECTRA, PENDING_CONSOLIDATIONS_LIMIT, PENDING_DEPOSITS_LIMIT,
    PENDING_PARTIAL_WITHDRAWALS_LIMIT,
};
use super::phase0::{
    BeaconBlockHeader, Checkpoint, Deposit, Eth1Data, Fork, ProposerSlashing, SignedVoluntaryExit,
    Validator, EPOCHS_PER_ETH1_VOTING_PERIOD, EPOCHS_PER_HISTORICAL_VECTOR,
    EPOCHS_PER_SLASHINGS_VECTOR, HISTORICAL_ROOTS_LIMIT, JUSTIFICATION_BITS_LENGTH, MAX_DEPOSITS,
    MAX_PROPOSER_SLASHINGS, MAX_VOLUNTARY_EXITS, SLOTS_PER_EPOCH, SLOTS_PER_HISTORICAL_ROOT,
    VALIDATOR_REGISTRY_LIMIT,
};

pub const PTC_SIZE: usize = 512;
pub const MAX_PAYLOAD_ATTESTATIONS: usize = 4;
pub const BUILDER_PENDING_WITHDRAWALS_LIMIT: usize = 1_048_576;

const ETH1_DATA_VOTES_LIMIT: usize = EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH;
const PROPOSER_LOOKAHEAD_LEN: usize = 64; // (1+1)*32

// ── New types ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BuilderPendingWithdrawal {
    pub fee_recipient: [u8; 20],
    pub amount: u64,
    pub builder_index: u64,
    pub withdrawable_epoch: u64,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BuilderPendingPayment {
    pub weight: u64,
    pub withdrawal: BuilderPendingWithdrawal,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct PayloadAttestationData {
    pub beacon_block_root: [u8; 32],
    pub slot: u64,
    pub payload_present: bool,
    pub blob_data_available: bool,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
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
pub struct IndexedPayloadAttestation {
    pub attesting_indices: SszList<u64, PTC_SIZE>,
    pub data: PayloadAttestationData,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
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
    pub blob_kzg_commitments_root: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedExecutionPayloadBid {
    pub message: ExecutionPayloadBid,
    pub signature: [u8; 96],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ExecutionPayloadEnvelope {
    pub payload: ExecutionPayload,
    pub execution_requests: ExecutionRequests,
    pub builder_index: u64,
    pub beacon_block_root: [u8; 32],
    pub slot: u64,
    pub blob_kzg_commitments: SszList<[u8; 48], MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub state_root: [u8; 32],
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedExecutionPayloadEnvelope {
    pub message: ExecutionPayloadEnvelope,
    pub signature: [u8; 96],
}

// Gloas DataColumnSidecar — modified from fulu
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct DataColumnSidecar {
    pub index: u64,
    pub column:
        SszList<SszVector<u8, { super::fulu::BYTES_PER_CELL }>, MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub kzg_commitments: SszList<[u8; 48], MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub kzg_proofs: SszList<[u8; 48], MAX_BLOB_COMMITMENTS_PER_BLOCK>,
    pub slot: u64,
    pub beacon_block_root: [u8; 32],
}

// ForkChoiceNode: PayloadStatus = uint8
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct ForkChoiceNode {
    pub root: [u8; 32],
    pub payload_status: u8,
}

// ── Modified types ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BeaconBlockBody {
    pub randao_reveal: [u8; 96],
    pub eth1_data: Eth1Data,
    pub graffiti: [u8; 32],
    pub proposer_slashings: SszList<ProposerSlashing, MAX_PROPOSER_SLASHINGS>,
    pub attester_slashings: SszList<AttesterSlashing, MAX_ATTESTER_SLASHINGS_ELECTRA>,
    pub attestations: SszList<Attestation, MAX_ATTESTATIONS_ELECTRA>,
    pub deposits: SszList<Deposit, MAX_DEPOSITS>,
    pub voluntary_exits: SszList<SignedVoluntaryExit, MAX_VOLUNTARY_EXITS>,
    pub sync_aggregate: SyncAggregate,
    pub bls_to_execution_changes: SszList<SignedBLSToExecutionChange, MAX_BLS_TO_EXECUTION_CHANGES>,
    pub signed_execution_payload_bid: SignedExecutionPayloadBid,
    pub payload_attestations: SszList<PayloadAttestation, MAX_PAYLOAD_ATTESTATIONS>,
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
    pub latest_execution_payload_bid: ExecutionPayloadBid,
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
    pub execution_payload_availability: SszBitvector<SLOTS_PER_HISTORICAL_ROOT>,
    pub builder_pending_payments: SszVector<BuilderPendingPayment, { 2 * SLOTS_PER_EPOCH }>,
    pub builder_pending_withdrawals:
        SszList<BuilderPendingWithdrawal, BUILDER_PENDING_WITHDRAWALS_LIMIT>,
    pub latest_block_hash: [u8; 32],
    pub latest_withdrawals_root: [u8; 32],
}
