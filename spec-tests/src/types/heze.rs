//! Heze types as of consensus-specs v1.7.0-alpha.13.
//!
//! Heze builds on Gloas and reintroduces inclusion lists. Only the containers
//! that actually change are defined here; everything else is reused from Gloas
//! and earlier forks.

use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{ProgressiveList, SszBitvector, SszList, SszVector};

use super::altair::{SyncAggregate, SyncCommittee};
use super::capella::{HistoricalSummary, SignedBLSToExecutionChange, Withdrawal};
use super::electra::{PendingConsolidation, PendingDeposit, PendingPartialWithdrawal};
use super::gloas::{
    Attestation, AttesterSlashing, Builder, BuilderPendingPayment, BuilderPendingWithdrawal,
    ExecutionRequests, PayloadAttestation, ProgressiveByteList, CURRENT_SYNC_COMMITTEE_BRANCH_LEN,
    EXECUTION_BRANCH_LEN, FINALITY_BRANCH_LEN, MIN_SEED_LOOKAHEAD, NEXT_SYNC_COMMITTEE_BRANCH_LEN,
    PTC_SIZE,
};
use super::phase0::{
    BeaconBlockHeader, Checkpoint, Deposit, Eth1Data, Fork, ProposerSlashing, SignedVoluntaryExit,
    Validator, EPOCHS_PER_ETH1_VOTING_PERIOD, EPOCHS_PER_HISTORICAL_VECTOR,
    EPOCHS_PER_SLASHINGS_VECTOR, HISTORICAL_ROOTS_LIMIT, JUSTIFICATION_BITS_LENGTH,
    SLOTS_PER_EPOCH, SLOTS_PER_HISTORICAL_ROOT,
};

pub const INCLUSION_LIST_COMMITTEE_SIZE: usize = 16;

const ETH1_DATA_VOTES_LIMIT: usize = EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH;
const PROPOSER_LOOKAHEAD_LEN: usize = (MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH;
const PTC_WINDOW_LEN: usize = (2 + MIN_SEED_LOOKAHEAD) * SLOTS_PER_EPOCH;
const BUILDER_PENDING_PAYMENTS_LEN: usize = 2 * SLOTS_PER_EPOCH;

// ── Inclusion lists ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct InclusionList {
    pub slot: u64,
    pub validator_index: u64,
    pub inclusion_list_committee_root: [u8; 32],
    pub transactions: ProgressiveList<ProgressiveByteList>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedInclusionList {
    pub message: InclusionList,
    pub signature: [u8; 96],
}

// ── Execution payload bid ──

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
    pub inclusion_list_bits: SszBitvector<INCLUSION_LIST_COMMITTEE_SIZE>,
}

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SignedExecutionPayloadBid {
    pub message: ExecutionPayloadBid,
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

// ── Light client ──
//
// Heze keeps the Gloas `BeaconBlockBody` and `BeaconState` field layout, so the
// branch lengths are unchanged.

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
