use ssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use ssz_types::{SszBitvector, SszList, SszVector};

use super::phase0::{
    Attestation, AttesterSlashing, BeaconBlockHeader, Checkpoint, Deposit, Eth1Data, Fork,
    ProposerSlashing, SignedVoluntaryExit, Validator, EPOCHS_PER_ETH1_VOTING_PERIOD,
    EPOCHS_PER_HISTORICAL_VECTOR, EPOCHS_PER_SLASHINGS_VECTOR, HISTORICAL_ROOTS_LIMIT,
    JUSTIFICATION_BITS_LENGTH, MAX_ATTESTATIONS, MAX_ATTESTER_SLASHINGS, MAX_DEPOSITS,
    MAX_PROPOSER_SLASHINGS, MAX_VOLUNTARY_EXITS, SLOTS_PER_EPOCH, SLOTS_PER_HISTORICAL_ROOT,
    VALIDATOR_REGISTRY_LIMIT,
};

pub const SYNC_COMMITTEE_SIZE: usize = 512;
pub const SYNC_COMMITTEE_SUBNET_COUNT: usize = 4;

const ETH1_DATA_VOTES_LIMIT: usize = EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH;

// ── New types ──

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
pub struct SyncCommitteeMessage {
    pub slot: u64,
    pub beacon_block_root: [u8; 32],
    pub validator_index: u64,
    pub signature: [u8; 96],
}

// SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT = 128
const SYNC_SUBCOMMITTEE_SIZE: usize = SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT;

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

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct SyncAggregatorSelectionData {
    pub slot: u64,
    pub subcommittee_index: u64,
}

// ── Light client types ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct LightClientHeader {
    pub beacon: BeaconBlockHeader,
}

// floorlog2(105) = 6
const FINALITY_BRANCH_LEN: usize = 6;
// floorlog2(54) = 5
const CURRENT_SYNC_COMMITTEE_BRANCH_LEN: usize = 5;
// floorlog2(55) = 5
const NEXT_SYNC_COMMITTEE_BRANCH_LEN: usize = 5;

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

// ── Modified types (altair versions) ──

#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct BeaconBlockBody {
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

// ParticipationFlags = uint8
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
}
