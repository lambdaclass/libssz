use spec_tests::loader::{self, Archive};
use ssz::{SszDecode, SszEncode};
use ssz_merkle::HashTreeRoot;

fn check_roundtrip_root<T: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug>(
    ssz: &[u8],
    expected_root: &[u8; 32],
    case_name: &str,
) {
    let decoded =
        T::from_ssz_bytes(ssz).unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
    let reencoded = decoded.to_ssz();
    assert_eq!(reencoded, ssz, "{case_name}: roundtrip mismatch");
    let root = decoded.hash_tree_root();
    assert_eq!(root, *expected_root, "{case_name}: hash tree root mismatch");
}

fn run_ssz_static_type<T: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug>(
    archive: Archive,
    fork: &str,
    type_name: &str,
) {
    let cases = loader::ssz_static_cases(archive, fork, type_name);
    assert!(!cases.is_empty(), "{fork}/{type_name}: no test cases found");
    for (case_path, case_name) in &cases {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let root_file = case_path.join("roots.yaml");
        let expected_root = loader::parse_root(&root_file);
        check_roundtrip_root::<T>(
            &ssz,
            &expected_root,
            &format!("{fork}/{type_name}/{case_name}"),
        );
    }
}

// ── Phase 0 mainnet ──

macro_rules! phase0_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "phase0", $type_name);
        }
    };
}

use spec_tests::types::phase0::*;

phase0_mainnet_test!(
    phase0_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    AggregateAndProof
);
phase0_mainnet_test!(phase0_mainnet_attestation, "Attestation", Attestation);
phase0_mainnet_test!(
    phase0_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
phase0_mainnet_test!(
    phase0_mainnet_attester_slashing,
    "AttesterSlashing",
    AttesterSlashing
);
phase0_mainnet_test!(phase0_mainnet_beacon_block, "BeaconBlock", BeaconBlock);
phase0_mainnet_test!(
    phase0_mainnet_beacon_block_body,
    "BeaconBlockBody",
    BeaconBlockBody
);
phase0_mainnet_test!(
    phase0_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
phase0_mainnet_test!(phase0_mainnet_beacon_state, "BeaconState", BeaconState);
phase0_mainnet_test!(phase0_mainnet_checkpoint, "Checkpoint", Checkpoint);
phase0_mainnet_test!(phase0_mainnet_deposit, "Deposit", Deposit);
phase0_mainnet_test!(phase0_mainnet_deposit_data, "DepositData", DepositData);
phase0_mainnet_test!(
    phase0_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
phase0_mainnet_test!(phase0_mainnet_eth1_block, "Eth1Block", Eth1Block);
phase0_mainnet_test!(phase0_mainnet_eth1_data, "Eth1Data", Eth1Data);
phase0_mainnet_test!(phase0_mainnet_fork, "Fork", Fork);
phase0_mainnet_test!(phase0_mainnet_fork_data, "ForkData", ForkData);
phase0_mainnet_test!(
    phase0_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
phase0_mainnet_test!(
    phase0_mainnet_indexed_attestation,
    "IndexedAttestation",
    IndexedAttestation
);
phase0_mainnet_test!(
    phase0_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
phase0_mainnet_test!(
    phase0_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
phase0_mainnet_test!(
    phase0_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    SignedAggregateAndProof
);
phase0_mainnet_test!(
    phase0_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    SignedBeaconBlock
);
phase0_mainnet_test!(
    phase0_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
phase0_mainnet_test!(
    phase0_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
phase0_mainnet_test!(phase0_mainnet_signing_data, "SigningData", SigningData);
phase0_mainnet_test!(phase0_mainnet_validator, "Validator", Validator);
phase0_mainnet_test!(
    phase0_mainnet_voluntary_exit,
    "VoluntaryExit",
    VoluntaryExit
);

// ── Altair mainnet ──

macro_rules! altair_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "altair", $type_name);
        }
    };
}

use spec_tests::types::altair;

// Unchanged from phase0
altair_mainnet_test!(
    altair_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    AggregateAndProof
);
altair_mainnet_test!(altair_mainnet_attestation, "Attestation", Attestation);
altair_mainnet_test!(
    altair_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
altair_mainnet_test!(
    altair_mainnet_attester_slashing,
    "AttesterSlashing",
    AttesterSlashing
);
altair_mainnet_test!(
    altair_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
altair_mainnet_test!(altair_mainnet_checkpoint, "Checkpoint", Checkpoint);
altair_mainnet_test!(altair_mainnet_deposit, "Deposit", Deposit);
altair_mainnet_test!(altair_mainnet_deposit_data, "DepositData", DepositData);
altair_mainnet_test!(
    altair_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
altair_mainnet_test!(altair_mainnet_eth1_block, "Eth1Block", Eth1Block);
altair_mainnet_test!(altair_mainnet_eth1_data, "Eth1Data", Eth1Data);
altair_mainnet_test!(altair_mainnet_fork, "Fork", Fork);
altair_mainnet_test!(altair_mainnet_fork_data, "ForkData", ForkData);
altair_mainnet_test!(
    altair_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
altair_mainnet_test!(
    altair_mainnet_indexed_attestation,
    "IndexedAttestation",
    IndexedAttestation
);
altair_mainnet_test!(
    altair_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
altair_mainnet_test!(
    altair_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
altair_mainnet_test!(
    altair_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    SignedAggregateAndProof
);
altair_mainnet_test!(
    altair_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
altair_mainnet_test!(
    altair_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
altair_mainnet_test!(altair_mainnet_signing_data, "SigningData", SigningData);
altair_mainnet_test!(altair_mainnet_validator, "Validator", Validator);
altair_mainnet_test!(
    altair_mainnet_voluntary_exit,
    "VoluntaryExit",
    VoluntaryExit
);

// New in altair
altair_mainnet_test!(
    altair_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
altair_mainnet_test!(
    altair_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
altair_mainnet_test!(
    altair_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
altair_mainnet_test!(
    altair_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
altair_mainnet_test!(
    altair_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
altair_mainnet_test!(
    altair_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
altair_mainnet_test!(
    altair_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);

// Light client types
altair_mainnet_test!(
    altair_mainnet_light_client_header,
    "LightClientHeader",
    altair::LightClientHeader
);
altair_mainnet_test!(
    altair_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    altair::LightClientBootstrap
);
altair_mainnet_test!(
    altair_mainnet_light_client_update,
    "LightClientUpdate",
    altair::LightClientUpdate
);
altair_mainnet_test!(
    altair_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    altair::LightClientFinalityUpdate
);
altair_mainnet_test!(
    altair_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    altair::LightClientOptimisticUpdate
);

// Modified in altair
altair_mainnet_test!(
    altair_mainnet_beacon_block,
    "BeaconBlock",
    altair::BeaconBlock
);
altair_mainnet_test!(
    altair_mainnet_beacon_block_body,
    "BeaconBlockBody",
    altair::BeaconBlockBody
);
altair_mainnet_test!(
    altair_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    altair::SignedBeaconBlock
);
altair_mainnet_test!(
    altair_mainnet_beacon_state,
    "BeaconState",
    altair::BeaconState
);

// ── Bellatrix mainnet ──

macro_rules! bellatrix_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "bellatrix", $type_name);
        }
    };
}

use spec_tests::types::bellatrix;

// Unchanged from altair
bellatrix_mainnet_test!(
    bellatrix_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    AggregateAndProof
);
bellatrix_mainnet_test!(bellatrix_mainnet_attestation, "Attestation", Attestation);
bellatrix_mainnet_test!(
    bellatrix_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_attester_slashing,
    "AttesterSlashing",
    AttesterSlashing
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
bellatrix_mainnet_test!(bellatrix_mainnet_checkpoint, "Checkpoint", Checkpoint);
bellatrix_mainnet_test!(
    bellatrix_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
bellatrix_mainnet_test!(bellatrix_mainnet_deposit, "Deposit", Deposit);
bellatrix_mainnet_test!(bellatrix_mainnet_deposit_data, "DepositData", DepositData);
bellatrix_mainnet_test!(
    bellatrix_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
bellatrix_mainnet_test!(bellatrix_mainnet_eth1_block, "Eth1Block", Eth1Block);
bellatrix_mainnet_test!(bellatrix_mainnet_eth1_data, "Eth1Data", Eth1Data);
bellatrix_mainnet_test!(bellatrix_mainnet_fork, "Fork", Fork);
bellatrix_mainnet_test!(bellatrix_mainnet_fork_data, "ForkData", ForkData);
bellatrix_mainnet_test!(
    bellatrix_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_indexed_attestation,
    "IndexedAttestation",
    IndexedAttestation
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    altair::LightClientBootstrap
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    altair::LightClientFinalityUpdate
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_light_client_header,
    "LightClientHeader",
    altair::LightClientHeader
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    altair::LightClientOptimisticUpdate
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_light_client_update,
    "LightClientUpdate",
    altair::LightClientUpdate
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    SignedAggregateAndProof
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
bellatrix_mainnet_test!(bellatrix_mainnet_signing_data, "SigningData", SigningData);
bellatrix_mainnet_test!(
    bellatrix_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
bellatrix_mainnet_test!(bellatrix_mainnet_validator, "Validator", Validator);
bellatrix_mainnet_test!(
    bellatrix_mainnet_voluntary_exit,
    "VoluntaryExit",
    VoluntaryExit
);

// New in bellatrix
bellatrix_mainnet_test!(
    bellatrix_mainnet_execution_payload,
    "ExecutionPayload",
    bellatrix::ExecutionPayload
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_execution_payload_header,
    "ExecutionPayloadHeader",
    bellatrix::ExecutionPayloadHeader
);
bellatrix_mainnet_test!(bellatrix_mainnet_pow_block, "PowBlock", bellatrix::PowBlock);

// Modified in bellatrix
bellatrix_mainnet_test!(
    bellatrix_mainnet_beacon_block,
    "BeaconBlock",
    bellatrix::BeaconBlock
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_beacon_block_body,
    "BeaconBlockBody",
    bellatrix::BeaconBlockBody
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    bellatrix::SignedBeaconBlock
);
bellatrix_mainnet_test!(
    bellatrix_mainnet_beacon_state,
    "BeaconState",
    bellatrix::BeaconState
);

// ── Capella mainnet ──

macro_rules! capella_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "capella", $type_name);
        }
    };
}

use spec_tests::types::capella;

// Unchanged from bellatrix
capella_mainnet_test!(
    capella_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    AggregateAndProof
);
capella_mainnet_test!(capella_mainnet_attestation, "Attestation", Attestation);
capella_mainnet_test!(
    capella_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
capella_mainnet_test!(
    capella_mainnet_attester_slashing,
    "AttesterSlashing",
    AttesterSlashing
);
capella_mainnet_test!(
    capella_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
capella_mainnet_test!(capella_mainnet_checkpoint, "Checkpoint", Checkpoint);
capella_mainnet_test!(
    capella_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
capella_mainnet_test!(capella_mainnet_deposit, "Deposit", Deposit);
capella_mainnet_test!(capella_mainnet_deposit_data, "DepositData", DepositData);
capella_mainnet_test!(
    capella_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
capella_mainnet_test!(capella_mainnet_eth1_block, "Eth1Block", Eth1Block);
capella_mainnet_test!(capella_mainnet_eth1_data, "Eth1Data", Eth1Data);
capella_mainnet_test!(capella_mainnet_fork, "Fork", Fork);
capella_mainnet_test!(capella_mainnet_fork_data, "ForkData", ForkData);
capella_mainnet_test!(
    capella_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
capella_mainnet_test!(
    capella_mainnet_indexed_attestation,
    "IndexedAttestation",
    IndexedAttestation
);
capella_mainnet_test!(
    capella_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
capella_mainnet_test!(
    capella_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
capella_mainnet_test!(
    capella_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    SignedAggregateAndProof
);
capella_mainnet_test!(
    capella_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
capella_mainnet_test!(
    capella_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
capella_mainnet_test!(
    capella_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
capella_mainnet_test!(capella_mainnet_signing_data, "SigningData", SigningData);
capella_mainnet_test!(
    capella_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
capella_mainnet_test!(
    capella_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);
capella_mainnet_test!(
    capella_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
capella_mainnet_test!(
    capella_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
capella_mainnet_test!(
    capella_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
capella_mainnet_test!(capella_mainnet_validator, "Validator", Validator);
capella_mainnet_test!(
    capella_mainnet_voluntary_exit,
    "VoluntaryExit",
    VoluntaryExit
);

// New in capella
capella_mainnet_test!(
    capella_mainnet_withdrawal,
    "Withdrawal",
    capella::Withdrawal
);
capella_mainnet_test!(
    capella_mainnet_bls_to_execution_change,
    "BLSToExecutionChange",
    capella::BLSToExecutionChange
);
capella_mainnet_test!(
    capella_mainnet_signed_bls_to_execution_change,
    "SignedBLSToExecutionChange",
    capella::SignedBLSToExecutionChange
);
capella_mainnet_test!(
    capella_mainnet_historical_summary,
    "HistoricalSummary",
    capella::HistoricalSummary
);

// Modified in capella
capella_mainnet_test!(
    capella_mainnet_execution_payload,
    "ExecutionPayload",
    capella::ExecutionPayload
);
capella_mainnet_test!(
    capella_mainnet_execution_payload_header,
    "ExecutionPayloadHeader",
    capella::ExecutionPayloadHeader
);
capella_mainnet_test!(
    capella_mainnet_beacon_block,
    "BeaconBlock",
    capella::BeaconBlock
);
capella_mainnet_test!(
    capella_mainnet_beacon_block_body,
    "BeaconBlockBody",
    capella::BeaconBlockBody
);
capella_mainnet_test!(
    capella_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    capella::SignedBeaconBlock
);
capella_mainnet_test!(
    capella_mainnet_beacon_state,
    "BeaconState",
    capella::BeaconState
);

// Light client (modified in capella)
capella_mainnet_test!(
    capella_mainnet_light_client_header,
    "LightClientHeader",
    capella::LightClientHeader
);
capella_mainnet_test!(
    capella_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    capella::LightClientBootstrap
);
capella_mainnet_test!(
    capella_mainnet_light_client_update,
    "LightClientUpdate",
    capella::LightClientUpdate
);
capella_mainnet_test!(
    capella_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    capella::LightClientFinalityUpdate
);
capella_mainnet_test!(
    capella_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    capella::LightClientOptimisticUpdate
);

// ── Deneb mainnet ──

macro_rules! deneb_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "deneb", $type_name);
        }
    };
}

use spec_tests::types::deneb;

// Unchanged from capella
deneb_mainnet_test!(
    deneb_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    AggregateAndProof
);
deneb_mainnet_test!(deneb_mainnet_attestation, "Attestation", Attestation);
deneb_mainnet_test!(
    deneb_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
deneb_mainnet_test!(
    deneb_mainnet_attester_slashing,
    "AttesterSlashing",
    AttesterSlashing
);
deneb_mainnet_test!(
    deneb_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
deneb_mainnet_test!(
    deneb_mainnet_bls_to_execution_change,
    "BLSToExecutionChange",
    capella::BLSToExecutionChange
);
deneb_mainnet_test!(deneb_mainnet_checkpoint, "Checkpoint", Checkpoint);
deneb_mainnet_test!(
    deneb_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
deneb_mainnet_test!(deneb_mainnet_deposit, "Deposit", Deposit);
deneb_mainnet_test!(deneb_mainnet_deposit_data, "DepositData", DepositData);
deneb_mainnet_test!(
    deneb_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
deneb_mainnet_test!(deneb_mainnet_eth1_block, "Eth1Block", Eth1Block);
deneb_mainnet_test!(deneb_mainnet_eth1_data, "Eth1Data", Eth1Data);
deneb_mainnet_test!(deneb_mainnet_fork, "Fork", Fork);
deneb_mainnet_test!(deneb_mainnet_fork_data, "ForkData", ForkData);
deneb_mainnet_test!(
    deneb_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
deneb_mainnet_test!(
    deneb_mainnet_historical_summary,
    "HistoricalSummary",
    capella::HistoricalSummary
);
deneb_mainnet_test!(
    deneb_mainnet_indexed_attestation,
    "IndexedAttestation",
    IndexedAttestation
);
deneb_mainnet_test!(
    deneb_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
deneb_mainnet_test!(
    deneb_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
deneb_mainnet_test!(
    deneb_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    SignedAggregateAndProof
);
deneb_mainnet_test!(
    deneb_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
deneb_mainnet_test!(
    deneb_mainnet_signed_bls_to_execution_change,
    "SignedBLSToExecutionChange",
    capella::SignedBLSToExecutionChange
);
deneb_mainnet_test!(
    deneb_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
deneb_mainnet_test!(
    deneb_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
deneb_mainnet_test!(deneb_mainnet_signing_data, "SigningData", SigningData);
deneb_mainnet_test!(
    deneb_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
deneb_mainnet_test!(
    deneb_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);
deneb_mainnet_test!(
    deneb_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
deneb_mainnet_test!(
    deneb_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
deneb_mainnet_test!(
    deneb_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
deneb_mainnet_test!(deneb_mainnet_validator, "Validator", Validator);
deneb_mainnet_test!(deneb_mainnet_voluntary_exit, "VoluntaryExit", VoluntaryExit);
deneb_mainnet_test!(deneb_mainnet_withdrawal, "Withdrawal", capella::Withdrawal);

// New in deneb
deneb_mainnet_test!(
    deneb_mainnet_blob_identifier,
    "BlobIdentifier",
    deneb::BlobIdentifier
);
deneb_mainnet_test!(
    deneb_mainnet_blob_sidecar,
    "BlobSidecar",
    deneb::BlobSidecar
);

// Modified in deneb
deneb_mainnet_test!(
    deneb_mainnet_execution_payload,
    "ExecutionPayload",
    deneb::ExecutionPayload
);
deneb_mainnet_test!(
    deneb_mainnet_execution_payload_header,
    "ExecutionPayloadHeader",
    deneb::ExecutionPayloadHeader
);
deneb_mainnet_test!(
    deneb_mainnet_beacon_block,
    "BeaconBlock",
    deneb::BeaconBlock
);
deneb_mainnet_test!(
    deneb_mainnet_beacon_block_body,
    "BeaconBlockBody",
    deneb::BeaconBlockBody
);
deneb_mainnet_test!(
    deneb_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    deneb::SignedBeaconBlock
);
deneb_mainnet_test!(
    deneb_mainnet_beacon_state,
    "BeaconState",
    deneb::BeaconState
);

// Light client (modified in deneb)
deneb_mainnet_test!(
    deneb_mainnet_light_client_header,
    "LightClientHeader",
    deneb::LightClientHeader
);
deneb_mainnet_test!(
    deneb_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    deneb::LightClientBootstrap
);
deneb_mainnet_test!(
    deneb_mainnet_light_client_update,
    "LightClientUpdate",
    deneb::LightClientUpdate
);
deneb_mainnet_test!(
    deneb_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    deneb::LightClientFinalityUpdate
);
deneb_mainnet_test!(
    deneb_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    deneb::LightClientOptimisticUpdate
);
