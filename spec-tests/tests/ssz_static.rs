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

// ── Electra mainnet ──

macro_rules! electra_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "electra", $type_name);
        }
    };
}

use spec_tests::types::electra;

// Unchanged
electra_mainnet_test!(
    electra_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
electra_mainnet_test!(
    electra_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
electra_mainnet_test!(
    electra_mainnet_blob_identifier,
    "BlobIdentifier",
    deneb::BlobIdentifier
);
electra_mainnet_test!(
    electra_mainnet_blob_sidecar,
    "BlobSidecar",
    deneb::BlobSidecar
);
electra_mainnet_test!(
    electra_mainnet_bls_to_execution_change,
    "BLSToExecutionChange",
    capella::BLSToExecutionChange
);
electra_mainnet_test!(electra_mainnet_checkpoint, "Checkpoint", Checkpoint);
electra_mainnet_test!(
    electra_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
electra_mainnet_test!(electra_mainnet_deposit, "Deposit", Deposit);
electra_mainnet_test!(electra_mainnet_deposit_data, "DepositData", DepositData);
electra_mainnet_test!(
    electra_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
electra_mainnet_test!(electra_mainnet_eth1_block, "Eth1Block", Eth1Block);
electra_mainnet_test!(electra_mainnet_eth1_data, "Eth1Data", Eth1Data);
electra_mainnet_test!(electra_mainnet_fork, "Fork", Fork);
electra_mainnet_test!(electra_mainnet_fork_data, "ForkData", ForkData);
electra_mainnet_test!(
    electra_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
electra_mainnet_test!(
    electra_mainnet_historical_summary,
    "HistoricalSummary",
    capella::HistoricalSummary
);
electra_mainnet_test!(
    electra_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
electra_mainnet_test!(electra_mainnet_pow_block, "PowBlock", bellatrix::PowBlock);
electra_mainnet_test!(
    electra_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
electra_mainnet_test!(
    electra_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
electra_mainnet_test!(
    electra_mainnet_signed_bls_to_execution_change,
    "SignedBLSToExecutionChange",
    capella::SignedBLSToExecutionChange
);
electra_mainnet_test!(
    electra_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
electra_mainnet_test!(
    electra_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
electra_mainnet_test!(electra_mainnet_signing_data, "SigningData", SigningData);
electra_mainnet_test!(
    electra_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
electra_mainnet_test!(
    electra_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);
electra_mainnet_test!(
    electra_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
electra_mainnet_test!(
    electra_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
electra_mainnet_test!(
    electra_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
electra_mainnet_test!(electra_mainnet_validator, "Validator", Validator);
electra_mainnet_test!(
    electra_mainnet_voluntary_exit,
    "VoluntaryExit",
    VoluntaryExit
);
electra_mainnet_test!(
    electra_mainnet_withdrawal,
    "Withdrawal",
    capella::Withdrawal
);

// New in electra
electra_mainnet_test!(
    electra_mainnet_consolidation_request,
    "ConsolidationRequest",
    electra::ConsolidationRequest
);
electra_mainnet_test!(
    electra_mainnet_deposit_request,
    "DepositRequest",
    electra::DepositRequest
);
electra_mainnet_test!(
    electra_mainnet_execution_requests,
    "ExecutionRequests",
    electra::ExecutionRequests
);
electra_mainnet_test!(
    electra_mainnet_pending_consolidation,
    "PendingConsolidation",
    electra::PendingConsolidation
);
electra_mainnet_test!(
    electra_mainnet_pending_deposit,
    "PendingDeposit",
    electra::PendingDeposit
);
electra_mainnet_test!(
    electra_mainnet_pending_partial_withdrawal,
    "PendingPartialWithdrawal",
    electra::PendingPartialWithdrawal
);
electra_mainnet_test!(
    electra_mainnet_single_attestation,
    "SingleAttestation",
    electra::SingleAttestation
);
electra_mainnet_test!(
    electra_mainnet_withdrawal_request,
    "WithdrawalRequest",
    electra::WithdrawalRequest
);

// Modified in electra
electra_mainnet_test!(
    electra_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    electra::AggregateAndProof
);
electra_mainnet_test!(
    electra_mainnet_attestation,
    "Attestation",
    electra::Attestation
);
electra_mainnet_test!(
    electra_mainnet_attester_slashing,
    "AttesterSlashing",
    electra::AttesterSlashing
);
electra_mainnet_test!(
    electra_mainnet_indexed_attestation,
    "IndexedAttestation",
    electra::IndexedAttestation
);
electra_mainnet_test!(
    electra_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    electra::SignedAggregateAndProof
);
electra_mainnet_test!(
    electra_mainnet_execution_payload,
    "ExecutionPayload",
    electra::ExecutionPayload
);
electra_mainnet_test!(
    electra_mainnet_execution_payload_header,
    "ExecutionPayloadHeader",
    electra::ExecutionPayloadHeader
);
electra_mainnet_test!(
    electra_mainnet_beacon_block,
    "BeaconBlock",
    electra::BeaconBlock
);
electra_mainnet_test!(
    electra_mainnet_beacon_block_body,
    "BeaconBlockBody",
    electra::BeaconBlockBody
);
electra_mainnet_test!(
    electra_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    electra::SignedBeaconBlock
);
electra_mainnet_test!(
    electra_mainnet_beacon_state,
    "BeaconState",
    electra::BeaconState
);

// Light client
electra_mainnet_test!(
    electra_mainnet_light_client_header,
    "LightClientHeader",
    electra::LightClientHeader
);
electra_mainnet_test!(
    electra_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    electra::LightClientBootstrap
);
electra_mainnet_test!(
    electra_mainnet_light_client_update,
    "LightClientUpdate",
    electra::LightClientUpdate
);
electra_mainnet_test!(
    electra_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    electra::LightClientFinalityUpdate
);
electra_mainnet_test!(
    electra_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    electra::LightClientOptimisticUpdate
);

// ── Fulu mainnet ──

macro_rules! fulu_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "fulu", $type_name);
        }
    };
}

use spec_tests::types::{fulu, fulu_beacon};

// Reuse electra types for unchanged ones
fulu_mainnet_test!(
    fulu_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    electra::AggregateAndProof
);
fulu_mainnet_test!(
    fulu_mainnet_attestation,
    "Attestation",
    electra::Attestation
);
fulu_mainnet_test!(
    fulu_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
fulu_mainnet_test!(
    fulu_mainnet_attester_slashing,
    "AttesterSlashing",
    electra::AttesterSlashing
);
fulu_mainnet_test!(
    fulu_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
fulu_mainnet_test!(
    fulu_mainnet_blob_identifier,
    "BlobIdentifier",
    deneb::BlobIdentifier
);
fulu_mainnet_test!(fulu_mainnet_blob_sidecar, "BlobSidecar", deneb::BlobSidecar);
fulu_mainnet_test!(
    fulu_mainnet_bls_to_execution_change,
    "BLSToExecutionChange",
    capella::BLSToExecutionChange
);
fulu_mainnet_test!(fulu_mainnet_checkpoint, "Checkpoint", Checkpoint);
fulu_mainnet_test!(
    fulu_mainnet_consolidation_request,
    "ConsolidationRequest",
    electra::ConsolidationRequest
);
fulu_mainnet_test!(
    fulu_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
fulu_mainnet_test!(fulu_mainnet_deposit, "Deposit", Deposit);
fulu_mainnet_test!(fulu_mainnet_deposit_data, "DepositData", DepositData);
fulu_mainnet_test!(
    fulu_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
fulu_mainnet_test!(
    fulu_mainnet_deposit_request,
    "DepositRequest",
    electra::DepositRequest
);
fulu_mainnet_test!(fulu_mainnet_eth1_block, "Eth1Block", Eth1Block);
fulu_mainnet_test!(fulu_mainnet_eth1_data, "Eth1Data", Eth1Data);
fulu_mainnet_test!(
    fulu_mainnet_execution_payload,
    "ExecutionPayload",
    electra::ExecutionPayload
);
fulu_mainnet_test!(
    fulu_mainnet_execution_payload_header,
    "ExecutionPayloadHeader",
    electra::ExecutionPayloadHeader
);
fulu_mainnet_test!(
    fulu_mainnet_execution_requests,
    "ExecutionRequests",
    electra::ExecutionRequests
);
fulu_mainnet_test!(fulu_mainnet_fork, "Fork", Fork);
fulu_mainnet_test!(fulu_mainnet_fork_data, "ForkData", ForkData);
fulu_mainnet_test!(
    fulu_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
fulu_mainnet_test!(
    fulu_mainnet_historical_summary,
    "HistoricalSummary",
    capella::HistoricalSummary
);
fulu_mainnet_test!(
    fulu_mainnet_indexed_attestation,
    "IndexedAttestation",
    electra::IndexedAttestation
);
fulu_mainnet_test!(
    fulu_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
fulu_mainnet_test!(
    fulu_mainnet_pending_consolidation,
    "PendingConsolidation",
    electra::PendingConsolidation
);
fulu_mainnet_test!(
    fulu_mainnet_pending_deposit,
    "PendingDeposit",
    electra::PendingDeposit
);
fulu_mainnet_test!(
    fulu_mainnet_pending_partial_withdrawal,
    "PendingPartialWithdrawal",
    electra::PendingPartialWithdrawal
);
fulu_mainnet_test!(fulu_mainnet_pow_block, "PowBlock", bellatrix::PowBlock);
fulu_mainnet_test!(
    fulu_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
fulu_mainnet_test!(
    fulu_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    electra::SignedAggregateAndProof
);
fulu_mainnet_test!(
    fulu_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
fulu_mainnet_test!(
    fulu_mainnet_signed_bls_to_execution_change,
    "SignedBLSToExecutionChange",
    capella::SignedBLSToExecutionChange
);
fulu_mainnet_test!(
    fulu_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
fulu_mainnet_test!(
    fulu_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
fulu_mainnet_test!(fulu_mainnet_signing_data, "SigningData", SigningData);
fulu_mainnet_test!(
    fulu_mainnet_single_attestation,
    "SingleAttestation",
    electra::SingleAttestation
);
fulu_mainnet_test!(
    fulu_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
fulu_mainnet_test!(
    fulu_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);
fulu_mainnet_test!(
    fulu_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
fulu_mainnet_test!(
    fulu_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
fulu_mainnet_test!(
    fulu_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
fulu_mainnet_test!(fulu_mainnet_validator, "Validator", Validator);
fulu_mainnet_test!(fulu_mainnet_voluntary_exit, "VoluntaryExit", VoluntaryExit);
fulu_mainnet_test!(fulu_mainnet_withdrawal, "Withdrawal", capella::Withdrawal);
fulu_mainnet_test!(
    fulu_mainnet_withdrawal_request,
    "WithdrawalRequest",
    electra::WithdrawalRequest
);

// Reuse electra for block/light client (same structure in fulu)
fulu_mainnet_test!(
    fulu_mainnet_beacon_block,
    "BeaconBlock",
    electra::BeaconBlock
);
fulu_mainnet_test!(
    fulu_mainnet_beacon_block_body,
    "BeaconBlockBody",
    electra::BeaconBlockBody
);
fulu_mainnet_test!(
    fulu_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    electra::SignedBeaconBlock
);
fulu_mainnet_test!(
    fulu_mainnet_light_client_header,
    "LightClientHeader",
    electra::LightClientHeader
);
fulu_mainnet_test!(
    fulu_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    electra::LightClientBootstrap
);
fulu_mainnet_test!(
    fulu_mainnet_light_client_update,
    "LightClientUpdate",
    electra::LightClientUpdate
);
fulu_mainnet_test!(
    fulu_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    electra::LightClientFinalityUpdate
);
fulu_mainnet_test!(
    fulu_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    electra::LightClientOptimisticUpdate
);

// New in fulu
fulu_mainnet_test!(
    fulu_mainnet_data_column_sidecar,
    "DataColumnSidecar",
    fulu::DataColumnSidecar
);
fulu_mainnet_test!(
    fulu_mainnet_data_columns_by_root_identifier,
    "DataColumnsByRootIdentifier",
    fulu::DataColumnsByRootIdentifier
);
fulu_mainnet_test!(fulu_mainnet_matrix_entry, "MatrixEntry", fulu::MatrixEntry);

// Modified in fulu (BeaconState has proposer_lookahead field)
fulu_mainnet_test!(
    fulu_mainnet_beacon_state,
    "BeaconState",
    fulu_beacon::BeaconState
);

// ── Gloas mainnet ──

macro_rules! gloas_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "gloas", $type_name);
        }
    };
}

use spec_tests::types::gloas;

// Unchanged from fulu/electra
gloas_mainnet_test!(
    gloas_mainnet_attestation,
    "Attestation",
    electra::Attestation
);
gloas_mainnet_test!(
    gloas_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
gloas_mainnet_test!(
    gloas_mainnet_attester_slashing,
    "AttesterSlashing",
    electra::AttesterSlashing
);
gloas_mainnet_test!(
    gloas_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
gloas_mainnet_test!(
    gloas_mainnet_blob_identifier,
    "BlobIdentifier",
    deneb::BlobIdentifier
);
gloas_mainnet_test!(
    gloas_mainnet_blob_sidecar,
    "BlobSidecar",
    deneb::BlobSidecar
);
gloas_mainnet_test!(
    gloas_mainnet_bls_to_execution_change,
    "BLSToExecutionChange",
    capella::BLSToExecutionChange
);
gloas_mainnet_test!(gloas_mainnet_checkpoint, "Checkpoint", Checkpoint);
gloas_mainnet_test!(
    gloas_mainnet_consolidation_request,
    "ConsolidationRequest",
    electra::ConsolidationRequest
);
gloas_mainnet_test!(
    gloas_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
gloas_mainnet_test!(
    gloas_mainnet_data_column_sidecar,
    "DataColumnSidecar",
    gloas::DataColumnSidecar
);
gloas_mainnet_test!(
    gloas_mainnet_data_columns_by_root_identifier,
    "DataColumnsByRootIdentifier",
    fulu::DataColumnsByRootIdentifier
);
gloas_mainnet_test!(gloas_mainnet_deposit, "Deposit", Deposit);
gloas_mainnet_test!(gloas_mainnet_deposit_data, "DepositData", DepositData);
gloas_mainnet_test!(
    gloas_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
gloas_mainnet_test!(
    gloas_mainnet_deposit_request,
    "DepositRequest",
    electra::DepositRequest
);
gloas_mainnet_test!(gloas_mainnet_eth1_block, "Eth1Block", Eth1Block);
gloas_mainnet_test!(gloas_mainnet_eth1_data, "Eth1Data", Eth1Data);
gloas_mainnet_test!(
    gloas_mainnet_execution_payload,
    "ExecutionPayload",
    electra::ExecutionPayload
);
gloas_mainnet_test!(
    gloas_mainnet_execution_payload_header,
    "ExecutionPayloadHeader",
    electra::ExecutionPayloadHeader
);
gloas_mainnet_test!(
    gloas_mainnet_execution_requests,
    "ExecutionRequests",
    electra::ExecutionRequests
);
gloas_mainnet_test!(gloas_mainnet_fork, "Fork", Fork);
gloas_mainnet_test!(gloas_mainnet_fork_data, "ForkData", ForkData);
gloas_mainnet_test!(
    gloas_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
gloas_mainnet_test!(
    gloas_mainnet_historical_summary,
    "HistoricalSummary",
    capella::HistoricalSummary
);
gloas_mainnet_test!(
    gloas_mainnet_indexed_attestation,
    "IndexedAttestation",
    electra::IndexedAttestation
);
gloas_mainnet_test!(gloas_mainnet_matrix_entry, "MatrixEntry", fulu::MatrixEntry);
gloas_mainnet_test!(
    gloas_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
gloas_mainnet_test!(
    gloas_mainnet_pending_consolidation,
    "PendingConsolidation",
    electra::PendingConsolidation
);
gloas_mainnet_test!(
    gloas_mainnet_pending_deposit,
    "PendingDeposit",
    electra::PendingDeposit
);
gloas_mainnet_test!(
    gloas_mainnet_pending_partial_withdrawal,
    "PendingPartialWithdrawal",
    electra::PendingPartialWithdrawal
);
gloas_mainnet_test!(gloas_mainnet_pow_block, "PowBlock", bellatrix::PowBlock);
gloas_mainnet_test!(
    gloas_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
gloas_mainnet_test!(
    gloas_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    electra::SignedAggregateAndProof
);
gloas_mainnet_test!(
    gloas_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
gloas_mainnet_test!(
    gloas_mainnet_signed_bls_to_execution_change,
    "SignedBLSToExecutionChange",
    capella::SignedBLSToExecutionChange
);
gloas_mainnet_test!(
    gloas_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
gloas_mainnet_test!(
    gloas_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
gloas_mainnet_test!(gloas_mainnet_signing_data, "SigningData", SigningData);
gloas_mainnet_test!(
    gloas_mainnet_single_attestation,
    "SingleAttestation",
    electra::SingleAttestation
);
gloas_mainnet_test!(
    gloas_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
gloas_mainnet_test!(
    gloas_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);
gloas_mainnet_test!(
    gloas_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
gloas_mainnet_test!(
    gloas_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
gloas_mainnet_test!(
    gloas_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
gloas_mainnet_test!(gloas_mainnet_validator, "Validator", Validator);
gloas_mainnet_test!(gloas_mainnet_voluntary_exit, "VoluntaryExit", VoluntaryExit);
gloas_mainnet_test!(gloas_mainnet_withdrawal, "Withdrawal", capella::Withdrawal);
gloas_mainnet_test!(
    gloas_mainnet_withdrawal_request,
    "WithdrawalRequest",
    electra::WithdrawalRequest
);
gloas_mainnet_test!(
    gloas_mainnet_light_client_header,
    "LightClientHeader",
    electra::LightClientHeader
);
gloas_mainnet_test!(
    gloas_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    electra::LightClientBootstrap
);
gloas_mainnet_test!(
    gloas_mainnet_light_client_update,
    "LightClientUpdate",
    electra::LightClientUpdate
);
gloas_mainnet_test!(
    gloas_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    electra::LightClientFinalityUpdate
);
gloas_mainnet_test!(
    gloas_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    electra::LightClientOptimisticUpdate
);

// New in gloas
gloas_mainnet_test!(
    gloas_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    electra::AggregateAndProof
);
gloas_mainnet_test!(
    gloas_mainnet_builder_pending_payment,
    "BuilderPendingPayment",
    gloas::BuilderPendingPayment
);
gloas_mainnet_test!(
    gloas_mainnet_builder_pending_withdrawal,
    "BuilderPendingWithdrawal",
    gloas::BuilderPendingWithdrawal
);
gloas_mainnet_test!(
    gloas_mainnet_execution_payload_bid,
    "ExecutionPayloadBid",
    gloas::ExecutionPayloadBid
);
gloas_mainnet_test!(
    gloas_mainnet_execution_payload_envelope,
    "ExecutionPayloadEnvelope",
    gloas::ExecutionPayloadEnvelope
);
gloas_mainnet_test!(
    gloas_mainnet_fork_choice_node,
    "ForkChoiceNode",
    gloas::ForkChoiceNode
);
gloas_mainnet_test!(
    gloas_mainnet_indexed_payload_attestation,
    "IndexedPayloadAttestation",
    gloas::IndexedPayloadAttestation
);
gloas_mainnet_test!(
    gloas_mainnet_payload_attestation,
    "PayloadAttestation",
    gloas::PayloadAttestation
);
gloas_mainnet_test!(
    gloas_mainnet_payload_attestation_data,
    "PayloadAttestationData",
    gloas::PayloadAttestationData
);
gloas_mainnet_test!(
    gloas_mainnet_payload_attestation_message,
    "PayloadAttestationMessage",
    gloas::PayloadAttestationMessage
);
gloas_mainnet_test!(
    gloas_mainnet_signed_execution_payload_bid,
    "SignedExecutionPayloadBid",
    gloas::SignedExecutionPayloadBid
);
gloas_mainnet_test!(
    gloas_mainnet_signed_execution_payload_envelope,
    "SignedExecutionPayloadEnvelope",
    gloas::SignedExecutionPayloadEnvelope
);

// Modified in gloas
gloas_mainnet_test!(
    gloas_mainnet_beacon_block,
    "BeaconBlock",
    gloas::BeaconBlock
);
gloas_mainnet_test!(
    gloas_mainnet_beacon_block_body,
    "BeaconBlockBody",
    gloas::BeaconBlockBody
);
gloas_mainnet_test!(
    gloas_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    gloas::SignedBeaconBlock
);
gloas_mainnet_test!(
    gloas_mainnet_beacon_state,
    "BeaconState",
    gloas::BeaconState
);

// ── EIP7805 mainnet ──

macro_rules! eip7805_mainnet_test {
    ($test_name:ident, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>(Archive::Mainnet, "eip7805", $type_name);
        }
    };
}

use spec_tests::types::eip7805;

// Reuse electra types for most
eip7805_mainnet_test!(
    eip7805_mainnet_aggregate_and_proof,
    "AggregateAndProof",
    electra::AggregateAndProof
);
eip7805_mainnet_test!(
    eip7805_mainnet_attestation,
    "Attestation",
    electra::Attestation
);
eip7805_mainnet_test!(
    eip7805_mainnet_attestation_data,
    "AttestationData",
    AttestationData
);
eip7805_mainnet_test!(
    eip7805_mainnet_attester_slashing,
    "AttesterSlashing",
    electra::AttesterSlashing
);
eip7805_mainnet_test!(
    eip7805_mainnet_beacon_block_header,
    "BeaconBlockHeader",
    BeaconBlockHeader
);
eip7805_mainnet_test!(
    eip7805_mainnet_beacon_block,
    "BeaconBlock",
    electra::BeaconBlock
);
eip7805_mainnet_test!(
    eip7805_mainnet_beacon_block_body,
    "BeaconBlockBody",
    electra::BeaconBlockBody
);
eip7805_mainnet_test!(
    eip7805_mainnet_beacon_state,
    "BeaconState",
    fulu_beacon::BeaconState
);
eip7805_mainnet_test!(
    eip7805_mainnet_blob_identifier,
    "BlobIdentifier",
    deneb::BlobIdentifier
);
eip7805_mainnet_test!(
    eip7805_mainnet_blob_sidecar,
    "BlobSidecar",
    deneb::BlobSidecar
);
eip7805_mainnet_test!(
    eip7805_mainnet_bls_to_execution_change,
    "BLSToExecutionChange",
    capella::BLSToExecutionChange
);
eip7805_mainnet_test!(eip7805_mainnet_checkpoint, "Checkpoint", Checkpoint);
eip7805_mainnet_test!(
    eip7805_mainnet_consolidation_request,
    "ConsolidationRequest",
    electra::ConsolidationRequest
);
eip7805_mainnet_test!(
    eip7805_mainnet_contribution_and_proof,
    "ContributionAndProof",
    altair::ContributionAndProof
);
eip7805_mainnet_test!(eip7805_mainnet_deposit, "Deposit", Deposit);
eip7805_mainnet_test!(eip7805_mainnet_deposit_data, "DepositData", DepositData);
eip7805_mainnet_test!(
    eip7805_mainnet_deposit_message,
    "DepositMessage",
    DepositMessage
);
eip7805_mainnet_test!(
    eip7805_mainnet_deposit_request,
    "DepositRequest",
    electra::DepositRequest
);
eip7805_mainnet_test!(eip7805_mainnet_eth1_block, "Eth1Block", Eth1Block);
eip7805_mainnet_test!(eip7805_mainnet_eth1_data, "Eth1Data", Eth1Data);
eip7805_mainnet_test!(
    eip7805_mainnet_execution_payload,
    "ExecutionPayload",
    electra::ExecutionPayload
);
eip7805_mainnet_test!(
    eip7805_mainnet_execution_payload_header,
    "ExecutionPayloadHeader",
    electra::ExecutionPayloadHeader
);
eip7805_mainnet_test!(
    eip7805_mainnet_execution_requests,
    "ExecutionRequests",
    electra::ExecutionRequests
);
eip7805_mainnet_test!(eip7805_mainnet_fork, "Fork", Fork);
eip7805_mainnet_test!(eip7805_mainnet_fork_data, "ForkData", ForkData);
eip7805_mainnet_test!(
    eip7805_mainnet_historical_batch,
    "HistoricalBatch",
    HistoricalBatch
);
eip7805_mainnet_test!(
    eip7805_mainnet_historical_summary,
    "HistoricalSummary",
    capella::HistoricalSummary
);
eip7805_mainnet_test!(
    eip7805_mainnet_indexed_attestation,
    "IndexedAttestation",
    electra::IndexedAttestation
);
eip7805_mainnet_test!(
    eip7805_mainnet_pending_attestation,
    "PendingAttestation",
    PendingAttestation
);
eip7805_mainnet_test!(
    eip7805_mainnet_pending_consolidation,
    "PendingConsolidation",
    electra::PendingConsolidation
);
eip7805_mainnet_test!(
    eip7805_mainnet_pending_deposit,
    "PendingDeposit",
    electra::PendingDeposit
);
eip7805_mainnet_test!(
    eip7805_mainnet_pending_partial_withdrawal,
    "PendingPartialWithdrawal",
    electra::PendingPartialWithdrawal
);
eip7805_mainnet_test!(eip7805_mainnet_pow_block, "PowBlock", bellatrix::PowBlock);
eip7805_mainnet_test!(
    eip7805_mainnet_proposer_slashing,
    "ProposerSlashing",
    ProposerSlashing
);
eip7805_mainnet_test!(
    eip7805_mainnet_signed_aggregate_and_proof,
    "SignedAggregateAndProof",
    electra::SignedAggregateAndProof
);
eip7805_mainnet_test!(
    eip7805_mainnet_signed_beacon_block,
    "SignedBeaconBlock",
    electra::SignedBeaconBlock
);
eip7805_mainnet_test!(
    eip7805_mainnet_signed_beacon_block_header,
    "SignedBeaconBlockHeader",
    SignedBeaconBlockHeader
);
eip7805_mainnet_test!(
    eip7805_mainnet_signed_bls_to_execution_change,
    "SignedBLSToExecutionChange",
    capella::SignedBLSToExecutionChange
);
eip7805_mainnet_test!(
    eip7805_mainnet_signed_contribution_and_proof,
    "SignedContributionAndProof",
    altair::SignedContributionAndProof
);
eip7805_mainnet_test!(
    eip7805_mainnet_signed_voluntary_exit,
    "SignedVoluntaryExit",
    SignedVoluntaryExit
);
eip7805_mainnet_test!(eip7805_mainnet_signing_data, "SigningData", SigningData);
eip7805_mainnet_test!(
    eip7805_mainnet_single_attestation,
    "SingleAttestation",
    electra::SingleAttestation
);
eip7805_mainnet_test!(
    eip7805_mainnet_sync_aggregate,
    "SyncAggregate",
    altair::SyncAggregate
);
eip7805_mainnet_test!(
    eip7805_mainnet_sync_aggregator_selection_data,
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);
eip7805_mainnet_test!(
    eip7805_mainnet_sync_committee,
    "SyncCommittee",
    altair::SyncCommittee
);
eip7805_mainnet_test!(
    eip7805_mainnet_sync_committee_contribution,
    "SyncCommitteeContribution",
    altair::SyncCommitteeContribution
);
eip7805_mainnet_test!(
    eip7805_mainnet_sync_committee_message,
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
eip7805_mainnet_test!(eip7805_mainnet_validator, "Validator", Validator);
eip7805_mainnet_test!(
    eip7805_mainnet_voluntary_exit,
    "VoluntaryExit",
    VoluntaryExit
);
eip7805_mainnet_test!(
    eip7805_mainnet_withdrawal,
    "Withdrawal",
    capella::Withdrawal
);
eip7805_mainnet_test!(
    eip7805_mainnet_withdrawal_request,
    "WithdrawalRequest",
    electra::WithdrawalRequest
);
eip7805_mainnet_test!(
    eip7805_mainnet_light_client_header,
    "LightClientHeader",
    electra::LightClientHeader
);
eip7805_mainnet_test!(
    eip7805_mainnet_light_client_bootstrap,
    "LightClientBootstrap",
    electra::LightClientBootstrap
);
eip7805_mainnet_test!(
    eip7805_mainnet_light_client_update,
    "LightClientUpdate",
    electra::LightClientUpdate
);
eip7805_mainnet_test!(
    eip7805_mainnet_light_client_finality_update,
    "LightClientFinalityUpdate",
    electra::LightClientFinalityUpdate
);
eip7805_mainnet_test!(
    eip7805_mainnet_light_client_optimistic_update,
    "LightClientOptimisticUpdate",
    electra::LightClientOptimisticUpdate
);

// Fulu types also in eip7805
eip7805_mainnet_test!(
    eip7805_mainnet_data_column_sidecar,
    "DataColumnSidecar",
    fulu::DataColumnSidecar
);
eip7805_mainnet_test!(
    eip7805_mainnet_data_columns_by_root_identifier,
    "DataColumnsByRootIdentifier",
    fulu::DataColumnsByRootIdentifier
);
eip7805_mainnet_test!(
    eip7805_mainnet_matrix_entry,
    "MatrixEntry",
    fulu::MatrixEntry
);

// New in eip7805
eip7805_mainnet_test!(
    eip7805_mainnet_inclusion_list,
    "InclusionList",
    eip7805::InclusionList
);
eip7805_mainnet_test!(
    eip7805_mainnet_signed_inclusion_list,
    "SignedInclusionList",
    eip7805::SignedInclusionList
);
