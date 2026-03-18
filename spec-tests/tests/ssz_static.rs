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

use spec_tests::types::phase0::*;

#[test]
fn phase0_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>(Archive::Mainnet, "phase0", "AggregateAndProof");
}
#[test]
fn phase0_mainnet_attestation() {
    run_ssz_static_type::<Attestation>(Archive::Mainnet, "phase0", "Attestation");
}
#[test]
fn phase0_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "phase0", "AttestationData");
}
#[test]
fn phase0_mainnet_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>(Archive::Mainnet, "phase0", "AttesterSlashing");
}
#[test]
fn phase0_mainnet_beacon_block() {
    run_ssz_static_type::<BeaconBlock>(Archive::Mainnet, "phase0", "BeaconBlock");
}
#[test]
fn phase0_mainnet_beacon_block_body() {
    run_ssz_static_type::<BeaconBlockBody>(Archive::Mainnet, "phase0", "BeaconBlockBody");
}
#[test]
fn phase0_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "phase0", "BeaconBlockHeader");
}
#[test]
fn phase0_mainnet_beacon_state() {
    run_ssz_static_type::<BeaconState>(Archive::Mainnet, "phase0", "BeaconState");
}
#[test]
fn phase0_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "phase0", "Checkpoint");
}
#[test]
fn phase0_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "phase0", "Deposit");
}
#[test]
fn phase0_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "phase0", "DepositData");
}
#[test]
fn phase0_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "phase0", "DepositMessage");
}
#[test]
fn phase0_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "phase0", "Eth1Block");
}
#[test]
fn phase0_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "phase0", "Eth1Data");
}
#[test]
fn phase0_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "phase0", "Fork");
}
#[test]
fn phase0_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "phase0", "ForkData");
}
#[test]
fn phase0_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "phase0", "HistoricalBatch");
}
#[test]
fn phase0_mainnet_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>(Archive::Mainnet, "phase0", "IndexedAttestation");
}
#[test]
fn phase0_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "phase0", "PendingAttestation");
}
#[test]
fn phase0_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "phase0", "ProposerSlashing");
}
#[test]
fn phase0_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>(
        Archive::Mainnet,
        "phase0",
        "SignedAggregateAndProof",
    );
}
#[test]
fn phase0_mainnet_signed_beacon_block() {
    run_ssz_static_type::<SignedBeaconBlock>(Archive::Mainnet, "phase0", "SignedBeaconBlock");
}
#[test]
fn phase0_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "phase0",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn phase0_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "phase0", "SignedVoluntaryExit");
}
#[test]
fn phase0_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "phase0", "SigningData");
}
#[test]
fn phase0_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "phase0", "Validator");
}
#[test]
fn phase0_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "phase0", "VoluntaryExit");
}

// ── Altair mainnet ──

use spec_tests::types::altair;

// Unchanged from phase0
#[test]
fn altair_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>(Archive::Mainnet, "altair", "AggregateAndProof");
}
#[test]
fn altair_mainnet_attestation() {
    run_ssz_static_type::<Attestation>(Archive::Mainnet, "altair", "Attestation");
}
#[test]
fn altair_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "altair", "AttestationData");
}
#[test]
fn altair_mainnet_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>(Archive::Mainnet, "altair", "AttesterSlashing");
}
#[test]
fn altair_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "altair", "BeaconBlockHeader");
}
#[test]
fn altair_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "altair", "Checkpoint");
}
#[test]
fn altair_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "altair", "Deposit");
}
#[test]
fn altair_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "altair", "DepositData");
}
#[test]
fn altair_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "altair", "DepositMessage");
}
#[test]
fn altair_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "altair", "Eth1Block");
}
#[test]
fn altair_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "altair", "Eth1Data");
}
#[test]
fn altair_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "altair", "Fork");
}
#[test]
fn altair_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "altair", "ForkData");
}
#[test]
fn altair_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "altair", "HistoricalBatch");
}
#[test]
fn altair_mainnet_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>(Archive::Mainnet, "altair", "IndexedAttestation");
}
#[test]
fn altair_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "altair", "PendingAttestation");
}
#[test]
fn altair_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "altair", "ProposerSlashing");
}
#[test]
fn altair_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>(
        Archive::Mainnet,
        "altair",
        "SignedAggregateAndProof",
    );
}
#[test]
fn altair_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "altair",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn altair_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "altair", "SignedVoluntaryExit");
}
#[test]
fn altair_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "altair", "SigningData");
}
#[test]
fn altair_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "altair", "Validator");
}
#[test]
fn altair_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "altair", "VoluntaryExit");
}

// New in altair
#[test]
fn altair_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "altair", "SyncAggregate");
}
#[test]
fn altair_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "altair", "SyncCommittee");
}
#[test]
fn altair_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "altair",
        "SyncCommitteeMessage",
    );
}
#[test]
fn altair_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "altair",
        "SyncCommitteeContribution",
    );
}
#[test]
fn altair_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "altair",
        "ContributionAndProof",
    );
}
#[test]
fn altair_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "altair",
        "SignedContributionAndProof",
    );
}
#[test]
fn altair_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "altair",
        "SyncAggregatorSelectionData",
    );
}

// Light client types
#[test]
fn altair_mainnet_light_client_header() {
    run_ssz_static_type::<altair::LightClientHeader>(
        Archive::Mainnet,
        "altair",
        "LightClientHeader",
    );
}
#[test]
fn altair_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<altair::LightClientBootstrap>(
        Archive::Mainnet,
        "altair",
        "LightClientBootstrap",
    );
}
#[test]
fn altair_mainnet_light_client_update() {
    run_ssz_static_type::<altair::LightClientUpdate>(
        Archive::Mainnet,
        "altair",
        "LightClientUpdate",
    );
}
#[test]
fn altair_mainnet_light_client_finality_update() {
    run_ssz_static_type::<altair::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "altair",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn altair_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<altair::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "altair",
        "LightClientOptimisticUpdate",
    );
}

// Modified in altair
#[test]
fn altair_mainnet_beacon_block() {
    run_ssz_static_type::<altair::BeaconBlock>(Archive::Mainnet, "altair", "BeaconBlock");
}
#[test]
fn altair_mainnet_beacon_block_body() {
    run_ssz_static_type::<altair::BeaconBlockBody>(Archive::Mainnet, "altair", "BeaconBlockBody");
}
#[test]
fn altair_mainnet_signed_beacon_block() {
    run_ssz_static_type::<altair::SignedBeaconBlock>(
        Archive::Mainnet,
        "altair",
        "SignedBeaconBlock",
    );
}
#[test]
fn altair_mainnet_beacon_state() {
    run_ssz_static_type::<altair::BeaconState>(Archive::Mainnet, "altair", "BeaconState");
}

// ── Bellatrix mainnet ──

use spec_tests::types::bellatrix;

// Unchanged from altair
#[test]
fn bellatrix_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>(Archive::Mainnet, "bellatrix", "AggregateAndProof");
}
#[test]
fn bellatrix_mainnet_attestation() {
    run_ssz_static_type::<Attestation>(Archive::Mainnet, "bellatrix", "Attestation");
}
#[test]
fn bellatrix_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "bellatrix", "AttestationData");
}
#[test]
fn bellatrix_mainnet_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>(Archive::Mainnet, "bellatrix", "AttesterSlashing");
}
#[test]
fn bellatrix_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "bellatrix", "BeaconBlockHeader");
}
#[test]
fn bellatrix_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "bellatrix", "Checkpoint");
}
#[test]
fn bellatrix_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "bellatrix",
        "ContributionAndProof",
    );
}
#[test]
fn bellatrix_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "bellatrix", "Deposit");
}
#[test]
fn bellatrix_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "bellatrix", "DepositData");
}
#[test]
fn bellatrix_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "bellatrix", "DepositMessage");
}
#[test]
fn bellatrix_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "bellatrix", "Eth1Block");
}
#[test]
fn bellatrix_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "bellatrix", "Eth1Data");
}
#[test]
fn bellatrix_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "bellatrix", "Fork");
}
#[test]
fn bellatrix_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "bellatrix", "ForkData");
}
#[test]
fn bellatrix_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "bellatrix", "HistoricalBatch");
}
#[test]
fn bellatrix_mainnet_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>(Archive::Mainnet, "bellatrix", "IndexedAttestation");
}
#[test]
fn bellatrix_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<altair::LightClientBootstrap>(
        Archive::Mainnet,
        "bellatrix",
        "LightClientBootstrap",
    );
}
#[test]
fn bellatrix_mainnet_light_client_finality_update() {
    run_ssz_static_type::<altair::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "bellatrix",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn bellatrix_mainnet_light_client_header() {
    run_ssz_static_type::<altair::LightClientHeader>(
        Archive::Mainnet,
        "bellatrix",
        "LightClientHeader",
    );
}
#[test]
fn bellatrix_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<altair::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "bellatrix",
        "LightClientOptimisticUpdate",
    );
}
#[test]
fn bellatrix_mainnet_light_client_update() {
    run_ssz_static_type::<altair::LightClientUpdate>(
        Archive::Mainnet,
        "bellatrix",
        "LightClientUpdate",
    );
}
#[test]
fn bellatrix_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "bellatrix", "PendingAttestation");
}
#[test]
fn bellatrix_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "bellatrix", "ProposerSlashing");
}
#[test]
fn bellatrix_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>(
        Archive::Mainnet,
        "bellatrix",
        "SignedAggregateAndProof",
    );
}
#[test]
fn bellatrix_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "bellatrix",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn bellatrix_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "bellatrix",
        "SignedContributionAndProof",
    );
}
#[test]
fn bellatrix_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(
        Archive::Mainnet,
        "bellatrix",
        "SignedVoluntaryExit",
    );
}
#[test]
fn bellatrix_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "bellatrix", "SigningData");
}
#[test]
fn bellatrix_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "bellatrix", "SyncAggregate");
}
#[test]
fn bellatrix_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "bellatrix",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn bellatrix_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "bellatrix", "SyncCommittee");
}
#[test]
fn bellatrix_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "bellatrix",
        "SyncCommitteeContribution",
    );
}
#[test]
fn bellatrix_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "bellatrix",
        "SyncCommitteeMessage",
    );
}
#[test]
fn bellatrix_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "bellatrix", "Validator");
}
#[test]
fn bellatrix_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "bellatrix", "VoluntaryExit");
}

// New in bellatrix
#[test]
fn bellatrix_mainnet_execution_payload() {
    run_ssz_static_type::<bellatrix::ExecutionPayload>(
        Archive::Mainnet,
        "bellatrix",
        "ExecutionPayload",
    );
}
#[test]
fn bellatrix_mainnet_execution_payload_header() {
    run_ssz_static_type::<bellatrix::ExecutionPayloadHeader>(
        Archive::Mainnet,
        "bellatrix",
        "ExecutionPayloadHeader",
    );
}
#[test]
fn bellatrix_mainnet_pow_block() {
    run_ssz_static_type::<bellatrix::PowBlock>(Archive::Mainnet, "bellatrix", "PowBlock");
}

// Modified in bellatrix
#[test]
fn bellatrix_mainnet_beacon_block() {
    run_ssz_static_type::<bellatrix::BeaconBlock>(Archive::Mainnet, "bellatrix", "BeaconBlock");
}
#[test]
fn bellatrix_mainnet_beacon_block_body() {
    run_ssz_static_type::<bellatrix::BeaconBlockBody>(
        Archive::Mainnet,
        "bellatrix",
        "BeaconBlockBody",
    );
}
#[test]
fn bellatrix_mainnet_signed_beacon_block() {
    run_ssz_static_type::<bellatrix::SignedBeaconBlock>(
        Archive::Mainnet,
        "bellatrix",
        "SignedBeaconBlock",
    );
}
#[test]
fn bellatrix_mainnet_beacon_state() {
    run_ssz_static_type::<bellatrix::BeaconState>(Archive::Mainnet, "bellatrix", "BeaconState");
}

// ── Capella mainnet ──

use spec_tests::types::capella;

// Unchanged from bellatrix
#[test]
fn capella_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>(Archive::Mainnet, "capella", "AggregateAndProof");
}
#[test]
fn capella_mainnet_attestation() {
    run_ssz_static_type::<Attestation>(Archive::Mainnet, "capella", "Attestation");
}
#[test]
fn capella_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "capella", "AttestationData");
}
#[test]
fn capella_mainnet_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>(Archive::Mainnet, "capella", "AttesterSlashing");
}
#[test]
fn capella_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "capella", "BeaconBlockHeader");
}
#[test]
fn capella_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "capella", "Checkpoint");
}
#[test]
fn capella_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "capella",
        "ContributionAndProof",
    );
}
#[test]
fn capella_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "capella", "Deposit");
}
#[test]
fn capella_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "capella", "DepositData");
}
#[test]
fn capella_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "capella", "DepositMessage");
}
#[test]
fn capella_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "capella", "Eth1Block");
}
#[test]
fn capella_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "capella", "Eth1Data");
}
#[test]
fn capella_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "capella", "Fork");
}
#[test]
fn capella_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "capella", "ForkData");
}
#[test]
fn capella_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "capella", "HistoricalBatch");
}
#[test]
fn capella_mainnet_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>(Archive::Mainnet, "capella", "IndexedAttestation");
}
#[test]
fn capella_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "capella", "PendingAttestation");
}
#[test]
fn capella_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "capella", "ProposerSlashing");
}
#[test]
fn capella_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>(
        Archive::Mainnet,
        "capella",
        "SignedAggregateAndProof",
    );
}
#[test]
fn capella_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "capella",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn capella_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "capella",
        "SignedContributionAndProof",
    );
}
#[test]
fn capella_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "capella", "SignedVoluntaryExit");
}
#[test]
fn capella_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "capella", "SigningData");
}
#[test]
fn capella_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "capella", "SyncAggregate");
}
#[test]
fn capella_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "capella",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn capella_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "capella", "SyncCommittee");
}
#[test]
fn capella_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "capella",
        "SyncCommitteeContribution",
    );
}
#[test]
fn capella_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "capella",
        "SyncCommitteeMessage",
    );
}
#[test]
fn capella_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "capella", "Validator");
}
#[test]
fn capella_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "capella", "VoluntaryExit");
}

// New in capella
#[test]
fn capella_mainnet_withdrawal() {
    run_ssz_static_type::<capella::Withdrawal>(Archive::Mainnet, "capella", "Withdrawal");
}
#[test]
fn capella_mainnet_bls_to_execution_change() {
    run_ssz_static_type::<capella::BLSToExecutionChange>(
        Archive::Mainnet,
        "capella",
        "BLSToExecutionChange",
    );
}
#[test]
fn capella_mainnet_signed_bls_to_execution_change() {
    run_ssz_static_type::<capella::SignedBLSToExecutionChange>(
        Archive::Mainnet,
        "capella",
        "SignedBLSToExecutionChange",
    );
}
#[test]
fn capella_mainnet_historical_summary() {
    run_ssz_static_type::<capella::HistoricalSummary>(
        Archive::Mainnet,
        "capella",
        "HistoricalSummary",
    );
}

// Modified in capella
#[test]
fn capella_mainnet_execution_payload() {
    run_ssz_static_type::<capella::ExecutionPayload>(
        Archive::Mainnet,
        "capella",
        "ExecutionPayload",
    );
}
#[test]
fn capella_mainnet_execution_payload_header() {
    run_ssz_static_type::<capella::ExecutionPayloadHeader>(
        Archive::Mainnet,
        "capella",
        "ExecutionPayloadHeader",
    );
}
#[test]
fn capella_mainnet_beacon_block() {
    run_ssz_static_type::<capella::BeaconBlock>(Archive::Mainnet, "capella", "BeaconBlock");
}
#[test]
fn capella_mainnet_beacon_block_body() {
    run_ssz_static_type::<capella::BeaconBlockBody>(Archive::Mainnet, "capella", "BeaconBlockBody");
}
#[test]
fn capella_mainnet_signed_beacon_block() {
    run_ssz_static_type::<capella::SignedBeaconBlock>(
        Archive::Mainnet,
        "capella",
        "SignedBeaconBlock",
    );
}
#[test]
fn capella_mainnet_beacon_state() {
    run_ssz_static_type::<capella::BeaconState>(Archive::Mainnet, "capella", "BeaconState");
}

// Light client (modified in capella)
#[test]
fn capella_mainnet_light_client_header() {
    run_ssz_static_type::<capella::LightClientHeader>(
        Archive::Mainnet,
        "capella",
        "LightClientHeader",
    );
}
#[test]
fn capella_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<capella::LightClientBootstrap>(
        Archive::Mainnet,
        "capella",
        "LightClientBootstrap",
    );
}
#[test]
fn capella_mainnet_light_client_update() {
    run_ssz_static_type::<capella::LightClientUpdate>(
        Archive::Mainnet,
        "capella",
        "LightClientUpdate",
    );
}
#[test]
fn capella_mainnet_light_client_finality_update() {
    run_ssz_static_type::<capella::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "capella",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn capella_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<capella::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "capella",
        "LightClientOptimisticUpdate",
    );
}

// ── Deneb mainnet ──

use spec_tests::types::deneb;

// Unchanged from capella
#[test]
fn deneb_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>(Archive::Mainnet, "deneb", "AggregateAndProof");
}
#[test]
fn deneb_mainnet_attestation() {
    run_ssz_static_type::<Attestation>(Archive::Mainnet, "deneb", "Attestation");
}
#[test]
fn deneb_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "deneb", "AttestationData");
}
#[test]
fn deneb_mainnet_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>(Archive::Mainnet, "deneb", "AttesterSlashing");
}
#[test]
fn deneb_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "deneb", "BeaconBlockHeader");
}
#[test]
fn deneb_mainnet_bls_to_execution_change() {
    run_ssz_static_type::<capella::BLSToExecutionChange>(
        Archive::Mainnet,
        "deneb",
        "BLSToExecutionChange",
    );
}
#[test]
fn deneb_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "deneb", "Checkpoint");
}
#[test]
fn deneb_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "deneb",
        "ContributionAndProof",
    );
}
#[test]
fn deneb_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "deneb", "Deposit");
}
#[test]
fn deneb_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "deneb", "DepositData");
}
#[test]
fn deneb_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "deneb", "DepositMessage");
}
#[test]
fn deneb_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "deneb", "Eth1Block");
}
#[test]
fn deneb_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "deneb", "Eth1Data");
}
#[test]
fn deneb_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "deneb", "Fork");
}
#[test]
fn deneb_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "deneb", "ForkData");
}
#[test]
fn deneb_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "deneb", "HistoricalBatch");
}
#[test]
fn deneb_mainnet_historical_summary() {
    run_ssz_static_type::<capella::HistoricalSummary>(
        Archive::Mainnet,
        "deneb",
        "HistoricalSummary",
    );
}
#[test]
fn deneb_mainnet_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>(Archive::Mainnet, "deneb", "IndexedAttestation");
}
#[test]
fn deneb_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "deneb", "PendingAttestation");
}
#[test]
fn deneb_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "deneb", "ProposerSlashing");
}
#[test]
fn deneb_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>(
        Archive::Mainnet,
        "deneb",
        "SignedAggregateAndProof",
    );
}
#[test]
fn deneb_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "deneb",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn deneb_mainnet_signed_bls_to_execution_change() {
    run_ssz_static_type::<capella::SignedBLSToExecutionChange>(
        Archive::Mainnet,
        "deneb",
        "SignedBLSToExecutionChange",
    );
}
#[test]
fn deneb_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "deneb",
        "SignedContributionAndProof",
    );
}
#[test]
fn deneb_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "deneb", "SignedVoluntaryExit");
}
#[test]
fn deneb_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "deneb", "SigningData");
}
#[test]
fn deneb_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "deneb", "SyncAggregate");
}
#[test]
fn deneb_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "deneb",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn deneb_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "deneb", "SyncCommittee");
}
#[test]
fn deneb_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "deneb",
        "SyncCommitteeContribution",
    );
}
#[test]
fn deneb_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "deneb",
        "SyncCommitteeMessage",
    );
}
#[test]
fn deneb_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "deneb", "Validator");
}
#[test]
fn deneb_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "deneb", "VoluntaryExit");
}
#[test]
fn deneb_mainnet_withdrawal() {
    run_ssz_static_type::<capella::Withdrawal>(Archive::Mainnet, "deneb", "Withdrawal");
}

// New in deneb
#[test]
fn deneb_mainnet_blob_identifier() {
    run_ssz_static_type::<deneb::BlobIdentifier>(Archive::Mainnet, "deneb", "BlobIdentifier");
}
#[test]
fn deneb_mainnet_blob_sidecar() {
    run_ssz_static_type::<deneb::BlobSidecar>(Archive::Mainnet, "deneb", "BlobSidecar");
}

// Modified in deneb
#[test]
fn deneb_mainnet_execution_payload() {
    run_ssz_static_type::<deneb::ExecutionPayload>(Archive::Mainnet, "deneb", "ExecutionPayload");
}
#[test]
fn deneb_mainnet_execution_payload_header() {
    run_ssz_static_type::<deneb::ExecutionPayloadHeader>(
        Archive::Mainnet,
        "deneb",
        "ExecutionPayloadHeader",
    );
}
#[test]
fn deneb_mainnet_beacon_block() {
    run_ssz_static_type::<deneb::BeaconBlock>(Archive::Mainnet, "deneb", "BeaconBlock");
}
#[test]
fn deneb_mainnet_beacon_block_body() {
    run_ssz_static_type::<deneb::BeaconBlockBody>(Archive::Mainnet, "deneb", "BeaconBlockBody");
}
#[test]
fn deneb_mainnet_signed_beacon_block() {
    run_ssz_static_type::<deneb::SignedBeaconBlock>(Archive::Mainnet, "deneb", "SignedBeaconBlock");
}
#[test]
fn deneb_mainnet_beacon_state() {
    run_ssz_static_type::<deneb::BeaconState>(Archive::Mainnet, "deneb", "BeaconState");
}

// Light client (modified in deneb)
#[test]
fn deneb_mainnet_light_client_header() {
    run_ssz_static_type::<deneb::LightClientHeader>(Archive::Mainnet, "deneb", "LightClientHeader");
}
#[test]
fn deneb_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<deneb::LightClientBootstrap>(
        Archive::Mainnet,
        "deneb",
        "LightClientBootstrap",
    );
}
#[test]
fn deneb_mainnet_light_client_update() {
    run_ssz_static_type::<deneb::LightClientUpdate>(Archive::Mainnet, "deneb", "LightClientUpdate");
}
#[test]
fn deneb_mainnet_light_client_finality_update() {
    run_ssz_static_type::<deneb::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "deneb",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn deneb_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<deneb::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "deneb",
        "LightClientOptimisticUpdate",
    );
}

// ── Electra mainnet ──

use spec_tests::types::electra;

// Unchanged
#[test]
fn electra_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "electra", "AttestationData");
}
#[test]
fn electra_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "electra", "BeaconBlockHeader");
}
#[test]
fn electra_mainnet_blob_identifier() {
    run_ssz_static_type::<deneb::BlobIdentifier>(Archive::Mainnet, "electra", "BlobIdentifier");
}
#[test]
fn electra_mainnet_blob_sidecar() {
    run_ssz_static_type::<deneb::BlobSidecar>(Archive::Mainnet, "electra", "BlobSidecar");
}
#[test]
fn electra_mainnet_bls_to_execution_change() {
    run_ssz_static_type::<capella::BLSToExecutionChange>(
        Archive::Mainnet,
        "electra",
        "BLSToExecutionChange",
    );
}
#[test]
fn electra_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "electra", "Checkpoint");
}
#[test]
fn electra_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "electra",
        "ContributionAndProof",
    );
}
#[test]
fn electra_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "electra", "Deposit");
}
#[test]
fn electra_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "electra", "DepositData");
}
#[test]
fn electra_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "electra", "DepositMessage");
}
#[test]
fn electra_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "electra", "Eth1Block");
}
#[test]
fn electra_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "electra", "Eth1Data");
}
#[test]
fn electra_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "electra", "Fork");
}
#[test]
fn electra_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "electra", "ForkData");
}
#[test]
fn electra_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "electra", "HistoricalBatch");
}
#[test]
fn electra_mainnet_historical_summary() {
    run_ssz_static_type::<capella::HistoricalSummary>(
        Archive::Mainnet,
        "electra",
        "HistoricalSummary",
    );
}
#[test]
fn electra_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "electra", "PendingAttestation");
}
#[test]
fn electra_mainnet_pow_block() {
    run_ssz_static_type::<bellatrix::PowBlock>(Archive::Mainnet, "electra", "PowBlock");
}
#[test]
fn electra_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "electra", "ProposerSlashing");
}
#[test]
fn electra_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "electra",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn electra_mainnet_signed_bls_to_execution_change() {
    run_ssz_static_type::<capella::SignedBLSToExecutionChange>(
        Archive::Mainnet,
        "electra",
        "SignedBLSToExecutionChange",
    );
}
#[test]
fn electra_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "electra",
        "SignedContributionAndProof",
    );
}
#[test]
fn electra_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "electra", "SignedVoluntaryExit");
}
#[test]
fn electra_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "electra", "SigningData");
}
#[test]
fn electra_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "electra", "SyncAggregate");
}
#[test]
fn electra_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "electra",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn electra_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "electra", "SyncCommittee");
}
#[test]
fn electra_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "electra",
        "SyncCommitteeContribution",
    );
}
#[test]
fn electra_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "electra",
        "SyncCommitteeMessage",
    );
}
#[test]
fn electra_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "electra", "Validator");
}
#[test]
fn electra_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "electra", "VoluntaryExit");
}
#[test]
fn electra_mainnet_withdrawal() {
    run_ssz_static_type::<capella::Withdrawal>(Archive::Mainnet, "electra", "Withdrawal");
}

// New in electra
#[test]
fn electra_mainnet_consolidation_request() {
    run_ssz_static_type::<electra::ConsolidationRequest>(
        Archive::Mainnet,
        "electra",
        "ConsolidationRequest",
    );
}
#[test]
fn electra_mainnet_deposit_request() {
    run_ssz_static_type::<electra::DepositRequest>(Archive::Mainnet, "electra", "DepositRequest");
}
#[test]
fn electra_mainnet_execution_requests() {
    run_ssz_static_type::<electra::ExecutionRequests>(
        Archive::Mainnet,
        "electra",
        "ExecutionRequests",
    );
}
#[test]
fn electra_mainnet_pending_consolidation() {
    run_ssz_static_type::<electra::PendingConsolidation>(
        Archive::Mainnet,
        "electra",
        "PendingConsolidation",
    );
}
#[test]
fn electra_mainnet_pending_deposit() {
    run_ssz_static_type::<electra::PendingDeposit>(Archive::Mainnet, "electra", "PendingDeposit");
}
#[test]
fn electra_mainnet_pending_partial_withdrawal() {
    run_ssz_static_type::<electra::PendingPartialWithdrawal>(
        Archive::Mainnet,
        "electra",
        "PendingPartialWithdrawal",
    );
}
#[test]
fn electra_mainnet_single_attestation() {
    run_ssz_static_type::<electra::SingleAttestation>(
        Archive::Mainnet,
        "electra",
        "SingleAttestation",
    );
}
#[test]
fn electra_mainnet_withdrawal_request() {
    run_ssz_static_type::<electra::WithdrawalRequest>(
        Archive::Mainnet,
        "electra",
        "WithdrawalRequest",
    );
}

// Modified in electra
#[test]
fn electra_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<electra::AggregateAndProof>(
        Archive::Mainnet,
        "electra",
        "AggregateAndProof",
    );
}
#[test]
fn electra_mainnet_attestation() {
    run_ssz_static_type::<electra::Attestation>(Archive::Mainnet, "electra", "Attestation");
}
#[test]
fn electra_mainnet_attester_slashing() {
    run_ssz_static_type::<electra::AttesterSlashing>(
        Archive::Mainnet,
        "electra",
        "AttesterSlashing",
    );
}
#[test]
fn electra_mainnet_indexed_attestation() {
    run_ssz_static_type::<electra::IndexedAttestation>(
        Archive::Mainnet,
        "electra",
        "IndexedAttestation",
    );
}
#[test]
fn electra_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<electra::SignedAggregateAndProof>(
        Archive::Mainnet,
        "electra",
        "SignedAggregateAndProof",
    );
}
#[test]
fn electra_mainnet_execution_payload() {
    run_ssz_static_type::<electra::ExecutionPayload>(
        Archive::Mainnet,
        "electra",
        "ExecutionPayload",
    );
}
#[test]
fn electra_mainnet_execution_payload_header() {
    run_ssz_static_type::<electra::ExecutionPayloadHeader>(
        Archive::Mainnet,
        "electra",
        "ExecutionPayloadHeader",
    );
}
#[test]
fn electra_mainnet_beacon_block() {
    run_ssz_static_type::<electra::BeaconBlock>(Archive::Mainnet, "electra", "BeaconBlock");
}
#[test]
fn electra_mainnet_beacon_block_body() {
    run_ssz_static_type::<electra::BeaconBlockBody>(Archive::Mainnet, "electra", "BeaconBlockBody");
}
#[test]
fn electra_mainnet_signed_beacon_block() {
    run_ssz_static_type::<electra::SignedBeaconBlock>(
        Archive::Mainnet,
        "electra",
        "SignedBeaconBlock",
    );
}
#[test]
fn electra_mainnet_beacon_state() {
    run_ssz_static_type::<electra::BeaconState>(Archive::Mainnet, "electra", "BeaconState");
}

// Light client
#[test]
fn electra_mainnet_light_client_header() {
    run_ssz_static_type::<electra::LightClientHeader>(
        Archive::Mainnet,
        "electra",
        "LightClientHeader",
    );
}
#[test]
fn electra_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<electra::LightClientBootstrap>(
        Archive::Mainnet,
        "electra",
        "LightClientBootstrap",
    );
}
#[test]
fn electra_mainnet_light_client_update() {
    run_ssz_static_type::<electra::LightClientUpdate>(
        Archive::Mainnet,
        "electra",
        "LightClientUpdate",
    );
}
#[test]
fn electra_mainnet_light_client_finality_update() {
    run_ssz_static_type::<electra::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "electra",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn electra_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<electra::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "electra",
        "LightClientOptimisticUpdate",
    );
}

// ── Fulu mainnet ──

use spec_tests::types::{fulu, fulu_beacon};

// Reuse electra types for unchanged ones
#[test]
fn fulu_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<electra::AggregateAndProof>(
        Archive::Mainnet,
        "fulu",
        "AggregateAndProof",
    );
}
#[test]
fn fulu_mainnet_attestation() {
    run_ssz_static_type::<electra::Attestation>(Archive::Mainnet, "fulu", "Attestation");
}
#[test]
fn fulu_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "fulu", "AttestationData");
}
#[test]
fn fulu_mainnet_attester_slashing() {
    run_ssz_static_type::<electra::AttesterSlashing>(Archive::Mainnet, "fulu", "AttesterSlashing");
}
#[test]
fn fulu_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "fulu", "BeaconBlockHeader");
}
#[test]
fn fulu_mainnet_blob_identifier() {
    run_ssz_static_type::<deneb::BlobIdentifier>(Archive::Mainnet, "fulu", "BlobIdentifier");
}
#[test]
fn fulu_mainnet_blob_sidecar() {
    run_ssz_static_type::<deneb::BlobSidecar>(Archive::Mainnet, "fulu", "BlobSidecar");
}
#[test]
fn fulu_mainnet_bls_to_execution_change() {
    run_ssz_static_type::<capella::BLSToExecutionChange>(
        Archive::Mainnet,
        "fulu",
        "BLSToExecutionChange",
    );
}
#[test]
fn fulu_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "fulu", "Checkpoint");
}
#[test]
fn fulu_mainnet_consolidation_request() {
    run_ssz_static_type::<electra::ConsolidationRequest>(
        Archive::Mainnet,
        "fulu",
        "ConsolidationRequest",
    );
}
#[test]
fn fulu_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "fulu",
        "ContributionAndProof",
    );
}
#[test]
fn fulu_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "fulu", "Deposit");
}
#[test]
fn fulu_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "fulu", "DepositData");
}
#[test]
fn fulu_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "fulu", "DepositMessage");
}
#[test]
fn fulu_mainnet_deposit_request() {
    run_ssz_static_type::<electra::DepositRequest>(Archive::Mainnet, "fulu", "DepositRequest");
}
#[test]
fn fulu_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "fulu", "Eth1Block");
}
#[test]
fn fulu_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "fulu", "Eth1Data");
}
#[test]
fn fulu_mainnet_execution_payload() {
    run_ssz_static_type::<electra::ExecutionPayload>(Archive::Mainnet, "fulu", "ExecutionPayload");
}
#[test]
fn fulu_mainnet_execution_payload_header() {
    run_ssz_static_type::<electra::ExecutionPayloadHeader>(
        Archive::Mainnet,
        "fulu",
        "ExecutionPayloadHeader",
    );
}
#[test]
fn fulu_mainnet_execution_requests() {
    run_ssz_static_type::<electra::ExecutionRequests>(
        Archive::Mainnet,
        "fulu",
        "ExecutionRequests",
    );
}
#[test]
fn fulu_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "fulu", "Fork");
}
#[test]
fn fulu_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "fulu", "ForkData");
}
#[test]
fn fulu_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "fulu", "HistoricalBatch");
}
#[test]
fn fulu_mainnet_historical_summary() {
    run_ssz_static_type::<capella::HistoricalSummary>(
        Archive::Mainnet,
        "fulu",
        "HistoricalSummary",
    );
}
#[test]
fn fulu_mainnet_indexed_attestation() {
    run_ssz_static_type::<electra::IndexedAttestation>(
        Archive::Mainnet,
        "fulu",
        "IndexedAttestation",
    );
}
#[test]
fn fulu_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "fulu", "PendingAttestation");
}
#[test]
fn fulu_mainnet_pending_consolidation() {
    run_ssz_static_type::<electra::PendingConsolidation>(
        Archive::Mainnet,
        "fulu",
        "PendingConsolidation",
    );
}
#[test]
fn fulu_mainnet_pending_deposit() {
    run_ssz_static_type::<electra::PendingDeposit>(Archive::Mainnet, "fulu", "PendingDeposit");
}
#[test]
fn fulu_mainnet_pending_partial_withdrawal() {
    run_ssz_static_type::<electra::PendingPartialWithdrawal>(
        Archive::Mainnet,
        "fulu",
        "PendingPartialWithdrawal",
    );
}
#[test]
fn fulu_mainnet_pow_block() {
    run_ssz_static_type::<bellatrix::PowBlock>(Archive::Mainnet, "fulu", "PowBlock");
}
#[test]
fn fulu_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "fulu", "ProposerSlashing");
}
#[test]
fn fulu_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<electra::SignedAggregateAndProof>(
        Archive::Mainnet,
        "fulu",
        "SignedAggregateAndProof",
    );
}
#[test]
fn fulu_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "fulu",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn fulu_mainnet_signed_bls_to_execution_change() {
    run_ssz_static_type::<capella::SignedBLSToExecutionChange>(
        Archive::Mainnet,
        "fulu",
        "SignedBLSToExecutionChange",
    );
}
#[test]
fn fulu_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "fulu",
        "SignedContributionAndProof",
    );
}
#[test]
fn fulu_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "fulu", "SignedVoluntaryExit");
}
#[test]
fn fulu_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "fulu", "SigningData");
}
#[test]
fn fulu_mainnet_single_attestation() {
    run_ssz_static_type::<electra::SingleAttestation>(
        Archive::Mainnet,
        "fulu",
        "SingleAttestation",
    );
}
#[test]
fn fulu_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "fulu", "SyncAggregate");
}
#[test]
fn fulu_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "fulu",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn fulu_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "fulu", "SyncCommittee");
}
#[test]
fn fulu_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "fulu",
        "SyncCommitteeContribution",
    );
}
#[test]
fn fulu_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "fulu",
        "SyncCommitteeMessage",
    );
}
#[test]
fn fulu_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "fulu", "Validator");
}
#[test]
fn fulu_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "fulu", "VoluntaryExit");
}
#[test]
fn fulu_mainnet_withdrawal() {
    run_ssz_static_type::<capella::Withdrawal>(Archive::Mainnet, "fulu", "Withdrawal");
}
#[test]
fn fulu_mainnet_withdrawal_request() {
    run_ssz_static_type::<electra::WithdrawalRequest>(
        Archive::Mainnet,
        "fulu",
        "WithdrawalRequest",
    );
}

// Reuse electra for block/light client (same structure in fulu)
#[test]
fn fulu_mainnet_beacon_block() {
    run_ssz_static_type::<electra::BeaconBlock>(Archive::Mainnet, "fulu", "BeaconBlock");
}
#[test]
fn fulu_mainnet_beacon_block_body() {
    run_ssz_static_type::<electra::BeaconBlockBody>(Archive::Mainnet, "fulu", "BeaconBlockBody");
}
#[test]
fn fulu_mainnet_signed_beacon_block() {
    run_ssz_static_type::<electra::SignedBeaconBlock>(
        Archive::Mainnet,
        "fulu",
        "SignedBeaconBlock",
    );
}
#[test]
fn fulu_mainnet_light_client_header() {
    run_ssz_static_type::<electra::LightClientHeader>(
        Archive::Mainnet,
        "fulu",
        "LightClientHeader",
    );
}
#[test]
fn fulu_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<electra::LightClientBootstrap>(
        Archive::Mainnet,
        "fulu",
        "LightClientBootstrap",
    );
}
#[test]
fn fulu_mainnet_light_client_update() {
    run_ssz_static_type::<electra::LightClientUpdate>(
        Archive::Mainnet,
        "fulu",
        "LightClientUpdate",
    );
}
#[test]
fn fulu_mainnet_light_client_finality_update() {
    run_ssz_static_type::<electra::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "fulu",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn fulu_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<electra::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "fulu",
        "LightClientOptimisticUpdate",
    );
}

// New in fulu
#[test]
fn fulu_mainnet_data_column_sidecar() {
    run_ssz_static_type::<fulu::DataColumnSidecar>(Archive::Mainnet, "fulu", "DataColumnSidecar");
}
#[test]
fn fulu_mainnet_data_columns_by_root_identifier() {
    run_ssz_static_type::<fulu::DataColumnsByRootIdentifier>(
        Archive::Mainnet,
        "fulu",
        "DataColumnsByRootIdentifier",
    );
}
#[test]
fn fulu_mainnet_matrix_entry() {
    run_ssz_static_type::<fulu::MatrixEntry>(Archive::Mainnet, "fulu", "MatrixEntry");
}

// Modified in fulu (BeaconState has proposer_lookahead field)
#[test]
fn fulu_mainnet_beacon_state() {
    run_ssz_static_type::<fulu_beacon::BeaconState>(Archive::Mainnet, "fulu", "BeaconState");
}

// ── Gloas mainnet ──

use spec_tests::types::gloas;

// Unchanged from fulu/electra
#[test]
fn gloas_mainnet_attestation() {
    run_ssz_static_type::<electra::Attestation>(Archive::Mainnet, "gloas", "Attestation");
}
#[test]
fn gloas_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "gloas", "AttestationData");
}
#[test]
fn gloas_mainnet_attester_slashing() {
    run_ssz_static_type::<electra::AttesterSlashing>(Archive::Mainnet, "gloas", "AttesterSlashing");
}
#[test]
fn gloas_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "gloas", "BeaconBlockHeader");
}
#[test]
fn gloas_mainnet_blob_identifier() {
    run_ssz_static_type::<deneb::BlobIdentifier>(Archive::Mainnet, "gloas", "BlobIdentifier");
}
#[test]
fn gloas_mainnet_blob_sidecar() {
    run_ssz_static_type::<deneb::BlobSidecar>(Archive::Mainnet, "gloas", "BlobSidecar");
}
#[test]
fn gloas_mainnet_bls_to_execution_change() {
    run_ssz_static_type::<capella::BLSToExecutionChange>(
        Archive::Mainnet,
        "gloas",
        "BLSToExecutionChange",
    );
}
#[test]
fn gloas_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "gloas", "Checkpoint");
}
#[test]
fn gloas_mainnet_consolidation_request() {
    run_ssz_static_type::<electra::ConsolidationRequest>(
        Archive::Mainnet,
        "gloas",
        "ConsolidationRequest",
    );
}
#[test]
fn gloas_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "gloas",
        "ContributionAndProof",
    );
}
#[test]
fn gloas_mainnet_data_column_sidecar() {
    run_ssz_static_type::<gloas::DataColumnSidecar>(Archive::Mainnet, "gloas", "DataColumnSidecar");
}
#[test]
fn gloas_mainnet_data_columns_by_root_identifier() {
    run_ssz_static_type::<fulu::DataColumnsByRootIdentifier>(
        Archive::Mainnet,
        "gloas",
        "DataColumnsByRootIdentifier",
    );
}
#[test]
fn gloas_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "gloas", "Deposit");
}
#[test]
fn gloas_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "gloas", "DepositData");
}
#[test]
fn gloas_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "gloas", "DepositMessage");
}
#[test]
fn gloas_mainnet_deposit_request() {
    run_ssz_static_type::<electra::DepositRequest>(Archive::Mainnet, "gloas", "DepositRequest");
}
#[test]
fn gloas_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "gloas", "Eth1Block");
}
#[test]
fn gloas_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "gloas", "Eth1Data");
}
#[test]
fn gloas_mainnet_execution_payload() {
    run_ssz_static_type::<electra::ExecutionPayload>(Archive::Mainnet, "gloas", "ExecutionPayload");
}
#[test]
fn gloas_mainnet_execution_payload_header() {
    run_ssz_static_type::<electra::ExecutionPayloadHeader>(
        Archive::Mainnet,
        "gloas",
        "ExecutionPayloadHeader",
    );
}
#[test]
fn gloas_mainnet_execution_requests() {
    run_ssz_static_type::<electra::ExecutionRequests>(
        Archive::Mainnet,
        "gloas",
        "ExecutionRequests",
    );
}
#[test]
fn gloas_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "gloas", "Fork");
}
#[test]
fn gloas_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "gloas", "ForkData");
}
#[test]
fn gloas_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "gloas", "HistoricalBatch");
}
#[test]
fn gloas_mainnet_historical_summary() {
    run_ssz_static_type::<capella::HistoricalSummary>(
        Archive::Mainnet,
        "gloas",
        "HistoricalSummary",
    );
}
#[test]
fn gloas_mainnet_indexed_attestation() {
    run_ssz_static_type::<electra::IndexedAttestation>(
        Archive::Mainnet,
        "gloas",
        "IndexedAttestation",
    );
}
#[test]
fn gloas_mainnet_matrix_entry() {
    run_ssz_static_type::<fulu::MatrixEntry>(Archive::Mainnet, "gloas", "MatrixEntry");
}
#[test]
fn gloas_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "gloas", "PendingAttestation");
}
#[test]
fn gloas_mainnet_pending_consolidation() {
    run_ssz_static_type::<electra::PendingConsolidation>(
        Archive::Mainnet,
        "gloas",
        "PendingConsolidation",
    );
}
#[test]
fn gloas_mainnet_pending_deposit() {
    run_ssz_static_type::<electra::PendingDeposit>(Archive::Mainnet, "gloas", "PendingDeposit");
}
#[test]
fn gloas_mainnet_pending_partial_withdrawal() {
    run_ssz_static_type::<electra::PendingPartialWithdrawal>(
        Archive::Mainnet,
        "gloas",
        "PendingPartialWithdrawal",
    );
}
#[test]
fn gloas_mainnet_pow_block() {
    run_ssz_static_type::<bellatrix::PowBlock>(Archive::Mainnet, "gloas", "PowBlock");
}
#[test]
fn gloas_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "gloas", "ProposerSlashing");
}
#[test]
fn gloas_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<electra::SignedAggregateAndProof>(
        Archive::Mainnet,
        "gloas",
        "SignedAggregateAndProof",
    );
}
#[test]
fn gloas_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "gloas",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn gloas_mainnet_signed_bls_to_execution_change() {
    run_ssz_static_type::<capella::SignedBLSToExecutionChange>(
        Archive::Mainnet,
        "gloas",
        "SignedBLSToExecutionChange",
    );
}
#[test]
fn gloas_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "gloas",
        "SignedContributionAndProof",
    );
}
#[test]
fn gloas_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "gloas", "SignedVoluntaryExit");
}
#[test]
fn gloas_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "gloas", "SigningData");
}
#[test]
fn gloas_mainnet_single_attestation() {
    run_ssz_static_type::<electra::SingleAttestation>(
        Archive::Mainnet,
        "gloas",
        "SingleAttestation",
    );
}
#[test]
fn gloas_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "gloas", "SyncAggregate");
}
#[test]
fn gloas_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "gloas",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn gloas_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "gloas", "SyncCommittee");
}
#[test]
fn gloas_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "gloas",
        "SyncCommitteeContribution",
    );
}
#[test]
fn gloas_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "gloas",
        "SyncCommitteeMessage",
    );
}
#[test]
fn gloas_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "gloas", "Validator");
}
#[test]
fn gloas_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "gloas", "VoluntaryExit");
}
#[test]
fn gloas_mainnet_withdrawal() {
    run_ssz_static_type::<capella::Withdrawal>(Archive::Mainnet, "gloas", "Withdrawal");
}
#[test]
fn gloas_mainnet_withdrawal_request() {
    run_ssz_static_type::<electra::WithdrawalRequest>(
        Archive::Mainnet,
        "gloas",
        "WithdrawalRequest",
    );
}
#[test]
fn gloas_mainnet_light_client_header() {
    run_ssz_static_type::<electra::LightClientHeader>(
        Archive::Mainnet,
        "gloas",
        "LightClientHeader",
    );
}
#[test]
fn gloas_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<electra::LightClientBootstrap>(
        Archive::Mainnet,
        "gloas",
        "LightClientBootstrap",
    );
}
#[test]
fn gloas_mainnet_light_client_update() {
    run_ssz_static_type::<electra::LightClientUpdate>(
        Archive::Mainnet,
        "gloas",
        "LightClientUpdate",
    );
}
#[test]
fn gloas_mainnet_light_client_finality_update() {
    run_ssz_static_type::<electra::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "gloas",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn gloas_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<electra::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "gloas",
        "LightClientOptimisticUpdate",
    );
}

// New in gloas
#[test]
fn gloas_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<electra::AggregateAndProof>(
        Archive::Mainnet,
        "gloas",
        "AggregateAndProof",
    );
}
#[test]
fn gloas_mainnet_builder_pending_payment() {
    run_ssz_static_type::<gloas::BuilderPendingPayment>(
        Archive::Mainnet,
        "gloas",
        "BuilderPendingPayment",
    );
}
#[test]
fn gloas_mainnet_builder_pending_withdrawal() {
    run_ssz_static_type::<gloas::BuilderPendingWithdrawal>(
        Archive::Mainnet,
        "gloas",
        "BuilderPendingWithdrawal",
    );
}
#[test]
fn gloas_mainnet_execution_payload_bid() {
    run_ssz_static_type::<gloas::ExecutionPayloadBid>(
        Archive::Mainnet,
        "gloas",
        "ExecutionPayloadBid",
    );
}
#[test]
fn gloas_mainnet_execution_payload_envelope() {
    run_ssz_static_type::<gloas::ExecutionPayloadEnvelope>(
        Archive::Mainnet,
        "gloas",
        "ExecutionPayloadEnvelope",
    );
}
#[test]
fn gloas_mainnet_fork_choice_node() {
    run_ssz_static_type::<gloas::ForkChoiceNode>(Archive::Mainnet, "gloas", "ForkChoiceNode");
}
#[test]
fn gloas_mainnet_indexed_payload_attestation() {
    run_ssz_static_type::<gloas::IndexedPayloadAttestation>(
        Archive::Mainnet,
        "gloas",
        "IndexedPayloadAttestation",
    );
}
#[test]
fn gloas_mainnet_payload_attestation() {
    run_ssz_static_type::<gloas::PayloadAttestation>(
        Archive::Mainnet,
        "gloas",
        "PayloadAttestation",
    );
}
#[test]
fn gloas_mainnet_payload_attestation_data() {
    run_ssz_static_type::<gloas::PayloadAttestationData>(
        Archive::Mainnet,
        "gloas",
        "PayloadAttestationData",
    );
}
#[test]
fn gloas_mainnet_payload_attestation_message() {
    run_ssz_static_type::<gloas::PayloadAttestationMessage>(
        Archive::Mainnet,
        "gloas",
        "PayloadAttestationMessage",
    );
}
#[test]
fn gloas_mainnet_signed_execution_payload_bid() {
    run_ssz_static_type::<gloas::SignedExecutionPayloadBid>(
        Archive::Mainnet,
        "gloas",
        "SignedExecutionPayloadBid",
    );
}
#[test]
fn gloas_mainnet_signed_execution_payload_envelope() {
    run_ssz_static_type::<gloas::SignedExecutionPayloadEnvelope>(
        Archive::Mainnet,
        "gloas",
        "SignedExecutionPayloadEnvelope",
    );
}

// Modified in gloas
#[test]
fn gloas_mainnet_beacon_block() {
    run_ssz_static_type::<gloas::BeaconBlock>(Archive::Mainnet, "gloas", "BeaconBlock");
}
#[test]
fn gloas_mainnet_beacon_block_body() {
    run_ssz_static_type::<gloas::BeaconBlockBody>(Archive::Mainnet, "gloas", "BeaconBlockBody");
}
#[test]
fn gloas_mainnet_signed_beacon_block() {
    run_ssz_static_type::<gloas::SignedBeaconBlock>(Archive::Mainnet, "gloas", "SignedBeaconBlock");
}
#[test]
fn gloas_mainnet_beacon_state() {
    run_ssz_static_type::<gloas::BeaconState>(Archive::Mainnet, "gloas", "BeaconState");
}

// ── EIP7805 mainnet ──

use spec_tests::types::eip7805;

// Reuse electra types for most
#[test]
fn eip7805_mainnet_aggregate_and_proof() {
    run_ssz_static_type::<electra::AggregateAndProof>(
        Archive::Mainnet,
        "eip7805",
        "AggregateAndProof",
    );
}
#[test]
fn eip7805_mainnet_attestation() {
    run_ssz_static_type::<electra::Attestation>(Archive::Mainnet, "eip7805", "Attestation");
}
#[test]
fn eip7805_mainnet_attestation_data() {
    run_ssz_static_type::<AttestationData>(Archive::Mainnet, "eip7805", "AttestationData");
}
#[test]
fn eip7805_mainnet_attester_slashing() {
    run_ssz_static_type::<electra::AttesterSlashing>(
        Archive::Mainnet,
        "eip7805",
        "AttesterSlashing",
    );
}
#[test]
fn eip7805_mainnet_beacon_block_header() {
    run_ssz_static_type::<BeaconBlockHeader>(Archive::Mainnet, "eip7805", "BeaconBlockHeader");
}
#[test]
fn eip7805_mainnet_beacon_block() {
    run_ssz_static_type::<electra::BeaconBlock>(Archive::Mainnet, "eip7805", "BeaconBlock");
}
#[test]
fn eip7805_mainnet_beacon_block_body() {
    run_ssz_static_type::<electra::BeaconBlockBody>(Archive::Mainnet, "eip7805", "BeaconBlockBody");
}
#[test]
fn eip7805_mainnet_beacon_state() {
    run_ssz_static_type::<fulu_beacon::BeaconState>(Archive::Mainnet, "eip7805", "BeaconState");
}
#[test]
fn eip7805_mainnet_blob_identifier() {
    run_ssz_static_type::<deneb::BlobIdentifier>(Archive::Mainnet, "eip7805", "BlobIdentifier");
}
#[test]
fn eip7805_mainnet_blob_sidecar() {
    run_ssz_static_type::<deneb::BlobSidecar>(Archive::Mainnet, "eip7805", "BlobSidecar");
}
#[test]
fn eip7805_mainnet_bls_to_execution_change() {
    run_ssz_static_type::<capella::BLSToExecutionChange>(
        Archive::Mainnet,
        "eip7805",
        "BLSToExecutionChange",
    );
}
#[test]
fn eip7805_mainnet_checkpoint() {
    run_ssz_static_type::<Checkpoint>(Archive::Mainnet, "eip7805", "Checkpoint");
}
#[test]
fn eip7805_mainnet_consolidation_request() {
    run_ssz_static_type::<electra::ConsolidationRequest>(
        Archive::Mainnet,
        "eip7805",
        "ConsolidationRequest",
    );
}
#[test]
fn eip7805_mainnet_contribution_and_proof() {
    run_ssz_static_type::<altair::ContributionAndProof>(
        Archive::Mainnet,
        "eip7805",
        "ContributionAndProof",
    );
}
#[test]
fn eip7805_mainnet_deposit() {
    run_ssz_static_type::<Deposit>(Archive::Mainnet, "eip7805", "Deposit");
}
#[test]
fn eip7805_mainnet_deposit_data() {
    run_ssz_static_type::<DepositData>(Archive::Mainnet, "eip7805", "DepositData");
}
#[test]
fn eip7805_mainnet_deposit_message() {
    run_ssz_static_type::<DepositMessage>(Archive::Mainnet, "eip7805", "DepositMessage");
}
#[test]
fn eip7805_mainnet_deposit_request() {
    run_ssz_static_type::<electra::DepositRequest>(Archive::Mainnet, "eip7805", "DepositRequest");
}
#[test]
fn eip7805_mainnet_eth1_block() {
    run_ssz_static_type::<Eth1Block>(Archive::Mainnet, "eip7805", "Eth1Block");
}
#[test]
fn eip7805_mainnet_eth1_data() {
    run_ssz_static_type::<Eth1Data>(Archive::Mainnet, "eip7805", "Eth1Data");
}
#[test]
fn eip7805_mainnet_execution_payload() {
    run_ssz_static_type::<electra::ExecutionPayload>(
        Archive::Mainnet,
        "eip7805",
        "ExecutionPayload",
    );
}
#[test]
fn eip7805_mainnet_execution_payload_header() {
    run_ssz_static_type::<electra::ExecutionPayloadHeader>(
        Archive::Mainnet,
        "eip7805",
        "ExecutionPayloadHeader",
    );
}
#[test]
fn eip7805_mainnet_execution_requests() {
    run_ssz_static_type::<electra::ExecutionRequests>(
        Archive::Mainnet,
        "eip7805",
        "ExecutionRequests",
    );
}
#[test]
fn eip7805_mainnet_fork() {
    run_ssz_static_type::<Fork>(Archive::Mainnet, "eip7805", "Fork");
}
#[test]
fn eip7805_mainnet_fork_data() {
    run_ssz_static_type::<ForkData>(Archive::Mainnet, "eip7805", "ForkData");
}
#[test]
fn eip7805_mainnet_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>(Archive::Mainnet, "eip7805", "HistoricalBatch");
}
#[test]
fn eip7805_mainnet_historical_summary() {
    run_ssz_static_type::<capella::HistoricalSummary>(
        Archive::Mainnet,
        "eip7805",
        "HistoricalSummary",
    );
}
#[test]
fn eip7805_mainnet_indexed_attestation() {
    run_ssz_static_type::<electra::IndexedAttestation>(
        Archive::Mainnet,
        "eip7805",
        "IndexedAttestation",
    );
}
#[test]
fn eip7805_mainnet_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>(Archive::Mainnet, "eip7805", "PendingAttestation");
}
#[test]
fn eip7805_mainnet_pending_consolidation() {
    run_ssz_static_type::<electra::PendingConsolidation>(
        Archive::Mainnet,
        "eip7805",
        "PendingConsolidation",
    );
}
#[test]
fn eip7805_mainnet_pending_deposit() {
    run_ssz_static_type::<electra::PendingDeposit>(Archive::Mainnet, "eip7805", "PendingDeposit");
}
#[test]
fn eip7805_mainnet_pending_partial_withdrawal() {
    run_ssz_static_type::<electra::PendingPartialWithdrawal>(
        Archive::Mainnet,
        "eip7805",
        "PendingPartialWithdrawal",
    );
}
#[test]
fn eip7805_mainnet_pow_block() {
    run_ssz_static_type::<bellatrix::PowBlock>(Archive::Mainnet, "eip7805", "PowBlock");
}
#[test]
fn eip7805_mainnet_proposer_slashing() {
    run_ssz_static_type::<ProposerSlashing>(Archive::Mainnet, "eip7805", "ProposerSlashing");
}
#[test]
fn eip7805_mainnet_signed_aggregate_and_proof() {
    run_ssz_static_type::<electra::SignedAggregateAndProof>(
        Archive::Mainnet,
        "eip7805",
        "SignedAggregateAndProof",
    );
}
#[test]
fn eip7805_mainnet_signed_beacon_block() {
    run_ssz_static_type::<electra::SignedBeaconBlock>(
        Archive::Mainnet,
        "eip7805",
        "SignedBeaconBlock",
    );
}
#[test]
fn eip7805_mainnet_signed_beacon_block_header() {
    run_ssz_static_type::<SignedBeaconBlockHeader>(
        Archive::Mainnet,
        "eip7805",
        "SignedBeaconBlockHeader",
    );
}
#[test]
fn eip7805_mainnet_signed_bls_to_execution_change() {
    run_ssz_static_type::<capella::SignedBLSToExecutionChange>(
        Archive::Mainnet,
        "eip7805",
        "SignedBLSToExecutionChange",
    );
}
#[test]
fn eip7805_mainnet_signed_contribution_and_proof() {
    run_ssz_static_type::<altair::SignedContributionAndProof>(
        Archive::Mainnet,
        "eip7805",
        "SignedContributionAndProof",
    );
}
#[test]
fn eip7805_mainnet_signed_voluntary_exit() {
    run_ssz_static_type::<SignedVoluntaryExit>(Archive::Mainnet, "eip7805", "SignedVoluntaryExit");
}
#[test]
fn eip7805_mainnet_signing_data() {
    run_ssz_static_type::<SigningData>(Archive::Mainnet, "eip7805", "SigningData");
}
#[test]
fn eip7805_mainnet_single_attestation() {
    run_ssz_static_type::<electra::SingleAttestation>(
        Archive::Mainnet,
        "eip7805",
        "SingleAttestation",
    );
}
#[test]
fn eip7805_mainnet_sync_aggregate() {
    run_ssz_static_type::<altair::SyncAggregate>(Archive::Mainnet, "eip7805", "SyncAggregate");
}
#[test]
fn eip7805_mainnet_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        Archive::Mainnet,
        "eip7805",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn eip7805_mainnet_sync_committee() {
    run_ssz_static_type::<altair::SyncCommittee>(Archive::Mainnet, "eip7805", "SyncCommittee");
}
#[test]
fn eip7805_mainnet_sync_committee_contribution() {
    run_ssz_static_type::<altair::SyncCommitteeContribution>(
        Archive::Mainnet,
        "eip7805",
        "SyncCommitteeContribution",
    );
}
#[test]
fn eip7805_mainnet_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>(
        Archive::Mainnet,
        "eip7805",
        "SyncCommitteeMessage",
    );
}
#[test]
fn eip7805_mainnet_validator() {
    run_ssz_static_type::<Validator>(Archive::Mainnet, "eip7805", "Validator");
}
#[test]
fn eip7805_mainnet_voluntary_exit() {
    run_ssz_static_type::<VoluntaryExit>(Archive::Mainnet, "eip7805", "VoluntaryExit");
}
#[test]
fn eip7805_mainnet_withdrawal() {
    run_ssz_static_type::<capella::Withdrawal>(Archive::Mainnet, "eip7805", "Withdrawal");
}
#[test]
fn eip7805_mainnet_withdrawal_request() {
    run_ssz_static_type::<electra::WithdrawalRequest>(
        Archive::Mainnet,
        "eip7805",
        "WithdrawalRequest",
    );
}
#[test]
fn eip7805_mainnet_light_client_header() {
    run_ssz_static_type::<electra::LightClientHeader>(
        Archive::Mainnet,
        "eip7805",
        "LightClientHeader",
    );
}
#[test]
fn eip7805_mainnet_light_client_bootstrap() {
    run_ssz_static_type::<electra::LightClientBootstrap>(
        Archive::Mainnet,
        "eip7805",
        "LightClientBootstrap",
    );
}
#[test]
fn eip7805_mainnet_light_client_update() {
    run_ssz_static_type::<electra::LightClientUpdate>(
        Archive::Mainnet,
        "eip7805",
        "LightClientUpdate",
    );
}
#[test]
fn eip7805_mainnet_light_client_finality_update() {
    run_ssz_static_type::<electra::LightClientFinalityUpdate>(
        Archive::Mainnet,
        "eip7805",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn eip7805_mainnet_light_client_optimistic_update() {
    run_ssz_static_type::<electra::LightClientOptimisticUpdate>(
        Archive::Mainnet,
        "eip7805",
        "LightClientOptimisticUpdate",
    );
}

// Fulu types also in eip7805
#[test]
fn eip7805_mainnet_data_column_sidecar() {
    run_ssz_static_type::<fulu::DataColumnSidecar>(
        Archive::Mainnet,
        "eip7805",
        "DataColumnSidecar",
    );
}
#[test]
fn eip7805_mainnet_data_columns_by_root_identifier() {
    run_ssz_static_type::<fulu::DataColumnsByRootIdentifier>(
        Archive::Mainnet,
        "eip7805",
        "DataColumnsByRootIdentifier",
    );
}
#[test]
fn eip7805_mainnet_matrix_entry() {
    run_ssz_static_type::<fulu::MatrixEntry>(Archive::Mainnet, "eip7805", "MatrixEntry");
}

// New in eip7805
#[test]
fn eip7805_mainnet_inclusion_list() {
    run_ssz_static_type::<eip7805::InclusionList>(Archive::Mainnet, "eip7805", "InclusionList");
}
#[test]
fn eip7805_mainnet_signed_inclusion_list() {
    run_ssz_static_type::<eip7805::SignedInclusionList>(
        Archive::Mainnet,
        "eip7805",
        "SignedInclusionList",
    );
}
