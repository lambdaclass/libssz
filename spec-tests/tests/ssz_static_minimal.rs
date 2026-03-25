use libssz::{SszDecode, SszEncode};
use libssz_merkle::HashTreeRoot;
use spec_tests::loader::{self, Archive};

fn check_roundtrip_root<T: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug>(
    ssz: &[u8],
    expected_root: &[u8; 32],
    case_name: &str,
) {
    let decoded =
        T::from_ssz_bytes(ssz).unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
    let reencoded = decoded.to_ssz();
    assert_eq!(reencoded, ssz, "{case_name}: roundtrip mismatch");
    let root = decoded.hash_tree_root(&libssz_merkle::Sha2Hasher);
    assert_eq!(root, *expected_root, "{case_name}: hash tree root mismatch");
}

fn run_ssz_static_type<T: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug>(
    fork: &str,
    type_name: &str,
) {
    let cases = loader::ssz_static_cases(Archive::Minimal, fork, type_name);
    assert!(!cases.is_empty(), "{fork}/{type_name}: no test cases found");
    for (case_path, case_name) in &cases {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let root_file = case_path.join("roots.yaml");
        let expected_root = loader::parse_root(&root_file);
        check_roundtrip_root::<T>(
            &ssz,
            &expected_root,
            &format!("minimal/{fork}/{type_name}/{case_name}"),
        );
    }
}

use spec_tests::types::minimal::*;
use spec_tests::types::phase0;

// Preset-independent types reused across ALL forks (same in mainnet and minimal)
// ── Phase 0 minimal ──

#[test]
fn phase0_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("phase0", "Fork");
}
#[test]
fn phase0_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("phase0", "ForkData");
}
#[test]
fn phase0_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("phase0", "Checkpoint");
}
#[test]
fn phase0_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("phase0", "Validator");
}
#[test]
fn phase0_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("phase0", "AttestationData");
}
#[test]
fn phase0_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("phase0", "Eth1Data");
}
#[test]
fn phase0_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("phase0", "Eth1Block");
}
#[test]
fn phase0_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("phase0", "DepositMessage");
}
#[test]
fn phase0_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("phase0", "DepositData");
}
#[test]
fn phase0_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("phase0", "Deposit");
}
#[test]
fn phase0_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("phase0", "BeaconBlockHeader");
}
#[test]
fn phase0_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("phase0", "SignedBeaconBlockHeader");
}
#[test]
fn phase0_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("phase0", "SigningData");
}
#[test]
fn phase0_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("phase0", "VoluntaryExit");
}
#[test]
fn phase0_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("phase0", "SignedVoluntaryExit");
}
#[test]
fn phase0_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("phase0", "ProposerSlashing");
}

#[test]
fn phase0_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("phase0", "HistoricalBatch");
}
#[test]
fn phase0_minimal_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>("phase0", "IndexedAttestation");
}
#[test]
fn phase0_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("phase0", "PendingAttestation");
}
#[test]
fn phase0_minimal_attestation() {
    run_ssz_static_type::<Attestation>("phase0", "Attestation");
}
#[test]
fn phase0_minimal_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>("phase0", "AttesterSlashing");
}
#[test]
fn phase0_minimal_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>("phase0", "AggregateAndProof");
}
#[test]
fn phase0_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>("phase0", "SignedAggregateAndProof");
}
#[test]
fn phase0_minimal_beacon_block_body() {
    run_ssz_static_type::<Phase0BeaconBlockBody>("phase0", "BeaconBlockBody");
}
#[test]
fn phase0_minimal_beacon_block() {
    run_ssz_static_type::<Phase0BeaconBlock>("phase0", "BeaconBlock");
}
#[test]
fn phase0_minimal_signed_beacon_block() {
    run_ssz_static_type::<Phase0SignedBeaconBlock>("phase0", "SignedBeaconBlock");
}
#[test]
fn phase0_minimal_beacon_state() {
    run_ssz_static_type::<Phase0BeaconState>("phase0", "BeaconState");
}

// ── Altair minimal ──

#[test]
fn altair_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("altair", "Fork");
}
#[test]
fn altair_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("altair", "ForkData");
}
#[test]
fn altair_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("altair", "Checkpoint");
}
#[test]
fn altair_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("altair", "Validator");
}
#[test]
fn altair_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("altair", "AttestationData");
}
#[test]
fn altair_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("altair", "Eth1Data");
}
#[test]
fn altair_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("altair", "Eth1Block");
}
#[test]
fn altair_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("altair", "DepositMessage");
}
#[test]
fn altair_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("altair", "DepositData");
}
#[test]
fn altair_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("altair", "Deposit");
}
#[test]
fn altair_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("altair", "BeaconBlockHeader");
}
#[test]
fn altair_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("altair", "SignedBeaconBlockHeader");
}
#[test]
fn altair_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("altair", "SigningData");
}
#[test]
fn altair_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("altair", "VoluntaryExit");
}
#[test]
fn altair_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("altair", "SignedVoluntaryExit");
}
#[test]
fn altair_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("altair", "ProposerSlashing");
}

#[test]
fn altair_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("altair", "HistoricalBatch");
}
#[test]
fn altair_minimal_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>("altair", "IndexedAttestation");
}
#[test]
fn altair_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("altair", "PendingAttestation");
}
#[test]
fn altair_minimal_attestation() {
    run_ssz_static_type::<Attestation>("altair", "Attestation");
}
#[test]
fn altair_minimal_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>("altair", "AttesterSlashing");
}
#[test]
fn altair_minimal_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>("altair", "AggregateAndProof");
}
#[test]
fn altair_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>("altair", "SignedAggregateAndProof");
}

// Altair sync types (preset-dependent: SYNC_COMMITTEE_SIZE)
#[test]
fn altair_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("altair", "SyncAggregate");
}
#[test]
fn altair_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("altair", "SyncCommittee");
}
#[test]
fn altair_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("altair", "SyncCommitteeContribution");
}
#[test]
fn altair_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("altair", "ContributionAndProof");
}
#[test]
fn altair_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("altair", "SignedContributionAndProof");
}

// Altair preset-independent sync types
use spec_tests::types::altair;
#[test]
fn altair_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("altair", "SyncCommitteeMessage");
}
#[test]
fn altair_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "altair",
        "SyncAggregatorSelectionData",
    );
}

// Altair light client
#[test]
fn altair_minimal_light_client_header() {
    run_ssz_static_type::<AltairLightClientHeader>("altair", "LightClientHeader");
}
#[test]
fn altair_minimal_light_client_bootstrap() {
    run_ssz_static_type::<AltairLightClientBootstrap>("altair", "LightClientBootstrap");
}
#[test]
fn altair_minimal_light_client_update() {
    run_ssz_static_type::<AltairLightClientUpdate>("altair", "LightClientUpdate");
}
#[test]
fn altair_minimal_light_client_finality_update() {
    run_ssz_static_type::<AltairLightClientFinalityUpdate>("altair", "LightClientFinalityUpdate");
}
#[test]
fn altair_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<AltairLightClientOptimisticUpdate>(
        "altair",
        "LightClientOptimisticUpdate",
    );
}

// Altair block/state
#[test]
fn altair_minimal_beacon_block_body() {
    run_ssz_static_type::<AltairBeaconBlockBody>("altair", "BeaconBlockBody");
}
#[test]
fn altair_minimal_beacon_block() {
    run_ssz_static_type::<AltairBeaconBlock>("altair", "BeaconBlock");
}
#[test]
fn altair_minimal_signed_beacon_block() {
    run_ssz_static_type::<AltairSignedBeaconBlock>("altair", "SignedBeaconBlock");
}
#[test]
fn altair_minimal_beacon_state() {
    run_ssz_static_type::<AltairBeaconState>("altair", "BeaconState");
}

// ── Bellatrix minimal ──
#[test]
fn bellatrix_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("bellatrix", "Fork");
}
#[test]
fn bellatrix_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("bellatrix", "ForkData");
}
#[test]
fn bellatrix_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("bellatrix", "Checkpoint");
}
#[test]
fn bellatrix_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("bellatrix", "Validator");
}
#[test]
fn bellatrix_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("bellatrix", "AttestationData");
}
#[test]
fn bellatrix_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("bellatrix", "Eth1Data");
}
#[test]
fn bellatrix_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("bellatrix", "Eth1Block");
}
#[test]
fn bellatrix_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("bellatrix", "DepositMessage");
}
#[test]
fn bellatrix_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("bellatrix", "DepositData");
}
#[test]
fn bellatrix_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("bellatrix", "Deposit");
}
#[test]
fn bellatrix_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("bellatrix", "BeaconBlockHeader");
}
#[test]
fn bellatrix_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("bellatrix", "SignedBeaconBlockHeader");
}
#[test]
fn bellatrix_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("bellatrix", "SigningData");
}
#[test]
fn bellatrix_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("bellatrix", "VoluntaryExit");
}
#[test]
fn bellatrix_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("bellatrix", "SignedVoluntaryExit");
}
#[test]
fn bellatrix_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("bellatrix", "ProposerSlashing");
}
#[test]
fn bellatrix_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("bellatrix", "HistoricalBatch");
}
#[test]
fn bellatrix_minimal_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>("bellatrix", "IndexedAttestation");
}
#[test]
fn bellatrix_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("bellatrix", "PendingAttestation");
}
#[test]
fn bellatrix_minimal_attestation() {
    run_ssz_static_type::<Attestation>("bellatrix", "Attestation");
}
#[test]
fn bellatrix_minimal_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>("bellatrix", "AttesterSlashing");
}
#[test]
fn bellatrix_minimal_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>("bellatrix", "AggregateAndProof");
}
#[test]
fn bellatrix_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>("bellatrix", "SignedAggregateAndProof");
}
#[test]
fn bellatrix_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("bellatrix", "SyncAggregate");
}
#[test]
fn bellatrix_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("bellatrix", "SyncCommittee");
}
#[test]
fn bellatrix_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("bellatrix", "SyncCommitteeContribution");
}
#[test]
fn bellatrix_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("bellatrix", "ContributionAndProof");
}
#[test]
fn bellatrix_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("bellatrix", "SignedContributionAndProof");
}
#[test]
fn bellatrix_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("bellatrix", "SyncCommitteeMessage");
}
#[test]
fn bellatrix_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "bellatrix",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn bellatrix_minimal_light_client_header() {
    run_ssz_static_type::<AltairLightClientHeader>("bellatrix", "LightClientHeader");
}
#[test]
fn bellatrix_minimal_light_client_bootstrap() {
    run_ssz_static_type::<AltairLightClientBootstrap>("bellatrix", "LightClientBootstrap");
}
#[test]
fn bellatrix_minimal_light_client_update() {
    run_ssz_static_type::<AltairLightClientUpdate>("bellatrix", "LightClientUpdate");
}
#[test]
fn bellatrix_minimal_light_client_finality_update() {
    run_ssz_static_type::<AltairLightClientFinalityUpdate>(
        "bellatrix",
        "LightClientFinalityUpdate",
    );
}
#[test]
fn bellatrix_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<AltairLightClientOptimisticUpdate>(
        "bellatrix",
        "LightClientOptimisticUpdate",
    );
}
#[test]
fn bellatrix_minimal_execution_payload() {
    run_ssz_static_type::<BellatrixExecutionPayload>("bellatrix", "ExecutionPayload");
}
#[test]
fn bellatrix_minimal_execution_payload_header() {
    run_ssz_static_type::<BellatrixExecutionPayloadHeader>("bellatrix", "ExecutionPayloadHeader");
}
#[test]
fn bellatrix_minimal_pow_block() {
    run_ssz_static_type::<PowBlock>("bellatrix", "PowBlock");
}
#[test]
fn bellatrix_minimal_beacon_block_body() {
    run_ssz_static_type::<BellatrixBeaconBlockBody>("bellatrix", "BeaconBlockBody");
}
#[test]
fn bellatrix_minimal_beacon_block() {
    run_ssz_static_type::<BellatrixBeaconBlock>("bellatrix", "BeaconBlock");
}
#[test]
fn bellatrix_minimal_signed_beacon_block() {
    run_ssz_static_type::<BellatrixSignedBeaconBlock>("bellatrix", "SignedBeaconBlock");
}
#[test]
fn bellatrix_minimal_beacon_state() {
    run_ssz_static_type::<BellatrixBeaconState>("bellatrix", "BeaconState");
}

// ── Capella minimal ──
#[test]
fn capella_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("capella", "Fork");
}
#[test]
fn capella_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("capella", "ForkData");
}
#[test]
fn capella_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("capella", "Checkpoint");
}
#[test]
fn capella_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("capella", "Validator");
}
#[test]
fn capella_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("capella", "AttestationData");
}
#[test]
fn capella_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("capella", "Eth1Data");
}
#[test]
fn capella_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("capella", "Eth1Block");
}
#[test]
fn capella_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("capella", "DepositMessage");
}
#[test]
fn capella_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("capella", "DepositData");
}
#[test]
fn capella_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("capella", "Deposit");
}
#[test]
fn capella_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("capella", "BeaconBlockHeader");
}
#[test]
fn capella_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("capella", "SignedBeaconBlockHeader");
}
#[test]
fn capella_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("capella", "SigningData");
}
#[test]
fn capella_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("capella", "VoluntaryExit");
}
#[test]
fn capella_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("capella", "SignedVoluntaryExit");
}
#[test]
fn capella_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("capella", "ProposerSlashing");
}
#[test]
fn capella_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("capella", "HistoricalBatch");
}
#[test]
fn capella_minimal_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>("capella", "IndexedAttestation");
}
#[test]
fn capella_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("capella", "PendingAttestation");
}
#[test]
fn capella_minimal_attestation() {
    run_ssz_static_type::<Attestation>("capella", "Attestation");
}
#[test]
fn capella_minimal_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>("capella", "AttesterSlashing");
}
#[test]
fn capella_minimal_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>("capella", "AggregateAndProof");
}
#[test]
fn capella_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>("capella", "SignedAggregateAndProof");
}
#[test]
fn capella_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("capella", "SyncAggregate");
}
#[test]
fn capella_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("capella", "SyncCommittee");
}
#[test]
fn capella_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("capella", "SyncCommitteeContribution");
}
#[test]
fn capella_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("capella", "ContributionAndProof");
}
#[test]
fn capella_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("capella", "SignedContributionAndProof");
}
#[test]
fn capella_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("capella", "SyncCommitteeMessage");
}
#[test]
fn capella_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "capella",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn capella_minimal_withdrawal() {
    run_ssz_static_type::<Withdrawal>("capella", "Withdrawal");
}
#[test]
fn capella_minimal_bls_to_execution_change() {
    run_ssz_static_type::<BLSToExecutionChange>("capella", "BLSToExecutionChange");
}
#[test]
fn capella_minimal_signed_bls_to_execution_change() {
    run_ssz_static_type::<SignedBLSToExecutionChange>("capella", "SignedBLSToExecutionChange");
}
#[test]
fn capella_minimal_historical_summary() {
    run_ssz_static_type::<HistoricalSummary>("capella", "HistoricalSummary");
}
#[test]
fn capella_minimal_execution_payload() {
    run_ssz_static_type::<CapellaExecutionPayload>("capella", "ExecutionPayload");
}
#[test]
fn capella_minimal_execution_payload_header() {
    run_ssz_static_type::<CapellaExecutionPayloadHeader>("capella", "ExecutionPayloadHeader");
}
#[test]
fn capella_minimal_light_client_header() {
    run_ssz_static_type::<CapellaLightClientHeader>("capella", "LightClientHeader");
}
#[test]
fn capella_minimal_light_client_bootstrap() {
    run_ssz_static_type::<CapellaLightClientBootstrap>("capella", "LightClientBootstrap");
}
#[test]
fn capella_minimal_light_client_update() {
    run_ssz_static_type::<CapellaLightClientUpdate>("capella", "LightClientUpdate");
}
#[test]
fn capella_minimal_light_client_finality_update() {
    run_ssz_static_type::<CapellaLightClientFinalityUpdate>("capella", "LightClientFinalityUpdate");
}
#[test]
fn capella_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<CapellaLightClientOptimisticUpdate>(
        "capella",
        "LightClientOptimisticUpdate",
    );
}
#[test]
fn capella_minimal_beacon_block_body() {
    run_ssz_static_type::<CapellaBeaconBlockBody>("capella", "BeaconBlockBody");
}
#[test]
fn capella_minimal_beacon_block() {
    run_ssz_static_type::<CapellaBeaconBlock>("capella", "BeaconBlock");
}
#[test]
fn capella_minimal_signed_beacon_block() {
    run_ssz_static_type::<CapellaSignedBeaconBlock>("capella", "SignedBeaconBlock");
}
#[test]
fn capella_minimal_beacon_state() {
    run_ssz_static_type::<CapellaBeaconState>("capella", "BeaconState");
}

// ── Deneb minimal ──
#[test]
fn deneb_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("deneb", "Fork");
}
#[test]
fn deneb_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("deneb", "ForkData");
}
#[test]
fn deneb_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("deneb", "Checkpoint");
}
#[test]
fn deneb_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("deneb", "Validator");
}
#[test]
fn deneb_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("deneb", "AttestationData");
}
#[test]
fn deneb_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("deneb", "Eth1Data");
}
#[test]
fn deneb_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("deneb", "Eth1Block");
}
#[test]
fn deneb_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("deneb", "DepositMessage");
}
#[test]
fn deneb_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("deneb", "DepositData");
}
#[test]
fn deneb_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("deneb", "Deposit");
}
#[test]
fn deneb_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("deneb", "BeaconBlockHeader");
}
#[test]
fn deneb_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("deneb", "SignedBeaconBlockHeader");
}
#[test]
fn deneb_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("deneb", "SigningData");
}
#[test]
fn deneb_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("deneb", "VoluntaryExit");
}
#[test]
fn deneb_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("deneb", "SignedVoluntaryExit");
}
#[test]
fn deneb_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("deneb", "ProposerSlashing");
}
#[test]
fn deneb_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("deneb", "HistoricalBatch");
}
#[test]
fn deneb_minimal_indexed_attestation() {
    run_ssz_static_type::<IndexedAttestation>("deneb", "IndexedAttestation");
}
#[test]
fn deneb_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("deneb", "PendingAttestation");
}
#[test]
fn deneb_minimal_attestation() {
    run_ssz_static_type::<Attestation>("deneb", "Attestation");
}
#[test]
fn deneb_minimal_attester_slashing() {
    run_ssz_static_type::<AttesterSlashing>("deneb", "AttesterSlashing");
}
#[test]
fn deneb_minimal_aggregate_and_proof() {
    run_ssz_static_type::<AggregateAndProof>("deneb", "AggregateAndProof");
}
#[test]
fn deneb_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<SignedAggregateAndProof>("deneb", "SignedAggregateAndProof");
}
#[test]
fn deneb_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("deneb", "SyncAggregate");
}
#[test]
fn deneb_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("deneb", "SyncCommittee");
}
#[test]
fn deneb_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("deneb", "SyncCommitteeContribution");
}
#[test]
fn deneb_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("deneb", "ContributionAndProof");
}
#[test]
fn deneb_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("deneb", "SignedContributionAndProof");
}
#[test]
fn deneb_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("deneb", "SyncCommitteeMessage");
}
#[test]
fn deneb_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "deneb",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn deneb_minimal_withdrawal() {
    run_ssz_static_type::<Withdrawal>("deneb", "Withdrawal");
}
#[test]
fn deneb_minimal_bls_to_execution_change() {
    run_ssz_static_type::<BLSToExecutionChange>("deneb", "BLSToExecutionChange");
}
#[test]
fn deneb_minimal_signed_bls_to_execution_change() {
    run_ssz_static_type::<SignedBLSToExecutionChange>("deneb", "SignedBLSToExecutionChange");
}
#[test]
fn deneb_minimal_historical_summary() {
    run_ssz_static_type::<HistoricalSummary>("deneb", "HistoricalSummary");
}
#[test]
fn deneb_minimal_blob_identifier() {
    run_ssz_static_type::<BlobIdentifier>("deneb", "BlobIdentifier");
}
#[test]
fn deneb_minimal_blob_sidecar() {
    run_ssz_static_type::<BlobSidecar>("deneb", "BlobSidecar");
}
#[test]
fn deneb_minimal_execution_payload() {
    run_ssz_static_type::<DenebExecutionPayload>("deneb", "ExecutionPayload");
}
#[test]
fn deneb_minimal_execution_payload_header() {
    run_ssz_static_type::<DenebExecutionPayloadHeader>("deneb", "ExecutionPayloadHeader");
}
#[test]
fn deneb_minimal_light_client_header() {
    run_ssz_static_type::<DenebLightClientHeader>("deneb", "LightClientHeader");
}
#[test]
fn deneb_minimal_light_client_bootstrap() {
    run_ssz_static_type::<DenebLightClientBootstrap>("deneb", "LightClientBootstrap");
}
#[test]
fn deneb_minimal_light_client_update() {
    run_ssz_static_type::<DenebLightClientUpdate>("deneb", "LightClientUpdate");
}
#[test]
fn deneb_minimal_light_client_finality_update() {
    run_ssz_static_type::<DenebLightClientFinalityUpdate>("deneb", "LightClientFinalityUpdate");
}
#[test]
fn deneb_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<DenebLightClientOptimisticUpdate>("deneb", "LightClientOptimisticUpdate");
}
#[test]
fn deneb_minimal_beacon_block_body() {
    run_ssz_static_type::<DenebBeaconBlockBody>("deneb", "BeaconBlockBody");
}
#[test]
fn deneb_minimal_beacon_block() {
    run_ssz_static_type::<DenebBeaconBlock>("deneb", "BeaconBlock");
}
#[test]
fn deneb_minimal_signed_beacon_block() {
    run_ssz_static_type::<DenebSignedBeaconBlock>("deneb", "SignedBeaconBlock");
}
#[test]
fn deneb_minimal_beacon_state() {
    run_ssz_static_type::<DenebBeaconState>("deneb", "BeaconState");
}

// ── Electra minimal ──
#[test]
fn electra_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("electra", "Fork");
}
#[test]
fn electra_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("electra", "ForkData");
}
#[test]
fn electra_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("electra", "Checkpoint");
}
#[test]
fn electra_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("electra", "Validator");
}
#[test]
fn electra_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("electra", "AttestationData");
}
#[test]
fn electra_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("electra", "Eth1Data");
}
#[test]
fn electra_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("electra", "Eth1Block");
}
#[test]
fn electra_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("electra", "DepositMessage");
}
#[test]
fn electra_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("electra", "DepositData");
}
#[test]
fn electra_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("electra", "Deposit");
}
#[test]
fn electra_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("electra", "BeaconBlockHeader");
}
#[test]
fn electra_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("electra", "SignedBeaconBlockHeader");
}
#[test]
fn electra_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("electra", "SigningData");
}
#[test]
fn electra_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("electra", "VoluntaryExit");
}
#[test]
fn electra_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("electra", "SignedVoluntaryExit");
}
#[test]
fn electra_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("electra", "ProposerSlashing");
}
#[test]
fn electra_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("electra", "HistoricalBatch");
}
#[test]
fn electra_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("electra", "PendingAttestation");
}
#[test]
fn electra_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("electra", "SyncAggregate");
}
#[test]
fn electra_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("electra", "SyncCommittee");
}
#[test]
fn electra_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("electra", "SyncCommitteeContribution");
}
#[test]
fn electra_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("electra", "ContributionAndProof");
}
#[test]
fn electra_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("electra", "SignedContributionAndProof");
}
#[test]
fn electra_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("electra", "SyncCommitteeMessage");
}
#[test]
fn electra_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "electra",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn electra_minimal_withdrawal() {
    run_ssz_static_type::<Withdrawal>("electra", "Withdrawal");
}
#[test]
fn electra_minimal_bls_to_execution_change() {
    run_ssz_static_type::<BLSToExecutionChange>("electra", "BLSToExecutionChange");
}
#[test]
fn electra_minimal_signed_bls_to_execution_change() {
    run_ssz_static_type::<SignedBLSToExecutionChange>("electra", "SignedBLSToExecutionChange");
}
#[test]
fn electra_minimal_historical_summary() {
    run_ssz_static_type::<HistoricalSummary>("electra", "HistoricalSummary");
}
#[test]
fn electra_minimal_blob_identifier() {
    run_ssz_static_type::<BlobIdentifier>("electra", "BlobIdentifier");
}
#[test]
fn electra_minimal_blob_sidecar() {
    run_ssz_static_type::<BlobSidecar>("electra", "BlobSidecar");
}
#[test]
fn electra_minimal_pow_block() {
    run_ssz_static_type::<PowBlock>("electra", "PowBlock");
}
#[test]
fn electra_minimal_consolidation_request() {
    run_ssz_static_type::<ConsolidationRequest>("electra", "ConsolidationRequest");
}
#[test]
fn electra_minimal_deposit_request() {
    run_ssz_static_type::<DepositRequest>("electra", "DepositRequest");
}
#[test]
fn electra_minimal_execution_requests() {
    run_ssz_static_type::<ExecutionRequests>("electra", "ExecutionRequests");
}
#[test]
fn electra_minimal_pending_consolidation() {
    run_ssz_static_type::<PendingConsolidation>("electra", "PendingConsolidation");
}
#[test]
fn electra_minimal_pending_deposit() {
    run_ssz_static_type::<PendingDeposit>("electra", "PendingDeposit");
}
#[test]
fn electra_minimal_pending_partial_withdrawal() {
    run_ssz_static_type::<PendingPartialWithdrawal>("electra", "PendingPartialWithdrawal");
}
#[test]
fn electra_minimal_single_attestation() {
    run_ssz_static_type::<SingleAttestation>("electra", "SingleAttestation");
}
#[test]
fn electra_minimal_withdrawal_request() {
    run_ssz_static_type::<WithdrawalRequest>("electra", "WithdrawalRequest");
}
#[test]
fn electra_minimal_attestation() {
    run_ssz_static_type::<ElectraAttestation>("electra", "Attestation");
}
#[test]
fn electra_minimal_indexed_attestation() {
    run_ssz_static_type::<ElectraIndexedAttestation>("electra", "IndexedAttestation");
}
#[test]
fn electra_minimal_attester_slashing() {
    run_ssz_static_type::<ElectraAttesterSlashing>("electra", "AttesterSlashing");
}
#[test]
fn electra_minimal_aggregate_and_proof() {
    run_ssz_static_type::<ElectraAggregateAndProof>("electra", "AggregateAndProof");
}
#[test]
fn electra_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<ElectraSignedAggregateAndProof>("electra", "SignedAggregateAndProof");
}
#[test]
fn electra_minimal_execution_payload() {
    run_ssz_static_type::<DenebExecutionPayload>("electra", "ExecutionPayload");
}
#[test]
fn electra_minimal_execution_payload_header() {
    run_ssz_static_type::<DenebExecutionPayloadHeader>("electra", "ExecutionPayloadHeader");
}
#[test]
fn electra_minimal_light_client_header() {
    run_ssz_static_type::<ElectraLightClientHeader>("electra", "LightClientHeader");
}
#[test]
fn electra_minimal_light_client_bootstrap() {
    run_ssz_static_type::<ElectraLightClientBootstrap>("electra", "LightClientBootstrap");
}
#[test]
fn electra_minimal_light_client_update() {
    run_ssz_static_type::<ElectraLightClientUpdate>("electra", "LightClientUpdate");
}
#[test]
fn electra_minimal_light_client_finality_update() {
    run_ssz_static_type::<ElectraLightClientFinalityUpdate>("electra", "LightClientFinalityUpdate");
}
#[test]
fn electra_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<ElectraLightClientOptimisticUpdate>(
        "electra",
        "LightClientOptimisticUpdate",
    );
}
#[test]
fn electra_minimal_beacon_block_body() {
    run_ssz_static_type::<ElectraBeaconBlockBody>("electra", "BeaconBlockBody");
}
#[test]
fn electra_minimal_beacon_block() {
    run_ssz_static_type::<ElectraBeaconBlock>("electra", "BeaconBlock");
}
#[test]
fn electra_minimal_signed_beacon_block() {
    run_ssz_static_type::<ElectraSignedBeaconBlock>("electra", "SignedBeaconBlock");
}
#[test]
fn electra_minimal_beacon_state() {
    run_ssz_static_type::<ElectraBeaconState>("electra", "BeaconState");
}

// ── Fulu minimal ──
// Same as electra but with DataColumn types and modified BeaconState
#[test]
fn fulu_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("fulu", "Fork");
}
#[test]
fn fulu_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("fulu", "ForkData");
}
#[test]
fn fulu_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("fulu", "Checkpoint");
}
#[test]
fn fulu_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("fulu", "Validator");
}
#[test]
fn fulu_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("fulu", "AttestationData");
}
#[test]
fn fulu_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("fulu", "Eth1Data");
}
#[test]
fn fulu_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("fulu", "Eth1Block");
}
#[test]
fn fulu_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("fulu", "DepositMessage");
}
#[test]
fn fulu_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("fulu", "DepositData");
}
#[test]
fn fulu_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("fulu", "Deposit");
}
#[test]
fn fulu_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("fulu", "BeaconBlockHeader");
}
#[test]
fn fulu_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("fulu", "SignedBeaconBlockHeader");
}
#[test]
fn fulu_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("fulu", "SigningData");
}
#[test]
fn fulu_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("fulu", "VoluntaryExit");
}
#[test]
fn fulu_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("fulu", "SignedVoluntaryExit");
}
#[test]
fn fulu_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("fulu", "ProposerSlashing");
}
#[test]
fn fulu_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("fulu", "HistoricalBatch");
}
#[test]
fn fulu_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("fulu", "PendingAttestation");
}
#[test]
fn fulu_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("fulu", "SyncAggregate");
}
#[test]
fn fulu_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("fulu", "SyncCommittee");
}
#[test]
fn fulu_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("fulu", "SyncCommitteeContribution");
}
#[test]
fn fulu_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("fulu", "ContributionAndProof");
}
#[test]
fn fulu_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("fulu", "SignedContributionAndProof");
}
#[test]
fn fulu_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("fulu", "SyncCommitteeMessage");
}
#[test]
fn fulu_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "fulu",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn fulu_minimal_withdrawal() {
    run_ssz_static_type::<Withdrawal>("fulu", "Withdrawal");
}
#[test]
fn fulu_minimal_bls_to_execution_change() {
    run_ssz_static_type::<BLSToExecutionChange>("fulu", "BLSToExecutionChange");
}
#[test]
fn fulu_minimal_signed_bls_to_execution_change() {
    run_ssz_static_type::<SignedBLSToExecutionChange>("fulu", "SignedBLSToExecutionChange");
}
#[test]
fn fulu_minimal_historical_summary() {
    run_ssz_static_type::<HistoricalSummary>("fulu", "HistoricalSummary");
}
#[test]
fn fulu_minimal_blob_identifier() {
    run_ssz_static_type::<BlobIdentifier>("fulu", "BlobIdentifier");
}
#[test]
fn fulu_minimal_blob_sidecar() {
    run_ssz_static_type::<BlobSidecar>("fulu", "BlobSidecar");
}
#[test]
fn fulu_minimal_pow_block() {
    run_ssz_static_type::<PowBlock>("fulu", "PowBlock");
}
#[test]
fn fulu_minimal_consolidation_request() {
    run_ssz_static_type::<ConsolidationRequest>("fulu", "ConsolidationRequest");
}
#[test]
fn fulu_minimal_deposit_request() {
    run_ssz_static_type::<DepositRequest>("fulu", "DepositRequest");
}
#[test]
fn fulu_minimal_execution_requests() {
    run_ssz_static_type::<ExecutionRequests>("fulu", "ExecutionRequests");
}
#[test]
fn fulu_minimal_pending_consolidation() {
    run_ssz_static_type::<PendingConsolidation>("fulu", "PendingConsolidation");
}
#[test]
fn fulu_minimal_pending_deposit() {
    run_ssz_static_type::<PendingDeposit>("fulu", "PendingDeposit");
}
#[test]
fn fulu_minimal_pending_partial_withdrawal() {
    run_ssz_static_type::<PendingPartialWithdrawal>("fulu", "PendingPartialWithdrawal");
}
#[test]
fn fulu_minimal_single_attestation() {
    run_ssz_static_type::<SingleAttestation>("fulu", "SingleAttestation");
}
#[test]
fn fulu_minimal_withdrawal_request() {
    run_ssz_static_type::<WithdrawalRequest>("fulu", "WithdrawalRequest");
}
#[test]
fn fulu_minimal_attestation() {
    run_ssz_static_type::<ElectraAttestation>("fulu", "Attestation");
}
#[test]
fn fulu_minimal_indexed_attestation() {
    run_ssz_static_type::<ElectraIndexedAttestation>("fulu", "IndexedAttestation");
}
#[test]
fn fulu_minimal_attester_slashing() {
    run_ssz_static_type::<ElectraAttesterSlashing>("fulu", "AttesterSlashing");
}
#[test]
fn fulu_minimal_aggregate_and_proof() {
    run_ssz_static_type::<ElectraAggregateAndProof>("fulu", "AggregateAndProof");
}
#[test]
fn fulu_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<ElectraSignedAggregateAndProof>("fulu", "SignedAggregateAndProof");
}
#[test]
fn fulu_minimal_execution_payload() {
    run_ssz_static_type::<DenebExecutionPayload>("fulu", "ExecutionPayload");
}
#[test]
fn fulu_minimal_execution_payload_header() {
    run_ssz_static_type::<DenebExecutionPayloadHeader>("fulu", "ExecutionPayloadHeader");
}
#[test]
fn fulu_minimal_light_client_header() {
    run_ssz_static_type::<ElectraLightClientHeader>("fulu", "LightClientHeader");
}
#[test]
fn fulu_minimal_light_client_bootstrap() {
    run_ssz_static_type::<ElectraLightClientBootstrap>("fulu", "LightClientBootstrap");
}
#[test]
fn fulu_minimal_light_client_update() {
    run_ssz_static_type::<ElectraLightClientUpdate>("fulu", "LightClientUpdate");
}
#[test]
fn fulu_minimal_light_client_finality_update() {
    run_ssz_static_type::<ElectraLightClientFinalityUpdate>("fulu", "LightClientFinalityUpdate");
}
#[test]
fn fulu_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<ElectraLightClientOptimisticUpdate>(
        "fulu",
        "LightClientOptimisticUpdate",
    );
}
#[test]
fn fulu_minimal_beacon_block_body() {
    run_ssz_static_type::<ElectraBeaconBlockBody>("fulu", "BeaconBlockBody");
}
#[test]
fn fulu_minimal_beacon_block() {
    run_ssz_static_type::<ElectraBeaconBlock>("fulu", "BeaconBlock");
}
#[test]
fn fulu_minimal_signed_beacon_block() {
    run_ssz_static_type::<ElectraSignedBeaconBlock>("fulu", "SignedBeaconBlock");
}
#[test]
fn fulu_minimal_data_column_sidecar() {
    run_ssz_static_type::<DataColumnSidecar>("fulu", "DataColumnSidecar");
}
#[test]
fn fulu_minimal_data_columns_by_root_identifier() {
    run_ssz_static_type::<DataColumnsByRootIdentifier>("fulu", "DataColumnsByRootIdentifier");
}
#[test]
fn fulu_minimal_matrix_entry() {
    run_ssz_static_type::<MatrixEntry>("fulu", "MatrixEntry");
}
#[test]
fn fulu_minimal_beacon_state() {
    run_ssz_static_type::<FuluBeaconState>("fulu", "BeaconState");
}

// ── Gloas minimal ──
#[test]
fn gloas_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("gloas", "Fork");
}
#[test]
fn gloas_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("gloas", "ForkData");
}
#[test]
fn gloas_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("gloas", "Checkpoint");
}
#[test]
fn gloas_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("gloas", "Validator");
}
#[test]
fn gloas_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("gloas", "AttestationData");
}
#[test]
fn gloas_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("gloas", "Eth1Data");
}
#[test]
fn gloas_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("gloas", "Eth1Block");
}
#[test]
fn gloas_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("gloas", "DepositMessage");
}
#[test]
fn gloas_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("gloas", "DepositData");
}
#[test]
fn gloas_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("gloas", "Deposit");
}
#[test]
fn gloas_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("gloas", "BeaconBlockHeader");
}
#[test]
fn gloas_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("gloas", "SignedBeaconBlockHeader");
}
#[test]
fn gloas_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("gloas", "SigningData");
}
#[test]
fn gloas_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("gloas", "VoluntaryExit");
}
#[test]
fn gloas_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("gloas", "SignedVoluntaryExit");
}
#[test]
fn gloas_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("gloas", "ProposerSlashing");
}
#[test]
fn gloas_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("gloas", "HistoricalBatch");
}
#[test]
fn gloas_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("gloas", "PendingAttestation");
}
#[test]
fn gloas_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("gloas", "SyncAggregate");
}
#[test]
fn gloas_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("gloas", "SyncCommittee");
}
#[test]
fn gloas_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("gloas", "SyncCommitteeContribution");
}
#[test]
fn gloas_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("gloas", "ContributionAndProof");
}
#[test]
fn gloas_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("gloas", "SignedContributionAndProof");
}
#[test]
fn gloas_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("gloas", "SyncCommitteeMessage");
}
#[test]
fn gloas_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "gloas",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn gloas_minimal_withdrawal() {
    run_ssz_static_type::<Withdrawal>("gloas", "Withdrawal");
}
#[test]
fn gloas_minimal_bls_to_execution_change() {
    run_ssz_static_type::<BLSToExecutionChange>("gloas", "BLSToExecutionChange");
}
#[test]
fn gloas_minimal_signed_bls_to_execution_change() {
    run_ssz_static_type::<SignedBLSToExecutionChange>("gloas", "SignedBLSToExecutionChange");
}
#[test]
fn gloas_minimal_historical_summary() {
    run_ssz_static_type::<HistoricalSummary>("gloas", "HistoricalSummary");
}
#[test]
fn gloas_minimal_blob_identifier() {
    run_ssz_static_type::<BlobIdentifier>("gloas", "BlobIdentifier");
}
#[test]
fn gloas_minimal_blob_sidecar() {
    run_ssz_static_type::<BlobSidecar>("gloas", "BlobSidecar");
}
#[test]
fn gloas_minimal_pow_block() {
    run_ssz_static_type::<PowBlock>("gloas", "PowBlock");
}
#[test]
fn gloas_minimal_consolidation_request() {
    run_ssz_static_type::<ConsolidationRequest>("gloas", "ConsolidationRequest");
}
#[test]
fn gloas_minimal_deposit_request() {
    run_ssz_static_type::<DepositRequest>("gloas", "DepositRequest");
}
#[test]
fn gloas_minimal_execution_requests() {
    run_ssz_static_type::<ExecutionRequests>("gloas", "ExecutionRequests");
}
#[test]
fn gloas_minimal_pending_consolidation() {
    run_ssz_static_type::<PendingConsolidation>("gloas", "PendingConsolidation");
}
#[test]
fn gloas_minimal_pending_deposit() {
    run_ssz_static_type::<PendingDeposit>("gloas", "PendingDeposit");
}
#[test]
fn gloas_minimal_pending_partial_withdrawal() {
    run_ssz_static_type::<PendingPartialWithdrawal>("gloas", "PendingPartialWithdrawal");
}
#[test]
fn gloas_minimal_single_attestation() {
    run_ssz_static_type::<SingleAttestation>("gloas", "SingleAttestation");
}
#[test]
fn gloas_minimal_withdrawal_request() {
    run_ssz_static_type::<WithdrawalRequest>("gloas", "WithdrawalRequest");
}
#[test]
fn gloas_minimal_attestation() {
    run_ssz_static_type::<ElectraAttestation>("gloas", "Attestation");
}
#[test]
fn gloas_minimal_indexed_attestation() {
    run_ssz_static_type::<ElectraIndexedAttestation>("gloas", "IndexedAttestation");
}
#[test]
fn gloas_minimal_attester_slashing() {
    run_ssz_static_type::<ElectraAttesterSlashing>("gloas", "AttesterSlashing");
}
#[test]
fn gloas_minimal_aggregate_and_proof() {
    run_ssz_static_type::<ElectraAggregateAndProof>("gloas", "AggregateAndProof");
}
#[test]
fn gloas_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<ElectraSignedAggregateAndProof>("gloas", "SignedAggregateAndProof");
}
#[test]
fn gloas_minimal_execution_payload() {
    run_ssz_static_type::<DenebExecutionPayload>("gloas", "ExecutionPayload");
}
#[test]
fn gloas_minimal_execution_payload_header() {
    run_ssz_static_type::<DenebExecutionPayloadHeader>("gloas", "ExecutionPayloadHeader");
}
#[test]
fn gloas_minimal_light_client_header() {
    run_ssz_static_type::<ElectraLightClientHeader>("gloas", "LightClientHeader");
}
#[test]
fn gloas_minimal_light_client_bootstrap() {
    run_ssz_static_type::<ElectraLightClientBootstrap>("gloas", "LightClientBootstrap");
}
#[test]
fn gloas_minimal_light_client_update() {
    run_ssz_static_type::<ElectraLightClientUpdate>("gloas", "LightClientUpdate");
}
#[test]
fn gloas_minimal_light_client_finality_update() {
    run_ssz_static_type::<ElectraLightClientFinalityUpdate>("gloas", "LightClientFinalityUpdate");
}
#[test]
fn gloas_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<ElectraLightClientOptimisticUpdate>(
        "gloas",
        "LightClientOptimisticUpdate",
    );
}
#[test]
fn gloas_minimal_data_columns_by_root_identifier() {
    run_ssz_static_type::<DataColumnsByRootIdentifier>("gloas", "DataColumnsByRootIdentifier");
}
#[test]
fn gloas_minimal_builder_pending_payment() {
    run_ssz_static_type::<BuilderPendingPayment>("gloas", "BuilderPendingPayment");
}
#[test]
fn gloas_minimal_builder_pending_withdrawal() {
    run_ssz_static_type::<BuilderPendingWithdrawal>("gloas", "BuilderPendingWithdrawal");
}
#[test]
fn gloas_minimal_execution_payload_bid() {
    run_ssz_static_type::<ExecutionPayloadBid>("gloas", "ExecutionPayloadBid");
}
#[test]
fn gloas_minimal_execution_payload_envelope() {
    run_ssz_static_type::<GloasExecutionPayloadEnvelope>("gloas", "ExecutionPayloadEnvelope");
}
#[test]
fn gloas_minimal_fork_choice_node() {
    run_ssz_static_type::<ForkChoiceNode>("gloas", "ForkChoiceNode");
}
#[test]
fn gloas_minimal_payload_attestation() {
    run_ssz_static_type::<GloasPayloadAttestation>("gloas", "PayloadAttestation");
}
#[test]
fn gloas_minimal_indexed_payload_attestation() {
    run_ssz_static_type::<GloasIndexedPayloadAttestation>("gloas", "IndexedPayloadAttestation");
}
#[test]
fn gloas_minimal_payload_attestation_data() {
    run_ssz_static_type::<PayloadAttestationData>("gloas", "PayloadAttestationData");
}
#[test]
fn gloas_minimal_payload_attestation_message() {
    run_ssz_static_type::<PayloadAttestationMessage>("gloas", "PayloadAttestationMessage");
}
#[test]
fn gloas_minimal_signed_execution_payload_bid() {
    run_ssz_static_type::<SignedExecutionPayloadBid>("gloas", "SignedExecutionPayloadBid");
}
#[test]
fn gloas_minimal_signed_execution_payload_envelope() {
    run_ssz_static_type::<GloasSignedExecutionPayloadEnvelope>(
        "gloas",
        "SignedExecutionPayloadEnvelope",
    );
}
#[test]
fn gloas_minimal_data_column_sidecar() {
    run_ssz_static_type::<GloasDataColumnSidecar>("gloas", "DataColumnSidecar");
}
#[test]
fn gloas_minimal_beacon_block_body() {
    run_ssz_static_type::<GloasBeaconBlockBody>("gloas", "BeaconBlockBody");
}
#[test]
fn gloas_minimal_beacon_block() {
    run_ssz_static_type::<GloasBeaconBlock>("gloas", "BeaconBlock");
}
#[test]
fn gloas_minimal_signed_beacon_block() {
    run_ssz_static_type::<GloasSignedBeaconBlock>("gloas", "SignedBeaconBlock");
}
#[test]
fn gloas_minimal_beacon_state() {
    run_ssz_static_type::<GloasBeaconState>("gloas", "BeaconState");
}

// ── EIP7805 minimal ──
#[test]
fn eip7805_minimal_fork() {
    run_ssz_static_type::<phase0::Fork>("eip7805", "Fork");
}
#[test]
fn eip7805_minimal_fork_data() {
    run_ssz_static_type::<phase0::ForkData>("eip7805", "ForkData");
}
#[test]
fn eip7805_minimal_checkpoint() {
    run_ssz_static_type::<phase0::Checkpoint>("eip7805", "Checkpoint");
}
#[test]
fn eip7805_minimal_validator() {
    run_ssz_static_type::<phase0::Validator>("eip7805", "Validator");
}
#[test]
fn eip7805_minimal_attestation_data() {
    run_ssz_static_type::<phase0::AttestationData>("eip7805", "AttestationData");
}
#[test]
fn eip7805_minimal_eth1_data() {
    run_ssz_static_type::<phase0::Eth1Data>("eip7805", "Eth1Data");
}
#[test]
fn eip7805_minimal_eth1_block() {
    run_ssz_static_type::<phase0::Eth1Block>("eip7805", "Eth1Block");
}
#[test]
fn eip7805_minimal_deposit_message() {
    run_ssz_static_type::<phase0::DepositMessage>("eip7805", "DepositMessage");
}
#[test]
fn eip7805_minimal_deposit_data() {
    run_ssz_static_type::<phase0::DepositData>("eip7805", "DepositData");
}
#[test]
fn eip7805_minimal_deposit() {
    run_ssz_static_type::<phase0::Deposit>("eip7805", "Deposit");
}
#[test]
fn eip7805_minimal_beacon_block_header() {
    run_ssz_static_type::<phase0::BeaconBlockHeader>("eip7805", "BeaconBlockHeader");
}
#[test]
fn eip7805_minimal_signed_beacon_block_header() {
    run_ssz_static_type::<phase0::SignedBeaconBlockHeader>("eip7805", "SignedBeaconBlockHeader");
}
#[test]
fn eip7805_minimal_signing_data() {
    run_ssz_static_type::<phase0::SigningData>("eip7805", "SigningData");
}
#[test]
fn eip7805_minimal_voluntary_exit() {
    run_ssz_static_type::<phase0::VoluntaryExit>("eip7805", "VoluntaryExit");
}
#[test]
fn eip7805_minimal_signed_voluntary_exit() {
    run_ssz_static_type::<phase0::SignedVoluntaryExit>("eip7805", "SignedVoluntaryExit");
}
#[test]
fn eip7805_minimal_proposer_slashing() {
    run_ssz_static_type::<phase0::ProposerSlashing>("eip7805", "ProposerSlashing");
}
#[test]
fn eip7805_minimal_historical_batch() {
    run_ssz_static_type::<HistoricalBatch>("eip7805", "HistoricalBatch");
}
#[test]
fn eip7805_minimal_pending_attestation() {
    run_ssz_static_type::<PendingAttestation>("eip7805", "PendingAttestation");
}
#[test]
fn eip7805_minimal_sync_aggregate() {
    run_ssz_static_type::<SyncAggregate>("eip7805", "SyncAggregate");
}
#[test]
fn eip7805_minimal_sync_committee() {
    run_ssz_static_type::<SyncCommittee>("eip7805", "SyncCommittee");
}
#[test]
fn eip7805_minimal_sync_committee_contribution() {
    run_ssz_static_type::<SyncCommitteeContribution>("eip7805", "SyncCommitteeContribution");
}
#[test]
fn eip7805_minimal_contribution_and_proof() {
    run_ssz_static_type::<ContributionAndProof>("eip7805", "ContributionAndProof");
}
#[test]
fn eip7805_minimal_signed_contribution_and_proof() {
    run_ssz_static_type::<SignedContributionAndProof>("eip7805", "SignedContributionAndProof");
}
#[test]
fn eip7805_minimal_sync_committee_message() {
    run_ssz_static_type::<altair::SyncCommitteeMessage>("eip7805", "SyncCommitteeMessage");
}
#[test]
fn eip7805_minimal_sync_aggregator_selection_data() {
    run_ssz_static_type::<altair::SyncAggregatorSelectionData>(
        "eip7805",
        "SyncAggregatorSelectionData",
    );
}
#[test]
fn eip7805_minimal_withdrawal() {
    run_ssz_static_type::<Withdrawal>("eip7805", "Withdrawal");
}
#[test]
fn eip7805_minimal_bls_to_execution_change() {
    run_ssz_static_type::<BLSToExecutionChange>("eip7805", "BLSToExecutionChange");
}
#[test]
fn eip7805_minimal_signed_bls_to_execution_change() {
    run_ssz_static_type::<SignedBLSToExecutionChange>("eip7805", "SignedBLSToExecutionChange");
}
#[test]
fn eip7805_minimal_historical_summary() {
    run_ssz_static_type::<HistoricalSummary>("eip7805", "HistoricalSummary");
}
#[test]
fn eip7805_minimal_blob_identifier() {
    run_ssz_static_type::<BlobIdentifier>("eip7805", "BlobIdentifier");
}
#[test]
fn eip7805_minimal_blob_sidecar() {
    run_ssz_static_type::<BlobSidecar>("eip7805", "BlobSidecar");
}
#[test]
fn eip7805_minimal_pow_block() {
    run_ssz_static_type::<PowBlock>("eip7805", "PowBlock");
}
#[test]
fn eip7805_minimal_consolidation_request() {
    run_ssz_static_type::<ConsolidationRequest>("eip7805", "ConsolidationRequest");
}
#[test]
fn eip7805_minimal_deposit_request() {
    run_ssz_static_type::<DepositRequest>("eip7805", "DepositRequest");
}
#[test]
fn eip7805_minimal_execution_requests() {
    run_ssz_static_type::<ExecutionRequests>("eip7805", "ExecutionRequests");
}
#[test]
fn eip7805_minimal_pending_consolidation() {
    run_ssz_static_type::<PendingConsolidation>("eip7805", "PendingConsolidation");
}
#[test]
fn eip7805_minimal_pending_deposit() {
    run_ssz_static_type::<PendingDeposit>("eip7805", "PendingDeposit");
}
#[test]
fn eip7805_minimal_pending_partial_withdrawal() {
    run_ssz_static_type::<PendingPartialWithdrawal>("eip7805", "PendingPartialWithdrawal");
}
#[test]
fn eip7805_minimal_single_attestation() {
    run_ssz_static_type::<SingleAttestation>("eip7805", "SingleAttestation");
}
#[test]
fn eip7805_minimal_withdrawal_request() {
    run_ssz_static_type::<WithdrawalRequest>("eip7805", "WithdrawalRequest");
}
#[test]
fn eip7805_minimal_attestation() {
    run_ssz_static_type::<ElectraAttestation>("eip7805", "Attestation");
}
#[test]
fn eip7805_minimal_indexed_attestation() {
    run_ssz_static_type::<ElectraIndexedAttestation>("eip7805", "IndexedAttestation");
}
#[test]
fn eip7805_minimal_attester_slashing() {
    run_ssz_static_type::<ElectraAttesterSlashing>("eip7805", "AttesterSlashing");
}
#[test]
fn eip7805_minimal_aggregate_and_proof() {
    run_ssz_static_type::<ElectraAggregateAndProof>("eip7805", "AggregateAndProof");
}
#[test]
fn eip7805_minimal_signed_aggregate_and_proof() {
    run_ssz_static_type::<ElectraSignedAggregateAndProof>("eip7805", "SignedAggregateAndProof");
}
#[test]
fn eip7805_minimal_execution_payload() {
    run_ssz_static_type::<DenebExecutionPayload>("eip7805", "ExecutionPayload");
}
#[test]
fn eip7805_minimal_execution_payload_header() {
    run_ssz_static_type::<DenebExecutionPayloadHeader>("eip7805", "ExecutionPayloadHeader");
}
#[test]
fn eip7805_minimal_light_client_header() {
    run_ssz_static_type::<ElectraLightClientHeader>("eip7805", "LightClientHeader");
}
#[test]
fn eip7805_minimal_light_client_bootstrap() {
    run_ssz_static_type::<ElectraLightClientBootstrap>("eip7805", "LightClientBootstrap");
}
#[test]
fn eip7805_minimal_light_client_update() {
    run_ssz_static_type::<ElectraLightClientUpdate>("eip7805", "LightClientUpdate");
}
#[test]
fn eip7805_minimal_light_client_finality_update() {
    run_ssz_static_type::<ElectraLightClientFinalityUpdate>("eip7805", "LightClientFinalityUpdate");
}
#[test]
fn eip7805_minimal_light_client_optimistic_update() {
    run_ssz_static_type::<ElectraLightClientOptimisticUpdate>(
        "eip7805",
        "LightClientOptimisticUpdate",
    );
}
#[test]
fn eip7805_minimal_beacon_block_body() {
    run_ssz_static_type::<ElectraBeaconBlockBody>("eip7805", "BeaconBlockBody");
}
#[test]
fn eip7805_minimal_beacon_block() {
    run_ssz_static_type::<ElectraBeaconBlock>("eip7805", "BeaconBlock");
}
#[test]
fn eip7805_minimal_signed_beacon_block() {
    run_ssz_static_type::<ElectraSignedBeaconBlock>("eip7805", "SignedBeaconBlock");
}
#[test]
fn eip7805_minimal_data_column_sidecar() {
    run_ssz_static_type::<DataColumnSidecar>("eip7805", "DataColumnSidecar");
}
#[test]
fn eip7805_minimal_data_columns_by_root_identifier() {
    run_ssz_static_type::<DataColumnsByRootIdentifier>("eip7805", "DataColumnsByRootIdentifier");
}
#[test]
fn eip7805_minimal_matrix_entry() {
    run_ssz_static_type::<MatrixEntry>("eip7805", "MatrixEntry");
}
#[test]
fn eip7805_minimal_inclusion_list() {
    run_ssz_static_type::<InclusionList>("eip7805", "InclusionList");
}
#[test]
fn eip7805_minimal_signed_inclusion_list() {
    run_ssz_static_type::<SignedInclusionList>("eip7805", "SignedInclusionList");
}
#[test]
fn eip7805_minimal_beacon_state() {
    run_ssz_static_type::<FuluBeaconState>("eip7805", "BeaconState");
}
