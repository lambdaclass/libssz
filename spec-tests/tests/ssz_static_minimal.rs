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

macro_rules! minimal_test {
    ($test_name:ident, $fork:literal, $type_name:literal, $rust_type:ty) => {
        #[test]
        fn $test_name() {
            run_ssz_static_type::<$rust_type>($fork, $type_name);
        }
    };
}

use spec_tests::types::minimal::*;
use spec_tests::types::phase0;

// Preset-independent types reused across ALL forks (same in mainnet and minimal)
macro_rules! preset_independent_tests {
    ($prefix:ident, $fork:literal) => {
        paste::paste! {
            minimal_test!([<$prefix _fork>], $fork, "Fork", phase0::Fork);
            minimal_test!([<$prefix _fork_data>], $fork, "ForkData", phase0::ForkData);
            minimal_test!([<$prefix _checkpoint>], $fork, "Checkpoint", phase0::Checkpoint);
            minimal_test!([<$prefix _validator>], $fork, "Validator", phase0::Validator);
            minimal_test!([<$prefix _attestation_data>], $fork, "AttestationData", phase0::AttestationData);
            minimal_test!([<$prefix _eth1_data>], $fork, "Eth1Data", phase0::Eth1Data);
            minimal_test!([<$prefix _eth1_block>], $fork, "Eth1Block", phase0::Eth1Block);
            minimal_test!([<$prefix _deposit_message>], $fork, "DepositMessage", phase0::DepositMessage);
            minimal_test!([<$prefix _deposit_data>], $fork, "DepositData", phase0::DepositData);
            minimal_test!([<$prefix _deposit>], $fork, "Deposit", phase0::Deposit);
            minimal_test!([<$prefix _beacon_block_header>], $fork, "BeaconBlockHeader", phase0::BeaconBlockHeader);
            minimal_test!([<$prefix _signed_beacon_block_header>], $fork, "SignedBeaconBlockHeader", phase0::SignedBeaconBlockHeader);
            minimal_test!([<$prefix _signing_data>], $fork, "SigningData", phase0::SigningData);
            minimal_test!([<$prefix _voluntary_exit>], $fork, "VoluntaryExit", phase0::VoluntaryExit);
            minimal_test!([<$prefix _signed_voluntary_exit>], $fork, "SignedVoluntaryExit", phase0::SignedVoluntaryExit);
            minimal_test!([<$prefix _proposer_slashing>], $fork, "ProposerSlashing", phase0::ProposerSlashing);
        }
    };
}

// ── Phase 0 minimal ──

preset_independent_tests!(phase0_minimal, "phase0");

minimal_test!(
    phase0_minimal_historical_batch,
    "phase0",
    "HistoricalBatch",
    HistoricalBatch
);
minimal_test!(
    phase0_minimal_indexed_attestation,
    "phase0",
    "IndexedAttestation",
    IndexedAttestation
);
minimal_test!(
    phase0_minimal_pending_attestation,
    "phase0",
    "PendingAttestation",
    PendingAttestation
);
minimal_test!(
    phase0_minimal_attestation,
    "phase0",
    "Attestation",
    Attestation
);
minimal_test!(
    phase0_minimal_attester_slashing,
    "phase0",
    "AttesterSlashing",
    AttesterSlashing
);
minimal_test!(
    phase0_minimal_aggregate_and_proof,
    "phase0",
    "AggregateAndProof",
    AggregateAndProof
);
minimal_test!(
    phase0_minimal_signed_aggregate_and_proof,
    "phase0",
    "SignedAggregateAndProof",
    SignedAggregateAndProof
);
minimal_test!(
    phase0_minimal_beacon_block_body,
    "phase0",
    "BeaconBlockBody",
    Phase0BeaconBlockBody
);
minimal_test!(
    phase0_minimal_beacon_block,
    "phase0",
    "BeaconBlock",
    Phase0BeaconBlock
);
minimal_test!(
    phase0_minimal_signed_beacon_block,
    "phase0",
    "SignedBeaconBlock",
    Phase0SignedBeaconBlock
);
minimal_test!(
    phase0_minimal_beacon_state,
    "phase0",
    "BeaconState",
    Phase0BeaconState
);

// ── Altair minimal ──

preset_independent_tests!(altair_minimal, "altair");

minimal_test!(
    altair_minimal_historical_batch,
    "altair",
    "HistoricalBatch",
    HistoricalBatch
);
minimal_test!(
    altair_minimal_indexed_attestation,
    "altair",
    "IndexedAttestation",
    IndexedAttestation
);
minimal_test!(
    altair_minimal_pending_attestation,
    "altair",
    "PendingAttestation",
    PendingAttestation
);
minimal_test!(
    altair_minimal_attestation,
    "altair",
    "Attestation",
    Attestation
);
minimal_test!(
    altair_minimal_attester_slashing,
    "altair",
    "AttesterSlashing",
    AttesterSlashing
);
minimal_test!(
    altair_minimal_aggregate_and_proof,
    "altair",
    "AggregateAndProof",
    AggregateAndProof
);
minimal_test!(
    altair_minimal_signed_aggregate_and_proof,
    "altair",
    "SignedAggregateAndProof",
    SignedAggregateAndProof
);

// Altair sync types (preset-dependent: SYNC_COMMITTEE_SIZE)
minimal_test!(
    altair_minimal_sync_aggregate,
    "altair",
    "SyncAggregate",
    SyncAggregate
);
minimal_test!(
    altair_minimal_sync_committee,
    "altair",
    "SyncCommittee",
    SyncCommittee
);
minimal_test!(
    altair_minimal_sync_committee_contribution,
    "altair",
    "SyncCommitteeContribution",
    SyncCommitteeContribution
);
minimal_test!(
    altair_minimal_contribution_and_proof,
    "altair",
    "ContributionAndProof",
    ContributionAndProof
);
minimal_test!(
    altair_minimal_signed_contribution_and_proof,
    "altair",
    "SignedContributionAndProof",
    SignedContributionAndProof
);

// Altair preset-independent sync types
use spec_tests::types::altair;
minimal_test!(
    altair_minimal_sync_committee_message,
    "altair",
    "SyncCommitteeMessage",
    altair::SyncCommitteeMessage
);
minimal_test!(
    altair_minimal_sync_aggregator_selection_data,
    "altair",
    "SyncAggregatorSelectionData",
    altair::SyncAggregatorSelectionData
);

// Altair light client
minimal_test!(
    altair_minimal_light_client_header,
    "altair",
    "LightClientHeader",
    AltairLightClientHeader
);
minimal_test!(
    altair_minimal_light_client_bootstrap,
    "altair",
    "LightClientBootstrap",
    AltairLightClientBootstrap
);
minimal_test!(
    altair_minimal_light_client_update,
    "altair",
    "LightClientUpdate",
    AltairLightClientUpdate
);
minimal_test!(
    altair_minimal_light_client_finality_update,
    "altair",
    "LightClientFinalityUpdate",
    AltairLightClientFinalityUpdate
);
minimal_test!(
    altair_minimal_light_client_optimistic_update,
    "altair",
    "LightClientOptimisticUpdate",
    AltairLightClientOptimisticUpdate
);

// Altair block/state
minimal_test!(
    altair_minimal_beacon_block_body,
    "altair",
    "BeaconBlockBody",
    AltairBeaconBlockBody
);
minimal_test!(
    altair_minimal_beacon_block,
    "altair",
    "BeaconBlock",
    AltairBeaconBlock
);
minimal_test!(
    altair_minimal_signed_beacon_block,
    "altair",
    "SignedBeaconBlock",
    AltairSignedBeaconBlock
);
minimal_test!(
    altair_minimal_beacon_state,
    "altair",
    "BeaconState",
    AltairBeaconState
);
