//! Runner for the `ethereum/ssz-specs` test vectors.
//!
//! These vectors are published separately from the consensus-specs ones and use
//! a different layout: one JSON fixture per case, holding the encoding and root
//! as hex rather than a directory of snappy-compressed and YAML files. Decode
//! failures also live alongside the valid cases instead of in an `invalid/`
//! tree, tagged with a `rejectionReason`.
//!
//! Each fixture group gets one test that dispatches on the fixture's `typeName`,
//! so a type name the runner does not know about fails loudly rather than being
//! silently skipped.

use libssz::{SszDecode, SszEncode};
use libssz_merkle::HashTreeRoot;
use libssz_types::{ProgressiveBitlist, SszBitlist, SszBitvector, SszList, SszVector};
use spec_tests::loader::{self, SszSpecsCase};
use spec_tests::types::ssz_specs::{
    compatible_unions as cu, progressive_containers as pc, progressive_types as pt,
};

/// Check one case: a valid case must round-trip and match its root, a
/// decode-failure case must be rejected.
fn check<T: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug>(case: &SszSpecsCase) {
    let name = &case.name;

    if case.is_rejection() {
        let reason = case.rejection_reason.as_deref().unwrap_or("unknown");
        if let Ok(value) = T::from_ssz_bytes(&case.input_bytes()) {
            panic!("{name}: should have been rejected ({reason}) but decoded as {value:?}");
        }
        return;
    }

    let ssz = case.serialized_bytes();
    let decoded =
        T::from_ssz_bytes(&ssz).unwrap_or_else(|e| panic!("{name}: decode failed: {e:?}"));

    let reencoded = decoded.to_ssz();
    assert_eq!(reencoded, ssz, "{name}: re-encoded bytes mismatch");

    let root = decoded.hash_tree_root(&libssz_merkle::Sha2Hasher);
    assert_eq!(
        root,
        case.expected_root(),
        "{name}: hash tree root mismatch"
    );
}

/// Run every case in a fixture group through `dispatch`.
fn run_group(group: &str, expected_cases: usize, dispatch: fn(&SszSpecsCase)) {
    let cases = loader::ssz_specs_cases(group);
    assert_eq!(
        cases.len(),
        expected_cases,
        "{group}: case count changed since v0.1.0"
    );
    for case in &cases {
        dispatch(case);
    }
}

#[test]
fn basic_types() {
    run_group("test_basic_types", 59, |case| {
        match case.type_name.as_str() {
            "Boolean" => check::<bool>(case),
            "Uint8" => check::<u8>(case),
            "Uint16" => check::<u16>(case),
            "Uint32" => check::<u32>(case),
            "Uint64" => check::<u64>(case),
            "Uint128" => check::<u128>(case),
            // uint256 has no primitive counterpart; a 32-byte vector of bytes
            // encodes and merkleizes identically.
            "Uint256" => check::<[u8; 32]>(case),
            "Bytes4" => check::<[u8; 4]>(case),
            "Bytes32" => check::<[u8; 32]>(case),
            "Bytes52" => check::<[u8; 52]>(case),
            "Bytes64" => check::<[u8; 64]>(case),
            "ByteList512KiB" => check::<SszList<u8, { 512 * 1024 }>>(case),
            "SampleBitVector8" => check::<SszBitvector<8>>(case),
            "SampleBitVector64" => check::<SszBitvector<64>>(case),
            "SampleBitList16" => check::<SszBitlist<16>>(case),
            "SampleUint16Vector3" => check::<SszVector<u16, 3>>(case),
            "SampleUint64Vector4" => check::<SszVector<u64, 4>>(case),
            "SampleUint32List16" => check::<SszList<u32, 16>>(case),
            "SampleBytes32List8" => check::<SszList<[u8; 32], 8>>(case),
            other => panic!("{}: unhandled type {other}", case.name),
        }
    });
}

#[test]
fn merkleization_boundaries() {
    run_group("test_merkleization_boundaries", 8, |case| {
        match case.type_name.as_str() {
            "BoundaryBitVector1" => check::<SszBitvector<1>>(case),
            "BoundaryBitVector7" => check::<SszBitvector<7>>(case),
            "BoundaryBitVector9" => check::<SszBitvector<9>>(case),
            "BoundaryBitVector255" => check::<SszBitvector<255>>(case),
            "BoundaryBitVector256" => check::<SszBitvector<256>>(case),
            "BoundaryBitVector257" => check::<SszBitvector<257>>(case),
            "BoundaryBitList256" => check::<SszBitlist<256>>(case),
            "BoundaryUint64List32" => check::<SszList<u64, 32>>(case),
            other => panic!("{}: unhandled type {other}", case.name),
        }
    });
}

#[test]
fn progressive_types() {
    run_group("test_progressive_types", 18, |case| {
        match case.type_name.as_str() {
            "ProgressiveBitList" => check::<ProgressiveBitlist>(case),
            "SampleUint64ProgressiveList" => check::<pt::SampleUint64ProgressiveList>(case),
            "SampleBytes32ProgressiveList" => check::<pt::SampleBytes32ProgressiveList>(case),
            "SampleNestedProgressiveList" => check::<pt::SampleNestedProgressiveList>(case),
            "SampleContainerWithProgressiveList" => {
                check::<pt::SampleContainerWithProgressiveList>(case)
            }
            other => panic!("{}: unhandled type {other}", case.name),
        }
    });
}

#[test]
fn progressive_containers() {
    run_group("test_progressive_containers", 15, |case| {
        match case.type_name.as_str() {
            "SampleSquare" => check::<pc::SampleSquare>(case),
            "SampleCircle" => check::<pc::SampleCircle>(case),
            "SampleOneField" => check::<pc::SampleOneField>(case),
            "SampleLeadingGaps" => check::<pc::SampleLeadingGaps>(case),
            "SampleMultipleGaps" => check::<pc::SampleMultipleGaps>(case),
            "SampleWidestLayout" => check::<pc::SampleWidestLayout>(case),
            "SampleLevelBoundary" => check::<pc::SampleLevelBoundary>(case),
            "SampleBoundedListField" => check::<pc::SampleBoundedListField>(case),
            "SampleProgressiveFields" => check::<pc::SampleProgressiveFields>(case),
            "SampleInnerShape" => check::<pc::SampleInnerShape>(case),
            "SampleOuterShape" => check::<pc::SampleOuterShape>(case),
            "SampleSquareProgressiveList" => check::<pc::SampleSquareProgressiveList>(case),
            "SampleShapeContainer" => check::<pc::SampleShapeContainer>(case),
            other => panic!("{}: unhandled type {other}", case.name),
        }
    });
}

#[test]
fn compatible_unions() {
    run_group("test_compatible_unions", 16, |case| {
        match case.type_name.as_str() {
            "SampleShape" => check::<cu::SampleShape>(case),
            "SampleNumbers" => check::<cu::SampleNumbers>(case),
            "SampleEmptyProne" => check::<cu::SampleEmptyProne>(case),
            "SampleSquareOnly" => check::<cu::SampleSquareOnly>(case),
            "SampleNestedShape" => check::<cu::SampleNestedShape>(case),
            "SampleShapeContainer" => check::<cu::SampleShapeContainer>(case),
            "SampleShapeProgressiveContainer" => check::<cu::SampleShapeProgressiveContainer>(case),
            "SampleShapeProgressiveList" => check::<cu::SampleShapeProgressiveList>(case),
            other => panic!("{}: unhandled type {other}", case.name),
        }
    });
}

#[test]
fn decode_failure_smoke() {
    run_group("test_decode_failure_smoke", 1, |case| {
        match case.type_name.as_str() {
            "SmokeBitList8" => check::<SszBitlist<8>>(case),
            other => panic!("{}: unhandled type {other}", case.name),
        }
    });
}

/// Every fixture group the release ships must have a test above. A new group in
/// a future release fails here instead of going unnoticed.
#[test]
fn all_fixture_groups_covered() {
    const COVERED: &[&str] = &[
        "test_basic_types",
        "test_compatible_unions",
        "test_decode_failure_smoke",
        "test_merkleization_boundaries",
        "test_progressive_containers",
        "test_progressive_types",
    ];

    let fixtures_dir = loader::ssz_specs_dir()
        .join("fixtures")
        .join("ssz")
        .join("ssz");
    let mut found: Vec<String> = std::fs::read_dir(&fixtures_dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {}", fixtures_dir.display(), e))
        .filter_map(|entry| entry.ok())
        .filter(|entry| entry.file_type().is_ok_and(|t| t.is_dir()))
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect();
    found.sort();

    assert_eq!(found, COVERED, "fixture groups changed since v0.1.0");
}
