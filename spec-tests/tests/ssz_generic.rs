use spec_tests::loader;
use ssz::{SszDecode, SszEncode};
use ssz_merkle::HashTreeRoot;

// ── boolean ──

#[test]
fn boolean_valid() {
    for (case_path, case_name) in loader::ssz_generic_valid_cases("boolean") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));
        let yaml_value = loader::read_yaml_value(&case_path.join("value.yaml"));

        let expected: bool = match &yaml_value {
            serde_yaml::Value::Bool(b) => *b,
            serde_yaml::Value::String(s) => s == "true",
            other => panic!("{case_name}: unexpected YAML value: {other:?}"),
        };

        // Decode
        let decoded = bool::from_ssz_bytes(&ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded, expected, "{case_name}: decoded value mismatch");

        // Re-encode roundtrip
        let reencoded = decoded.to_ssz();
        assert_eq!(reencoded, ssz, "{case_name}: re-encoded bytes mismatch");

        // Hash tree root
        let root = decoded.hash_tree_root();
        assert_eq!(root, expected_root, "{case_name}: hash tree root mismatch");
    }
}

#[test]
fn boolean_invalid() {
    for (case_path, case_name) in loader::ssz_generic_invalid_cases("boolean") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));

        if let Ok(val) = bool::from_ssz_bytes(&ssz) {
            panic!("{case_name}: should have failed but decoded as {val}");
        }
    }
}

// ── uints ──

#[test]
fn uints_valid() {
    for (case_path, case_name) in loader::ssz_generic_valid_cases("uints") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));
        let yaml_value = loader::read_yaml_value(&case_path.join("value.yaml"));
        let yaml_str = match &yaml_value {
            serde_yaml::Value::Number(n) => n.to_string(),
            serde_yaml::Value::String(s) => s.clone(),
            other => panic!("{case_name}: unexpected YAML: {other:?}"),
        };

        // Parse bit width from case name: "uint_{bits}_{descriptor}"
        let bits = parse_uint_bits(&case_name);

        match bits {
            8 => check_uint::<u8>(&ssz, &yaml_str, &expected_root, &case_name),
            16 => check_uint::<u16>(&ssz, &yaml_str, &expected_root, &case_name),
            32 => check_uint::<u32>(&ssz, &yaml_str, &expected_root, &case_name),
            64 => check_uint::<u64>(&ssz, &yaml_str, &expected_root, &case_name),
            128 => check_uint::<u128>(&ssz, &yaml_str, &expected_root, &case_name),
            256 => check_uint_256(&ssz, &yaml_str, &expected_root, &case_name),
            _ => panic!("{case_name}: unsupported uint bit width: {bits}"),
        }
    }
}

#[test]
fn uints_invalid() {
    for (case_path, case_name) in loader::ssz_generic_invalid_cases("uints") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let bits = parse_uint_bits(&case_name);

        let result_is_err = match bits {
            8 => u8::from_ssz_bytes(&ssz).is_err(),
            16 => u16::from_ssz_bytes(&ssz).is_err(),
            32 => u32::from_ssz_bytes(&ssz).is_err(),
            64 => u64::from_ssz_bytes(&ssz).is_err(),
            128 => u128::from_ssz_bytes(&ssz).is_err(),
            256 => <[u8; 32]>::from_ssz_bytes(&ssz).is_err(),
            _ => panic!("{case_name}: unsupported uint bit width: {bits}"),
        };

        assert!(result_is_err, "{case_name}: should have failed to decode");
    }
}

fn parse_uint_bits(case_name: &str) -> u32 {
    // Case name format: "uint_{bits}_{descriptor}"
    let after_prefix = case_name.strip_prefix("uint_").unwrap_or(case_name);
    let bits_str = after_prefix.split('_').next().unwrap();
    bits_str.parse().unwrap()
}

trait UintTestable: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug + PartialEq {
    fn from_decimal(s: &str) -> Self;
}

impl UintTestable for u8 {
    fn from_decimal(s: &str) -> Self {
        s.parse().unwrap()
    }
}

impl UintTestable for u16 {
    fn from_decimal(s: &str) -> Self {
        s.parse().unwrap()
    }
}

impl UintTestable for u32 {
    fn from_decimal(s: &str) -> Self {
        s.parse().unwrap()
    }
}

impl UintTestable for u64 {
    fn from_decimal(s: &str) -> Self {
        s.parse().unwrap()
    }
}

impl UintTestable for u128 {
    fn from_decimal(s: &str) -> Self {
        s.parse().unwrap()
    }
}

fn check_uint<T: UintTestable>(
    ssz: &[u8],
    yaml_str: &str,
    expected_root: &[u8; 32],
    case_name: &str,
) {
    let expected = T::from_decimal(yaml_str);

    let decoded =
        T::from_ssz_bytes(ssz).unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
    assert_eq!(decoded, expected, "{case_name}: value mismatch");

    let reencoded = decoded.to_ssz();
    assert_eq!(reencoded, ssz, "{case_name}: roundtrip mismatch");

    let root = decoded.hash_tree_root();
    assert_eq!(&root, expected_root, "{case_name}: hash tree root mismatch");
}

/// u256 is represented as `[u8; 32]` in SSZ (32 bytes, little-endian).
/// The YAML value is a decimal string.
fn check_uint_256(ssz: &[u8], yaml_str: &str, expected_root: &[u8; 32], case_name: &str) {
    // Decode as [u8; 32]
    let decoded = <[u8; 32]>::from_ssz_bytes(ssz)
        .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));

    // Verify against YAML value: parse decimal string to u256 LE bytes
    let expected_bytes = decimal_to_u256_le(yaml_str);
    assert_eq!(decoded, expected_bytes, "{case_name}: value mismatch");

    // Roundtrip
    let reencoded = decoded.to_ssz();
    assert_eq!(reencoded, ssz, "{case_name}: roundtrip mismatch");

    // Hash tree root: for a basic type of 32 bytes, the root IS the value
    // (already chunk-sized, no padding needed)
    let root = decoded.hash_tree_root();
    assert_eq!(&root, expected_root, "{case_name}: hash tree root mismatch");
}

/// Convert a decimal string to 32-byte little-endian representation.
fn decimal_to_u256_le(s: &str) -> [u8; 32] {
    // Use simple big-integer division for arbitrary precision
    let mut digits: Vec<u8> = s.bytes().map(|b| b - b'0').collect();
    let mut result = [0u8; 32];

    for byte in &mut result {
        let mut remainder = 0u16;
        for digit in digits.iter_mut() {
            let val = remainder * 10 + (*digit as u16);
            *digit = (val / 256) as u8;
            remainder = val % 256;
        }
        *byte = remainder as u8;
        // Strip leading zeros for efficiency
        while digits.first() == Some(&0) && digits.len() > 1 {
            digits.remove(0);
        }
    }
    result
}

// ── basic_vector ──

/// Dispatch a runtime size to a const generic. Covers all sizes used across
/// basic_vector, bitlist, and bitvector test vectors.
macro_rules! dispatch_size {
    ($func:ident, $ssz:expr, $expected_root:expr, $case_name:expr, $n:expr) => {
        match $n {
            1 => $func::<1>($ssz, $expected_root, $case_name),
            2 => $func::<2>($ssz, $expected_root, $case_name),
            3 => $func::<3>($ssz, $expected_root, $case_name),
            4 => $func::<4>($ssz, $expected_root, $case_name),
            5 => $func::<5>($ssz, $expected_root, $case_name),
            6 => $func::<6>($ssz, $expected_root, $case_name),
            7 => $func::<7>($ssz, $expected_root, $case_name),
            8 => $func::<8>($ssz, $expected_root, $case_name),
            9 => $func::<9>($ssz, $expected_root, $case_name),
            15 => $func::<15>($ssz, $expected_root, $case_name),
            16 => $func::<16>($ssz, $expected_root, $case_name),
            17 => $func::<17>($ssz, $expected_root, $case_name),
            31 => $func::<31>($ssz, $expected_root, $case_name),
            32 => $func::<32>($ssz, $expected_root, $case_name),
            33 => $func::<33>($ssz, $expected_root, $case_name),
            64 => $func::<64>($ssz, $expected_root, $case_name),
            128 => $func::<128>($ssz, $expected_root, $case_name),
            256 => $func::<256>($ssz, $expected_root, $case_name),
            511 => $func::<511>($ssz, $expected_root, $case_name),
            512 => $func::<512>($ssz, $expected_root, $case_name),
            513 => $func::<513>($ssz, $expected_root, $case_name),
            1024 => $func::<1024>($ssz, $expected_root, $case_name),
            2048 => $func::<2048>($ssz, $expected_root, $case_name),
            4096 => $func::<4096>($ssz, $expected_root, $case_name),
            8192 => $func::<8192>($ssz, $expected_root, $case_name),
            other => panic!("{}: unsupported size: {}", $case_name, other),
        }
    };
}

#[test]
fn basic_vector_valid() {
    use ssz_types::SszVector;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("basic_vector") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));

        let (elem_type, length) = parse_basic_vector_case(&case_name);

        match elem_type {
            "bool" => dispatch_size!(check_vector_bool, &ssz, &expected_root, &case_name, length),
            "uint8" => dispatch_size!(check_vector_u8, &ssz, &expected_root, &case_name, length),
            "uint16" => dispatch_size!(check_vector_u16, &ssz, &expected_root, &case_name, length),
            "uint32" => dispatch_size!(check_vector_u32, &ssz, &expected_root, &case_name, length),
            "uint64" => dispatch_size!(check_vector_u64, &ssz, &expected_root, &case_name, length),
            "uint128" => {
                dispatch_size!(check_vector_u128, &ssz, &expected_root, &case_name, length)
            }
            "uint256" => {
                dispatch_size!(check_vector_u256, &ssz, &expected_root, &case_name, length)
            }
            _ => panic!("{case_name}: unsupported element type: {elem_type}"),
        }
    }

    fn check_vector_bool<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
        let decoded = SszVector::<bool, N>::from_ssz_bytes(ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(
            decoded.hash_tree_root(),
            *expected_root,
            "{case_name}: root"
        );
    }

    fn check_vector_u8<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
        let decoded = SszVector::<u8, N>::from_ssz_bytes(ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(
            decoded.hash_tree_root(),
            *expected_root,
            "{case_name}: root"
        );
    }

    fn check_vector_u16<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
        let decoded = SszVector::<u16, N>::from_ssz_bytes(ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(
            decoded.hash_tree_root(),
            *expected_root,
            "{case_name}: root"
        );
    }

    fn check_vector_u32<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
        let decoded = SszVector::<u32, N>::from_ssz_bytes(ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(
            decoded.hash_tree_root(),
            *expected_root,
            "{case_name}: root"
        );
    }

    fn check_vector_u64<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
        let decoded = SszVector::<u64, N>::from_ssz_bytes(ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(
            decoded.hash_tree_root(),
            *expected_root,
            "{case_name}: root"
        );
    }

    fn check_vector_u128<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
        let decoded = SszVector::<u128, N>::from_ssz_bytes(ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(
            decoded.hash_tree_root(),
            *expected_root,
            "{case_name}: root"
        );
    }

    fn check_vector_u256<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
        let decoded = SszVector::<[u8; 32], N>::from_ssz_bytes(ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(
            decoded.hash_tree_root(),
            *expected_root,
            "{case_name}: root"
        );
    }
}

#[test]
fn basic_vector_invalid() {
    use ssz_types::SszVector;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("basic_vector") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let (elem_type, length) = parse_basic_vector_case(&case_name);

        // Zero-length vectors are invalid by definition
        if length == 0 {
            continue;
        }

        fn fail_bool<const N: usize>(ssz: &[u8], _: &[u8; 32], cn: &str) {
            assert!(SszVector::<bool, N>::from_ssz_bytes(ssz).is_err(), "{cn}");
        }
        fn fail_u8<const N: usize>(ssz: &[u8], _: &[u8; 32], cn: &str) {
            assert!(SszVector::<u8, N>::from_ssz_bytes(ssz).is_err(), "{cn}");
        }
        fn fail_u16<const N: usize>(ssz: &[u8], _: &[u8; 32], cn: &str) {
            assert!(SszVector::<u16, N>::from_ssz_bytes(ssz).is_err(), "{cn}");
        }
        fn fail_u32<const N: usize>(ssz: &[u8], _: &[u8; 32], cn: &str) {
            assert!(SszVector::<u32, N>::from_ssz_bytes(ssz).is_err(), "{cn}");
        }
        fn fail_u64<const N: usize>(ssz: &[u8], _: &[u8; 32], cn: &str) {
            assert!(SszVector::<u64, N>::from_ssz_bytes(ssz).is_err(), "{cn}");
        }
        fn fail_u128<const N: usize>(ssz: &[u8], _: &[u8; 32], cn: &str) {
            assert!(SszVector::<u128, N>::from_ssz_bytes(ssz).is_err(), "{cn}");
        }
        fn fail_u256<const N: usize>(ssz: &[u8], _: &[u8; 32], cn: &str) {
            assert!(
                SszVector::<[u8; 32], N>::from_ssz_bytes(ssz).is_err(),
                "{cn}"
            );
        }

        let dummy = [0u8; 32];
        match elem_type {
            "bool" => dispatch_size!(fail_bool, &ssz, &dummy, &case_name, length),
            "uint8" => dispatch_size!(fail_u8, &ssz, &dummy, &case_name, length),
            "uint16" => dispatch_size!(fail_u16, &ssz, &dummy, &case_name, length),
            "uint32" => dispatch_size!(fail_u32, &ssz, &dummy, &case_name, length),
            "uint64" => dispatch_size!(fail_u64, &ssz, &dummy, &case_name, length),
            "uint128" => dispatch_size!(fail_u128, &ssz, &dummy, &case_name, length),
            "uint256" => dispatch_size!(fail_u256, &ssz, &dummy, &case_name, length),
            _ => panic!("{case_name}: unsupported element type: {elem_type}"),
        }
    }
}

/// Parse "vec_{type}_{length}_{descriptor}" → (element_type, length)
fn parse_basic_vector_case(case_name: &str) -> (&str, usize) {
    let rest = case_name.strip_prefix("vec_").unwrap_or(case_name);
    // Try longest type names first to avoid "uint1" matching "uint16"
    for type_name in &[
        "uint128", "uint256", "uint16", "uint32", "uint64", "uint8", "bool",
    ] {
        if let Some(after_type) = rest.strip_prefix(type_name) {
            let after_type = after_type.strip_prefix('_').unwrap_or(after_type);
            let length_str = after_type.split('_').next().unwrap();
            let length: usize = length_str.parse().unwrap();
            return (type_name, length);
        }
    }
    panic!("cannot parse basic_vector case name: {case_name}");
}

// ── bitlist ──

#[test]
fn bitlist_valid() {
    use ssz_types::SszBitlist;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("bitlist") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));
        let limit = parse_bitfield_param(&case_name, "bitlist_");

        fn check<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
            let decoded = SszBitlist::<N>::from_ssz_bytes(ssz)
                .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
            assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
            assert_eq!(
                decoded.hash_tree_root(),
                *expected_root,
                "{case_name}: root"
            );
        }

        dispatch_size!(check, &ssz, &expected_root, &case_name, limit);
    }
}

#[test]
fn bitlist_invalid() {
    use ssz_types::SszBitlist;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("bitlist") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let limit = parse_bitfield_param(&case_name, "bitlist_");

        fn check_fails<const N: usize>(ssz: &[u8], _: &[u8; 32], case_name: &str) {
            assert!(SszBitlist::<N>::from_ssz_bytes(ssz).is_err(), "{case_name}");
        }

        dispatch_size!(check_fails, &ssz, &[0u8; 32], &case_name, limit);
    }
}

// ── bitvector ──

#[test]
fn bitvector_valid() {
    use ssz_types::SszBitvector;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("bitvector") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));
        let length = parse_bitfield_param(&case_name, "bitvec_");

        fn check<const N: usize>(ssz: &[u8], expected_root: &[u8; 32], case_name: &str) {
            let decoded = SszBitvector::<N>::from_ssz_bytes(ssz)
                .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
            assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
            assert_eq!(
                decoded.hash_tree_root(),
                *expected_root,
                "{case_name}: root"
            );
        }

        dispatch_size!(check, &ssz, &expected_root, &case_name, length);
    }
}

#[test]
fn bitvector_invalid() {
    use ssz_types::SszBitvector;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("bitvector") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let length = parse_bitfield_param(&case_name, "bitvec_");

        // Zero-length bitvectors are invalid by definition
        if length == 0 {
            continue;
        }

        fn check_fails<const N: usize>(ssz: &[u8], _: &[u8; 32], case_name: &str) {
            assert!(
                SszBitvector::<N>::from_ssz_bytes(ssz).is_err(),
                "{case_name}"
            );
        }

        dispatch_size!(check_fails, &ssz, &[0u8; 32], &case_name, length);
    }
}

/// Parse "bitlist_{limit}_{desc}" or "bitvec_{length}_{desc}" → param value.
/// Handles "bitlist_no_limit_..." by returning 32 as a fallback.
fn parse_bitfield_param(case_name: &str, prefix: &str) -> usize {
    let rest = case_name.strip_prefix(prefix).unwrap_or(case_name);
    let first_part = rest.split('_').next().unwrap();
    // "no" appears in "bitlist_no_limit" test cases
    if first_part == "no" {
        return 32; // arbitrary fallback — these are "no limit" cases
    }
    first_part.parse().unwrap()
}

// ── containers ──

#[test]
fn containers_valid() {
    use spec_tests::types::containers::*;
    use spec_tests::types::progressive_containers as pc;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("containers") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));

        let struct_name = case_name.split('_').next().unwrap();
        match struct_name {
            "SingleFieldTestStruct" => {
                check_container::<SingleFieldTestStruct>(&ssz, &expected_root, &case_name)
            }
            "SmallTestStruct" => {
                check_container::<SmallTestStruct>(&ssz, &expected_root, &case_name)
            }
            "FixedTestStruct" => {
                check_container::<FixedTestStruct>(&ssz, &expected_root, &case_name)
            }
            "VarTestStruct" => check_container::<VarTestStruct>(&ssz, &expected_root, &case_name),
            "ComplexTestStruct" => {
                check_container::<ComplexTestStruct>(&ssz, &expected_root, &case_name)
            }
            "BitsStruct" => check_container::<BitsStruct>(&ssz, &expected_root, &case_name),
            "ProgressiveTestStruct" => {
                check_container::<pc::ProgressiveTestStruct>(&ssz, &expected_root, &case_name)
            }
            "ProgressiveBitsStruct" => {
                check_container::<pc::ProgressiveBitsStruct>(&ssz, &expected_root, &case_name)
            }
            other => panic!("{case_name}: unknown container: {other}"),
        }
    }
}

#[test]
fn containers_invalid() {
    use spec_tests::types::containers::*;
    use spec_tests::types::progressive_containers as pc;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("containers") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));

        let struct_name = case_name.split('_').next().unwrap();
        match struct_name {
            "SingleFieldTestStruct" => assert!(
                SingleFieldTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            ),
            "SmallTestStruct" => assert!(
                SmallTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            ),
            "FixedTestStruct" => assert!(
                FixedTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            ),
            "VarTestStruct" => assert!(VarTestStruct::from_ssz_bytes(&ssz).is_err(), "{case_name}"),
            "ComplexTestStruct" => assert!(
                ComplexTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            ),
            "BitsStruct" => assert!(BitsStruct::from_ssz_bytes(&ssz).is_err(), "{case_name}"),
            "ProgressiveTestStruct" => assert!(
                pc::ProgressiveTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            ),
            "ProgressiveBitsStruct" => assert!(
                pc::ProgressiveBitsStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            ),
            other => panic!("{case_name}: unknown container: {other}"),
        }
    }
}

fn check_container<T: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug>(
    ssz: &[u8],
    expected_root: &[u8; 32],
    case_name: &str,
) {
    let decoded =
        T::from_ssz_bytes(ssz).unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
    assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
    assert_eq!(
        &decoded.hash_tree_root(),
        expected_root,
        "{case_name}: root"
    );
}

// ── basic_progressive_list ──

#[test]
fn basic_progressive_list_valid() {
    use ssz_types::ProgressiveList;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("basic_progressive_list") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));

        let elem_type = parse_proglist_type(&case_name);

        match elem_type {
            "bool" => {
                check_roundtrip_root::<ProgressiveList<bool>>(&ssz, &expected_root, &case_name)
            }
            "uint8" => {
                check_roundtrip_root::<ProgressiveList<u8>>(&ssz, &expected_root, &case_name)
            }
            "uint16" => {
                check_roundtrip_root::<ProgressiveList<u16>>(&ssz, &expected_root, &case_name)
            }
            "uint32" => {
                check_roundtrip_root::<ProgressiveList<u32>>(&ssz, &expected_root, &case_name)
            }
            "uint64" => {
                check_roundtrip_root::<ProgressiveList<u64>>(&ssz, &expected_root, &case_name)
            }
            "uint128" => {
                check_roundtrip_root::<ProgressiveList<u128>>(&ssz, &expected_root, &case_name)
            }
            "uint256" => {
                check_roundtrip_root::<ProgressiveList<[u8; 32]>>(&ssz, &expected_root, &case_name)
            }
            _ => panic!("{case_name}: unsupported element type: {elem_type}"),
        }
    }
}

#[test]
fn basic_progressive_list_invalid() {
    use ssz_types::ProgressiveList;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("basic_progressive_list") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let elem_type = parse_proglist_type(&case_name);

        let fails = match elem_type {
            "bool" => ProgressiveList::<bool>::from_ssz_bytes(&ssz).is_err(),
            "uint8" => ProgressiveList::<u8>::from_ssz_bytes(&ssz).is_err(),
            "uint16" => ProgressiveList::<u16>::from_ssz_bytes(&ssz).is_err(),
            "uint32" => ProgressiveList::<u32>::from_ssz_bytes(&ssz).is_err(),
            "uint64" => ProgressiveList::<u64>::from_ssz_bytes(&ssz).is_err(),
            "uint128" => ProgressiveList::<u128>::from_ssz_bytes(&ssz).is_err(),
            "uint256" => ProgressiveList::<[u8; 32]>::from_ssz_bytes(&ssz).is_err(),
            _ => panic!("{case_name}: unsupported element type: {elem_type}"),
        };

        assert!(fails, "{case_name}: should have failed to decode");
    }
}

/// Parse "proglist_{type}_{descriptor}" → element type
fn parse_proglist_type(case_name: &str) -> &str {
    let rest = case_name.strip_prefix("proglist_").unwrap_or(case_name);
    for type_name in &[
        "uint128", "uint256", "uint16", "uint32", "uint64", "uint8", "bool",
    ] {
        if rest.starts_with(type_name) {
            return type_name;
        }
    }
    panic!("cannot parse progressive list case name: {case_name}");
}

fn check_roundtrip_root<T: SszDecode + SszEncode + HashTreeRoot + std::fmt::Debug>(
    ssz: &[u8],
    expected_root: &[u8; 32],
    case_name: &str,
) {
    let decoded =
        T::from_ssz_bytes(ssz).unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
    assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
    assert_eq!(
        decoded.hash_tree_root(),
        *expected_root,
        "{case_name}: root"
    );
}

// ── progressive_bitlist ──

#[test]
fn progressive_bitlist_valid() {
    use ssz_types::ProgressiveBitlist;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("progressive_bitlist") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));

        let decoded = ProgressiveBitlist::from_ssz_bytes(&ssz)
            .unwrap_or_else(|e| panic!("{case_name}: decode failed: {e:?}"));
        assert_eq!(decoded.to_ssz(), ssz, "{case_name}: roundtrip");
        assert_eq!(decoded.hash_tree_root(), expected_root, "{case_name}: root");
    }
}

#[test]
fn progressive_bitlist_invalid() {
    use ssz_types::ProgressiveBitlist;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("progressive_bitlist") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        assert!(
            ProgressiveBitlist::from_ssz_bytes(&ssz).is_err(),
            "{case_name}: should have failed to decode"
        );
    }
}

// ── progressive_containers ──

#[test]
fn progressive_containers_valid() {
    use spec_tests::types::progressive_containers::*;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("progressive_containers") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));

        let struct_name = case_name.split('_').next().unwrap();
        match struct_name {
            "ProgressiveSingleFieldContainerTestStruct" => check_container::<
                ProgressiveSingleFieldContainerTestStruct,
            >(
                &ssz, &expected_root, &case_name
            ),
            "ProgressiveSingleListContainerTestStruct" => check_container::<
                ProgressiveSingleListContainerTestStruct,
            >(
                &ssz, &expected_root, &case_name
            ),
            "ProgressiveVarTestStruct" => {
                check_container::<ProgressiveVarTestStruct>(&ssz, &expected_root, &case_name)
            }
            "ProgressiveComplexTestStruct" => {
                check_container::<ProgressiveComplexTestStruct>(&ssz, &expected_root, &case_name)
            }
            other => panic!("{case_name}: unknown progressive container: {other}"),
        }
    }
}

#[test]
fn progressive_containers_invalid() {
    use spec_tests::types::progressive_containers::*;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("progressive_containers") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));

        if case_name.starts_with("ProgressiveSingleFieldContainerTestStruct") {
            assert!(
                ProgressiveSingleFieldContainerTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            );
        } else if case_name.starts_with("ProgressiveSingleListContainerTestStruct") {
            assert!(
                ProgressiveSingleListContainerTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            );
        } else if case_name.starts_with("ProgressiveVarTestStruct") {
            assert!(
                ProgressiveVarTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            );
        } else if case_name.starts_with("ProgressiveComplexTestStruct") {
            assert!(
                ProgressiveComplexTestStruct::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            );
        } else {
            panic!("{case_name}: unknown progressive container");
        }
    }
}

// ── compatible_unions ──

#[test]
fn compatible_unions_valid() {
    use spec_tests::types::compatible_unions::*;

    for (case_path, case_name) in loader::ssz_generic_valid_cases("compatible_unions") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));
        let expected_root = loader::parse_root(&case_path.join("meta.yaml"));

        if case_name.starts_with("CompatibleUnionABCA") {
            check_container::<CompatibleUnionABCA>(&ssz, &expected_root, &case_name);
        } else if case_name.starts_with("CompatibleUnionBC") {
            check_container::<CompatibleUnionBC>(&ssz, &expected_root, &case_name);
        } else if case_name.starts_with("CompatibleUnionA") {
            check_container::<CompatibleUnionA>(&ssz, &expected_root, &case_name);
        } else {
            panic!("{case_name}: unknown compatible union type");
        }
    }
}

#[test]
fn compatible_unions_invalid() {
    use spec_tests::types::compatible_unions::*;

    for (case_path, case_name) in loader::ssz_generic_invalid_cases("compatible_unions") {
        let ssz = loader::read_ssz_snappy(&case_path.join("serialized.ssz_snappy"));

        if case_name.starts_with("CompatibleUnionABCA") {
            assert!(
                CompatibleUnionABCA::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            );
        } else if case_name.starts_with("CompatibleUnionBC") {
            assert!(
                CompatibleUnionBC::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            );
        } else if case_name.starts_with("CompatibleUnionA") {
            assert!(
                CompatibleUnionA::from_ssz_bytes(&ssz).is_err(),
                "{case_name}"
            );
        } else {
            panic!("{case_name}: unknown compatible union type");
        }
    }
}
