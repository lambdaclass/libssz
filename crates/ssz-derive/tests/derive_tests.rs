use libssz::{DecodeError, SszDecode, SszEncode};
use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_merkle::{HashTreeRoot, Sha2Hasher};
// ── All-fixed struct ──

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct FixedStruct {
    a: u32,
    b: u64,
    c: bool,
}

#[test]
fn fixed_struct_encode() {
    let s = FixedStruct {
        a: 42,
        b: 100,
        c: true,
    };
    let encoded = s.to_ssz();
    // 4 + 8 + 1 = 13 bytes
    assert_eq!(encoded.len(), 13);
    assert_eq!(&encoded[0..4], &42u32.to_le_bytes());
    assert_eq!(&encoded[4..12], &100u64.to_le_bytes());
    assert_eq!(encoded[12], 1);
}

#[test]
fn fixed_struct_decode_round_trip() {
    let original = FixedStruct {
        a: 42,
        b: 100,
        c: true,
    };
    let encoded = original.to_ssz();
    let decoded = FixedStruct::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

#[test]
fn fixed_struct_is_fixed_size() {
    assert!(<FixedStruct as SszEncode>::is_fixed_size());
    assert_eq!(<FixedStruct as SszEncode>::fixed_size(), 13);
}

// ── Mixed fixed/variable struct ──

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct MixedStruct {
    a: u32,
    b: Vec<u8>,
    c: u16,
}

#[test]
fn mixed_struct_encode() {
    let s = MixedStruct {
        a: 7,
        b: vec![0xAA, 0xBB],
        c: 999,
    };
    let encoded = s.to_ssz();

    // Fixed part: 4 (u32) + 4 (offset) + 2 (u16) = 10
    // Variable part: [0xAA, 0xBB] = 2
    assert_eq!(encoded.len(), 12);

    // a = 7
    assert_eq!(&encoded[0..4], &7u32.to_le_bytes());
    // offset to b = 10
    assert_eq!(&encoded[4..8], &10u32.to_le_bytes());
    // c = 999
    assert_eq!(&encoded[8..10], &999u16.to_le_bytes());
    // b data
    assert_eq!(&encoded[10..12], &[0xAA, 0xBB]);
}

#[test]
fn mixed_struct_decode_round_trip() {
    let original = MixedStruct {
        a: 7,
        b: vec![0xAA, 0xBB],
        c: 999,
    };
    let encoded = original.to_ssz();
    let decoded = MixedStruct::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

#[test]
fn mixed_struct_is_variable_size() {
    assert!(!<MixedStruct as SszEncode>::is_fixed_size());
}

// ── Multiple variable fields ──

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct MultiVarStruct {
    a: Vec<u8>,
    b: u32,
    c: Vec<u16>,
}

#[test]
fn multi_var_struct_round_trip() {
    let original = MultiVarStruct {
        a: vec![1, 2, 3],
        b: 42,
        c: vec![100, 200],
    };
    let encoded = original.to_ssz();
    let decoded = MultiVarStruct::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

// ── Empty variable fields ──

#[test]
fn mixed_struct_empty_variable() {
    let original = MixedStruct {
        a: 0,
        b: vec![],
        c: 0,
    };
    let encoded = original.to_ssz();
    let decoded = MixedStruct::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

// ── HashTreeRoot for struct ──

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
struct SimpleContainer {
    a: u64,
    b: u64,
}

#[test]
fn hash_tree_root_struct() {
    let s = SimpleContainer { a: 1, b: 2 };
    let root = s.hash_tree_root(&Sha2Hasher);

    // Manual: merkleize([hash_tree_root(a), hash_tree_root(b)])
    let root_a = 1u64.hash_tree_root(&Sha2Hasher);
    let root_b = 2u64.hash_tree_root(&Sha2Hasher);
    let expected = libssz_merkle::merkleize(&Sha2Hasher, &[root_a, root_b], None);
    assert_eq!(root, expected);
}

// ── Union enum ──

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(enum_behaviour = "union")]
enum TestUnion {
    A(u32),
    B(Vec<u8>),
}

#[test]
fn union_encode_first_variant() {
    let val = TestUnion::A(42);
    let encoded = val.to_ssz();
    // selector=0, then u32 LE
    let mut expected = vec![0u8]; // selector
    expected.extend_from_slice(&42u32.to_le_bytes());
    assert_eq!(encoded, expected);
}

#[test]
fn union_encode_second_variant() {
    let val = TestUnion::B(vec![1, 2, 3]);
    let encoded = val.to_ssz();
    let mut expected = vec![1u8]; // selector
    expected.extend_from_slice(&[1, 2, 3]);
    assert_eq!(encoded, expected);
}

#[test]
fn union_decode_round_trip_a() {
    let original = TestUnion::A(42);
    let encoded = original.to_ssz();
    let decoded = TestUnion::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

#[test]
fn union_decode_round_trip_b() {
    let original = TestUnion::B(vec![1, 2, 3]);
    let encoded = original.to_ssz();
    let decoded = TestUnion::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

#[test]
fn union_decode_invalid_selector() {
    let bytes = [255u8, 0, 0, 0, 0];
    assert_eq!(
        TestUnion::from_ssz_bytes(&bytes),
        Err(DecodeError::InvalidUnionSelector(255))
    );
}

#[test]
fn union_hash_tree_root() {
    let val = TestUnion::A(42);
    let root = val.hash_tree_root(&Sha2Hasher);

    let inner_root = 42u32.hash_tree_root(&Sha2Hasher);
    let expected = libssz_merkle::mix_in_selector(&Sha2Hasher, &inner_root, 0);
    assert_eq!(root, expected);
}

// ── Transparent newtype ──

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(transparent)]
struct Wrapper(u64);

#[test]
fn transparent_encode() {
    let val = Wrapper(42);
    let encoded = val.to_ssz();
    assert_eq!(encoded, 42u64.to_ssz());
}

#[test]
fn transparent_decode_round_trip() {
    let original = Wrapper(42);
    let encoded = original.to_ssz();
    let decoded = Wrapper::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

#[test]
fn transparent_hash_tree_root() {
    let val = Wrapper(42);
    assert_eq!(
        val.hash_tree_root(&Sha2Hasher),
        42u64.hash_tree_root(&Sha2Hasher)
    );
}

// ── Named-field transparent ──

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(transparent)]
struct NamedWrapper {
    inner: u32,
}

#[test]
fn named_transparent_round_trip() {
    let original = NamedWrapper { inner: 123 };
    let encoded = original.to_ssz();
    let decoded = NamedWrapper::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, original);
}

// ── HashTreeRoot for progressive containers ──

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container)]
struct ProgressiveThreeFields {
    a: u64,
    b: u64,
    c: u64,
}

#[test]
fn hash_tree_root_progressive_container() {
    let s = ProgressiveThreeFields { a: 1, b: 2, c: 3 };
    let root = s.hash_tree_root(&Sha2Hasher);

    // Manual: mix_in_active_fields(merkleize_progressive(field_roots), [1, 1, 1])
    let field_roots = [
        1u64.hash_tree_root(&Sha2Hasher),
        2u64.hash_tree_root(&Sha2Hasher),
        3u64.hash_tree_root(&Sha2Hasher),
    ];
    let progressive = libssz_merkle::merkleize_progressive(&Sha2Hasher, &field_roots);
    let expected = libssz_merkle::mix_in_active_fields(&Sha2Hasher, &progressive, &[true; 3]);
    assert_eq!(root, expected);
}

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
struct PlainThreeFields {
    a: u64,
    b: u64,
    c: u64,
}

/// A progressive container merkleizes differently from a plain container even
/// though the two serialize identically.
#[test]
fn progressive_container_root_differs_from_plain_container() {
    let progressive = ProgressiveThreeFields { a: 1, b: 2, c: 3 };
    let plain = PlainThreeFields { a: 1, b: 2, c: 3 };

    assert_eq!(progressive.to_ssz(), plain.to_ssz());
    assert_ne!(
        progressive.hash_tree_root(&Sha2Hasher),
        plain.hash_tree_root(&Sha2Hasher)
    );
}

// ── HashTreeRoot for progressive containers with inactive fields ──

#[derive(Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container, active_fields = [1, 0, 1, 0, 1])]
struct ProgressiveInactiveFields {
    a: u64,
    b: u64,
    c: u64,
}

/// Inactive positions contribute a zero chunk, and the mixed-in bitvector has
/// the corresponding bits clear.
#[test]
fn hash_tree_root_progressive_container_with_inactive_fields() {
    let s = ProgressiveInactiveFields { a: 1, b: 2, c: 3 };

    let zero = [0u8; 32];
    let chunks = [
        1u64.hash_tree_root(&Sha2Hasher),
        zero,
        2u64.hash_tree_root(&Sha2Hasher),
        zero,
        3u64.hash_tree_root(&Sha2Hasher),
    ];
    let progressive = libssz_merkle::merkleize_progressive(&Sha2Hasher, &chunks);
    let expected = libssz_merkle::mix_in_active_fields(
        &Sha2Hasher,
        &progressive,
        &[true, false, true, false, true],
    );
    assert_eq!(s.hash_tree_root(&Sha2Hasher), expected);
}

/// `active_fields` changes only merkleization: the serialization is the same as
/// the all-active container with the same fields.
#[test]
fn inactive_fields_change_root_but_not_encoding() {
    let inactive = ProgressiveInactiveFields { a: 1, b: 2, c: 3 };
    let all_active = ProgressiveThreeFields { a: 1, b: 2, c: 3 };

    assert_eq!(inactive.to_ssz(), all_active.to_ssz());
    assert_ne!(
        inactive.hash_tree_root(&Sha2Hasher),
        all_active.hash_tree_root(&Sha2Hasher)
    );
}
