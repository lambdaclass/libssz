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

// ── More variable fields than the `ContainerDecoder` keeps inline ──

// Eleven variable fields: the decoder keeps the first eight offsets inline and the
// other three (`v8`, `v9`, `v10`) in separately allocated memory.
#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct ManyVarStruct {
    v0: Vec<u8>,
    f0: u16,
    v1: Vec<u16>,
    v2: Vec<u32>,
    v3: Vec<u64>,
    v4: Vec<u8>,
    f1: u64,
    v5: Vec<u8>,
    v6: Vec<u16>,
    v7: Vec<u8>,
    v8: Vec<u32>,
    v9: Vec<u8>,
    v10: Vec<u64>,
}

/// Fixed part: 11 offsets of 4 bytes, `f0` (2) and `f1` (8).
const MANY_VAR_FIXED_LEN: usize = 11 * 4 + 2 + 8;
/// Position, within the fixed part, of each variable field's offset.
const MANY_VAR_OFFSET_POS: [usize; 11] = [0, 6, 10, 14, 18, 30, 34, 38, 42, 46, 50];

fn many_var_sample() -> ManyVarStruct {
    ManyVarStruct {
        v0: vec![1, 2, 3],
        f0: 0xBEEF,
        v1: vec![100, 200],
        v2: vec![7],
        v3: vec![],
        v4: vec![9; 5],
        f1: 0x0102_0304_0506_0708,
        v5: vec![4],
        v6: vec![300, 400, 500],
        v7: vec![],
        v8: vec![0xDEAD_BEEF, 1],
        v9: vec![8, 8],
        v10: vec![u64::MAX, 0, 42],
    }
}

fn read_u32_le(bytes: &[u8], pos: usize) -> usize {
    u32::from_le_bytes(bytes[pos..pos + 4].try_into().unwrap()) as usize
}

fn write_u32_le(bytes: &mut [u8], pos: usize, value: usize) {
    bytes[pos..pos + 4].copy_from_slice(&(value as u32).to_le_bytes());
}

#[test]
fn many_var_struct_round_trip() {
    let original = many_var_sample();
    let encoded = original.to_ssz();
    assert_eq!(encoded.len(), original.encoded_len());

    // The eleven offsets, checked against each field's length.
    let body_lens = [3, 4, 4, 0, 5, 1, 6, 0, 8, 2, 24];
    let mut expected_offset = MANY_VAR_FIXED_LEN;
    for (pos, len) in MANY_VAR_OFFSET_POS.iter().zip(body_lens) {
        assert_eq!(read_u32_le(&encoded, *pos), expected_offset);
        expected_offset += len;
    }
    assert_eq!(encoded.len(), expected_offset);

    assert_eq!(ManyVarStruct::from_ssz_bytes(&encoded).unwrap(), original);
}

#[test]
fn many_var_struct_all_empty_round_trip() {
    let original = ManyVarStruct {
        v0: vec![],
        f0: 0,
        v1: vec![],
        v2: vec![],
        v3: vec![],
        v4: vec![],
        f1: 0,
        v5: vec![],
        v6: vec![],
        v7: vec![],
        v8: vec![],
        v9: vec![],
        v10: vec![],
    };
    let encoded = original.to_ssz();
    assert_eq!(encoded.len(), MANY_VAR_FIXED_LEN);
    assert_eq!(ManyVarStruct::from_ssz_bytes(&encoded).unwrap(), original);
}

#[test]
fn many_var_struct_rejects_bad_offsets() {
    let good = many_var_sample().to_ssz();

    // Ninth offset (the first spilled one) smaller than the eighth (the last inline one).
    let mut bytes = good.clone();
    let eighth = read_u32_le(&bytes, MANY_VAR_OFFSET_POS[7]);
    write_u32_le(&mut bytes, MANY_VAR_OFFSET_POS[8], eighth - 1);
    assert_eq!(
        ManyVarStruct::from_ssz_bytes(&bytes),
        Err(DecodeError::OffsetsAreNotMonotonicallyIncreasing)
    );

    // Eleventh smaller than the tenth: both spilled.
    let mut bytes = good.clone();
    let tenth = read_u32_le(&bytes, MANY_VAR_OFFSET_POS[9]);
    write_u32_le(&mut bytes, MANY_VAR_OFFSET_POS[10], tenth - 1);
    assert_eq!(
        ManyVarStruct::from_ssz_bytes(&bytes),
        Err(DecodeError::OffsetsAreNotMonotonicallyIncreasing)
    );

    // Eleventh past the end.
    let mut bytes = good.clone();
    write_u32_le(&mut bytes, MANY_VAR_OFFSET_POS[10], good.len() + 1);
    assert_eq!(
        ManyVarStruct::from_ssz_bytes(&bytes),
        Err(DecodeError::OffsetOutOfBounds {
            offset: good.len() + 1,
            length: good.len()
        })
    );

    // First offset not pointing at the end of the fixed part.
    let mut bytes = good.clone();
    write_u32_le(&mut bytes, MANY_VAR_OFFSET_POS[0], MANY_VAR_FIXED_LEN + 1);
    assert_eq!(
        ManyVarStruct::from_ssz_bytes(&bytes),
        Err(DecodeError::InvalidFirstOffset {
            expected: MANY_VAR_FIXED_LEN,
            got: MANY_VAR_FIXED_LEN + 1
        })
    );
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

// ── hash_tree_roots: the derived rows against item by item ──

#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct OneField {
    a: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct TwoFields {
    a: u64,
    b: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct ThreeFields {
    a: u64,
    b: bool,
    c: [u8; 48],
}

#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct FiveFields {
    a: u64,
    b: u64,
    c: [u8; 32],
    d: [u8; 32],
    e: [u8; 32],
}

/// The shape of a consensus `Validator`: 121 bytes, eight fields.
#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
struct EightFields {
    pubkey: [u8; 48],
    credentials: [u8; 32],
    balance: u64,
    slashed: bool,
    e1: u64,
    e2: u64,
    e3: u64,
    e4: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct NineFields {
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    h: u64,
    i: u64,
}

#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct NestedFields {
    a: TwoFields,
    b: u64,
    c: ThreeFields,
}

#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct VariableFields {
    a: u64,
    b: Vec<u64>,
    c: EightFields,
}

/// Thirty-three fields: past the 32 of the override, so it keeps the default.
#[derive(Clone, Debug, PartialEq, SszEncode, HashTreeRoot)]
struct ManyFields {
    f00: u8,
    f01: u8,
    f02: u8,
    f03: u8,
    f04: u8,
    f05: u8,
    f06: u8,
    f07: u8,
    f08: u8,
    f09: u8,
    f10: u8,
    f11: u8,
    f12: u8,
    f13: u8,
    f14: u8,
    f15: u8,
    f16: u8,
    f17: u8,
    f18: u8,
    f19: u8,
    f20: u8,
    f21: u8,
    f22: u8,
    f23: u8,
    f24: u8,
    f25: u8,
    f26: u8,
    f27: u8,
    f28: u8,
    f29: u8,
    f30: u8,
    f31: u8,
    f32: u8,
}

struct Seed(u64);

impl Seed {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        let mut out = [0u8; N];
        for b in out.iter_mut() {
            *b = self.next() as u8;
        }
        out
    }
}

fn two(s: &mut Seed) -> TwoFields {
    TwoFields {
        a: s.next(),
        b: s.bytes(),
    }
}

fn three(s: &mut Seed) -> ThreeFields {
    ThreeFields {
        a: s.next(),
        b: s.next().is_multiple_of(2),
        c: s.bytes(),
    }
}

fn eight(s: &mut Seed) -> EightFields {
    EightFields {
        pubkey: s.bytes(),
        credentials: s.bytes(),
        balance: s.next(),
        slashed: s.next().is_multiple_of(2),
        e1: s.next(),
        e2: s.next(),
        e3: s.next(),
        e4: s.next(),
    }
}

fn check_many<T: HashTreeRoot>(make: impl Fn(&mut Seed) -> T) {
    let mut seed = Seed(0x9e37_79b9_7f4a_7c15);
    let items: Vec<T> = (0..300).map(|_| make(&mut seed)).collect();
    for n in (0..=70).chain([255, 256, 257, 300]) {
        let items = &items[..n];
        let mut out = vec![[0xaa; 32]; n + 2];
        libssz_merkle::hash_tree_roots(items, &Sha2Hasher, &mut out);
        for (i, item) in items.iter().enumerate() {
            assert_eq!(out[i], item.hash_tree_root(&Sha2Hasher), "item {i} of {n}");
        }
        assert_eq!(out[n..], [[0xaa; 32]; 2], "{n} items: wrote past them");
    }
}

#[test]
fn hash_tree_roots_is_item_by_item() {
    check_many(|s| OneField { a: s.next() });
    check_many(two);
    check_many(three);
    check_many(|s| FiveFields {
        a: s.next(),
        b: s.next(),
        c: s.bytes(),
        d: s.bytes(),
        e: s.bytes(),
    });
    check_many(eight);
    check_many(|s| NineFields {
        a: s.next(),
        b: s.next(),
        c: s.next(),
        d: s.next(),
        e: s.next(),
        f: s.next(),
        g: s.next(),
        h: s.next(),
        i: s.next(),
    });
    check_many(|s| NestedFields {
        a: two(s),
        b: s.next(),
        c: three(s),
    });
    check_many(|s| {
        let len = (s.next() % 9) as usize;
        VariableFields {
            a: s.next(),
            b: (0..len).map(|_| s.next()).collect(),
            c: eight(s),
        }
    });
    check_many(|s| {
        let b: [u8; 33] = s.bytes();
        ManyFields {
            f00: b[0],
            f01: b[1],
            f02: b[2],
            f03: b[3],
            f04: b[4],
            f05: b[5],
            f06: b[6],
            f07: b[7],
            f08: b[8],
            f09: b[9],
            f10: b[10],
            f11: b[11],
            f12: b[12],
            f13: b[13],
            f14: b[14],
            f15: b[15],
            f16: b[16],
            f17: b[17],
            f18: b[18],
            f19: b[19],
            f20: b[20],
            f21: b[21],
            f22: b[22],
            f23: b[23],
            f24: b[24],
            f25: b[25],
            f26: b[26],
            f27: b[27],
            f28: b[28],
            f29: b[29],
            f30: b[30],
            f31: b[31],
            f32: b[32],
        }
    });
}

#[test]
#[should_panic]
fn hash_tree_roots_panics_on_a_short_output() {
    let mut seed = Seed(7);
    let items: Vec<EightFields> = (0..5).map(|_| eight(&mut seed)).collect();
    let mut out = vec![[0u8; 32]; 4];
    libssz_merkle::hash_tree_roots(&items, &Sha2Hasher, &mut out);
}

#[test]
fn derived_rows_have_the_padded_width() {
    assert_eq!(OneField::hash_tree_root_width(), 1);
    assert_eq!(TwoFields::hash_tree_root_width(), 2);
    assert_eq!(ThreeFields::hash_tree_root_width(), 4);
    assert_eq!(FiveFields::hash_tree_root_width(), 8);
    assert_eq!(EightFields::hash_tree_root_width(), 8);
    assert_eq!(NineFields::hash_tree_root_width(), 16);
    assert_eq!(ManyFields::hash_tree_root_width(), 1);
}

#[test]
fn list_of_containers_root_is_from_the_item_roots() {
    let mut seed = Seed(11);
    for n in [0usize, 1, 2, 31, 32, 33, 100] {
        let items: Vec<EightFields> = (0..n).map(|_| eight(&mut seed)).collect();
        let roots: Vec<[u8; 32]> = items
            .iter()
            .map(|v| v.hash_tree_root(&Sha2Hasher))
            .collect();
        let data = if roots.is_empty() {
            libssz_merkle::merkleize(&Sha2Hasher, &[[0u8; 32]], None)
        } else {
            libssz_merkle::merkleize(&Sha2Hasher, &roots, None)
        };
        let want = libssz_merkle::mix_in_length(&Sha2Hasher, &data, n);
        assert_eq!(items.hash_tree_root(&Sha2Hasher), want, "{n} items");
    }
}

// ── ssz_append_fixed_slice by blocks of 1 KB ──

#[derive(Clone, Debug, PartialEq, SszEncode, SszDecode)]
struct BigFixed {
    a: u8,
    b: [u8; 1100],
}

fn check_fixed_slice<T: SszEncode + Clone>(items: &[T]) {
    for n in 0..=items.len() {
        let mut want = vec![7u8, 8, 9];
        for item in &items[..n] {
            want.extend_from_slice(&item.to_ssz());
        }
        let mut got = vec![7u8, 8, 9];
        T::ssz_append_fixed_slice(&items[..n], &mut got);
        assert_eq!(got, want, "{n} items");
        assert_eq!(items[..n].to_vec().to_ssz(), want[3..], "{n} items, to_ssz");
    }
}

#[test]
fn ssz_append_fixed_slice_is_item_by_item() {
    let mut seed = Seed(3);
    // 121 bytes: eight per block of 1 KB.
    check_fixed_slice(&(0..40).map(|_| eight(&mut seed)).collect::<Vec<_>>());
    // 8 bytes: exactly 128 per block.
    check_fixed_slice(
        &(0..300)
            .map(|_| OneField { a: seed.next() })
            .collect::<Vec<_>>(),
    );
    // 1101 bytes: more than a block, one per block.
    check_fixed_slice(
        &(0..4)
            .map(|_| BigFixed {
                a: seed.next() as u8,
                b: seed.bytes(),
            })
            .collect::<Vec<_>>(),
    );
    // Round trip of a list that crosses many blocks.
    let items: Vec<EightFields> = (0..1000).map(|_| eight(&mut seed)).collect();
    assert_eq!(
        Vec::<EightFields>::from_ssz_bytes(&items.to_ssz()).unwrap(),
        items
    );
}
