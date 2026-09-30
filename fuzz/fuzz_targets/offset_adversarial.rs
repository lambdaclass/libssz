#![no_main]

//! Fuzz target for adversarial offset validation in variable-size SSZ containers.
//!
//! Uses raw byte input to exercise all kinds of adversarial patterns:
//! non-monotonic offsets, zero offsets, offsets exceeding buffer length,
//! offsets pointing into the fixed section, etc.

use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct OneVarField {
    a: Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct TwoVarFields {
    a: Vec<u8>,
    b: Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct ThreeVarFields {
    a: Vec<u8>,
    b: Vec<u8>,
    c: Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct FixedThenVar {
    id: u64,
    data: Vec<u8>,
}

// Variable-length collection of *variable-size* elements. This reaches the
// offset-table allocation path (`Vec::with_capacity(num_items)`) that the
// structs above never hit — their fields are fixed-size `u8` elements. That
// gap previously hid a pre-allocation DoS in variable-element list decoding.
#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct VarItemList {
    items: Vec<Vec<u8>>,
}

fuzz_target!(|data: &[u8]| {
    // Attempt decode of each struct — must never panic regardless of input.
    // If decode succeeds, roundtrip must hold.

    if let Ok(v) = OneVarField::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = OneVarField::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "OneVarField roundtrip");
    }

    if let Ok(v) = TwoVarFields::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = TwoVarFields::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "TwoVarFields roundtrip");
    }

    if let Ok(v) = ThreeVarFields::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = ThreeVarFields::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "ThreeVarFields roundtrip");
    }

    if let Ok(v) = FixedThenVar::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = FixedThenVar::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "FixedThenVar roundtrip");
    }

    if let Ok(v) = VarItemList::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = VarItemList::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "VarItemList roundtrip");
    }

    // The bare uncapped `Vec<T>` of variable-size elements (also the basis for
    // `ProgressiveList`): the offset-table allocation has no max-length backstop.
    if let Ok(v) = Vec::<Vec<u8>>::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = Vec::<Vec<u8>>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "Vec<Vec<u8>> roundtrip");
    }
});
