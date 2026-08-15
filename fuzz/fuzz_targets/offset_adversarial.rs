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

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct VarItemsField {
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

    // Lists of variable-length items have their own offset table, exercising
    // decode_variable_length_items_with_max rather than ContainerDecoder.
    if let Ok(v) = Vec::<Vec<u8>>::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = Vec::<Vec<u8>>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "Vec<Vec<u8>> roundtrip");
    }

    if let Ok(v) = VarItemsField::from_ssz_bytes(data) {
        let encoded = v.to_ssz();
        let decoded = VarItemsField::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(decoded, v, "VarItemsField roundtrip");
    }
});
