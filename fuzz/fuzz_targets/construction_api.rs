#![no_main]

//! Fuzz target for direct construction API methods on SSZ types.
//!
//! Tests SszBitlist, SszBitvector, SszList, and SszVector construction
//! methods that are not exercised by encode/decode fuzzing alone.

extern crate libssz as ssz;
extern crate libssz_merkle as ssz_merkle;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_types::{SszBitlist, SszBitvector, SszList, SszVector};

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    len: u16,
    bits: Vec<bool>,
    set_index: u16,
    set_value: bool,
    vec_u64: Vec<u64>,
}

fuzz_target!(|input: FuzzInput| {
    let len = input.len as usize;
    let set_index = input.set_index as usize;

    // Cap inputs for performance
    let bits: Vec<bool> = input.bits[..core::cmp::min(input.bits.len(), 4096)].to_vec();
    let vec_u64: Vec<u64> = input.vec_u64[..core::cmp::min(input.vec_u64.len(), 256)].to_vec();

    // -- SszBitlist::with_length --
    // Must not panic; returns Ok if len <= 4096, Err otherwise.
    if let Ok(bl) = SszBitlist::<4096>::with_length(len) {
        let encoded = bl.to_ssz();
        let decoded = SszBitlist::<4096>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bl, decoded, "SszBitlist::with_length roundtrip");
    }

    // -- SszBitlist::push up to capacity, then verify push at capacity returns Err --
    {
        let cap: usize = 16;
        let mut bl = SszBitlist::<16>::new();
        for i in 0..core::cmp::min(bits.len(), cap) {
            bl.push(bits[i]).unwrap();
        }
        if bl.len() == cap {
            assert!(bl.push(false).is_err(), "push at capacity must return Err");
        }
        // Roundtrip the filled bitlist
        let encoded = bl.to_ssz();
        let decoded = SszBitlist::<16>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bl, decoded, "SszBitlist push roundtrip");
    }

    // -- SszBitlist::set with index >= len returns Err --
    {
        if let Ok(mut bl) = SszBitlist::<4096>::with_length(len) {
            // set within bounds must return Ok (if len > 0)
            if len > 0 {
                assert!(bl.set(0, true).is_ok());
            }
            // set at or beyond len must return Err
            assert!(bl.set(len, true).is_err());
            assert!(bl.set(len.saturating_add(1), true).is_err());
            assert!(bl.set(set_index.saturating_add(len).saturating_add(1), true).is_err());
        }
    }

    // -- SszBitlist::try_from(Vec<bool>) -- must not panic --
    {
        let result = SszBitlist::<4096>::try_from(bits.clone());
        if let Ok(bl) = result {
            let encoded = bl.to_ssz();
            let decoded = SszBitlist::<4096>::from_ssz_bytes(&encoded).unwrap();
            assert_eq!(bl, decoded, "SszBitlist try_from roundtrip");
        }
    }

    // -- SszList<u64, 256>::try_from -- must not panic --
    {
        let result = SszList::<u64, 256>::try_from(vec_u64.clone());
        if let Ok(list) = result {
            let encoded = list.to_ssz();
            let decoded = SszList::<u64, 256>::from_ssz_bytes(&encoded).unwrap();
            assert_eq!(list, decoded, "SszList try_from roundtrip");
        }
    }

    // -- SszVector<u64, N>::try_from with specific sizes --
    // N must be a const generic, so test specific values.
    {
        let n1_input = vec_u64[..core::cmp::min(vec_u64.len(), 1)].to_vec();
        if let Ok(v) = SszVector::<u64, 1>::try_from(n1_input) {
            let encoded = v.to_ssz();
            let decoded = SszVector::<u64, 1>::from_ssz_bytes(&encoded).unwrap();
            assert_eq!(v, decoded, "SszVector<1> roundtrip");
        }
        // Wrong length — must not panic
        let _ = SszVector::<u64, 4>::try_from(vec_u64.clone());

        let n4_input = vec_u64[..core::cmp::min(vec_u64.len(), 4)].to_vec();
        if let Ok(v) = SszVector::<u64, 4>::try_from(n4_input) {
            let encoded = v.to_ssz();
            let decoded = SszVector::<u64, 4>::from_ssz_bytes(&encoded).unwrap();
            assert_eq!(v, decoded, "SszVector<4> roundtrip");
        }

        let n8_input = vec_u64[..core::cmp::min(vec_u64.len(), 8)].to_vec();
        if let Ok(v) = SszVector::<u64, 8>::try_from(n8_input) {
            let encoded = v.to_ssz();
            let decoded = SszVector::<u64, 8>::from_ssz_bytes(&encoded).unwrap();
            assert_eq!(v, decoded, "SszVector<8> roundtrip");
        }
        // Wrong length — must not panic
        let _ = SszVector::<u64, 8>::try_from(vec_u64.clone());
    }

    // -- SszBitvector::new() then set/get roundtrip --
    {
        let mut bv = SszBitvector::<64>::new();
        // set within bounds
        let idx = set_index % 64;
        bv.set(idx, input.set_value).unwrap();
        assert_eq!(bv.get(idx), Some(input.set_value), "SszBitvector set/get");
        // set out of bounds must return Err
        assert!(bv.set(64, true).is_err());
        assert!(bv.set(usize::MAX, true).is_err());

        let encoded = bv.to_ssz();
        let decoded = SszBitvector::<64>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bv, decoded, "SszBitvector roundtrip");
    }

    // -- SszBitvector with smaller N --
    {
        let mut bv = SszBitvector::<8>::new();
        let idx = set_index % 8;
        bv.set(idx, input.set_value).unwrap();
        assert_eq!(bv.get(idx), Some(input.set_value));
        let encoded = bv.to_ssz();
        let decoded = SszBitvector::<8>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bv, decoded, "SszBitvector<8> roundtrip");
    }
});
