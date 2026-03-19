#![no_main]

//! Fuzz target for nested variable-size SSZ types: roundtrip encode/decode and no-panic decode.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct InnerContainer {
    id: u64,
    data: Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct OuterContainer {
    header: u64,
    inner: InnerContainer,
    tail: Vec<u8>,
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    header: u64,
    inner_id: u64,
    inner_data: Vec<u8>,
    tail: Vec<u8>,
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap sizes for performance
    let inner_data: Vec<u8> = if input.inner_data.len() > 1024 {
        input.inner_data[..1024].to_vec()
    } else {
        input.inner_data.clone()
    };
    let tail: Vec<u8> = if input.tail.len() > 1024 {
        input.tail[..1024].to_vec()
    } else {
        input.tail.clone()
    };

    // -- No-panic decode from raw bytes --
    let _ = InnerContainer::from_ssz_bytes(&input.raw);
    let _ = OuterContainer::from_ssz_bytes(&input.raw);

    // -- Structured roundtrip: InnerContainer --
    let inner = InnerContainer {
        id: input.inner_id,
        data: inner_data.clone(),
    };
    let encoded = inner.to_ssz();
    let decoded = InnerContainer::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, inner, "InnerContainer roundtrip");

    // -- Structured roundtrip: OuterContainer (nested variable-size) --
    let outer = OuterContainer {
        header: input.header,
        inner: InnerContainer {
            id: input.inner_id,
            data: inner_data,
        },
        tail,
    };
    let encoded = outer.to_ssz();
    let decoded = OuterContainer::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, outer, "OuterContainer roundtrip");
});
