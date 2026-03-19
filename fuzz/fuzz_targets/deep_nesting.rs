#![no_main]

//! Fuzz target for deeply nested SSZ composites and SszList of variable-size items.

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct Level1 {
    id: u64,
    data: Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct Level2 {
    header: u64,
    inner: Level1,
    extra: Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct Level3 {
    tag: u64,
    nested: Level2,
    tail: Vec<u8>,
}

#[derive(Debug, Arbitrary)]
struct FuzzItem {
    id: u64,
    data: Vec<u8>,
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    tag: u64,
    header: u64,
    inner_id: u64,
    inner_data: Vec<u8>,
    extra: Vec<u8>,
    tail: Vec<u8>,
    raw: Vec<u8>,
    list_items: Vec<FuzzItem>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap sizes for performance
    let inner_data: Vec<u8> = input.inner_data[..input.inner_data.len().min(256)].to_vec();
    let extra: Vec<u8> = input.extra[..input.extra.len().min(256)].to_vec();
    let tail: Vec<u8> = input.tail[..input.tail.len().min(256)].to_vec();

    // -- No-panic decode from raw bytes --
    let _ = Level1::from_ssz_bytes(&input.raw);
    let _ = Level2::from_ssz_bytes(&input.raw);
    let _ = Level3::from_ssz_bytes(&input.raw);

    // -- Structured roundtrip: Level1 --
    let l1 = Level1 {
        id: input.inner_id,
        data: inner_data.clone(),
    };
    let encoded = l1.to_ssz();
    let decoded = Level1::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, l1, "Level1 roundtrip");

    // -- Structured roundtrip: Level2 --
    let l2 = Level2 {
        header: input.header,
        inner: Level1 {
            id: input.inner_id,
            data: inner_data.clone(),
        },
        extra: extra.clone(),
    };
    let encoded = l2.to_ssz();
    let decoded = Level2::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, l2, "Level2 roundtrip");

    // -- Structured roundtrip: Level3 (3-level deep nesting) --
    let l3 = Level3 {
        tag: input.tag,
        nested: Level2 {
            header: input.header,
            inner: Level1 {
                id: input.inner_id,
                data: inner_data,
            },
            extra,
        },
        tail,
    };
    let encoded = l3.to_ssz();
    let decoded = Level3::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, l3, "Level3 roundtrip");

    // -- SszList<Level1, 16>: list of variable-size items --
    let items: Vec<Level1> = input
        .list_items
        .iter()
        .take(16)
        .map(|fi| Level1 {
            id: fi.id,
            data: fi.data[..fi.data.len().min(256)].to_vec(),
        })
        .collect();

    if let Ok(list) = libssz_types::SszList::<Level1, 16>::try_from(items) {
        let encoded = list.to_ssz();
        let decoded = libssz_types::SszList::<Level1, 16>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(list, decoded, "SszList<Level1, 16> roundtrip");
    }
});
