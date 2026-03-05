#![no_main]

//! Fuzz union type decode for no-panic and roundtrip correctness.

extern crate libssz as ssz;

use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
#[ssz(enum_behaviour = "union")]
enum TestUnion {
    U64Val(u64),
    BoolVal(bool),
    Bytes32Val([u8; 32]),
    VecU8Val(Vec<u8>),
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct ContainerWithUnion {
    id: u64,
    payload: TestUnion,
}

fuzz_target!(|data: &[u8]| {
    // Decode union from arbitrary bytes — must not panic
    let _ = TestUnion::from_ssz_bytes(data);

    // Roundtrip
    if let Ok(val) = TestUnion::from_ssz_bytes(data) {
        let encoded = val.to_ssz();
        let decoded = TestUnion::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded, "union roundtrip mismatch");
    }

    // Container with union
    let _ = ContainerWithUnion::from_ssz_bytes(data);

    if let Ok(val) = ContainerWithUnion::from_ssz_bytes(data) {
        let encoded = val.to_ssz();
        let decoded = ContainerWithUnion::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded, "container-with-union roundtrip mismatch");
    }
});
