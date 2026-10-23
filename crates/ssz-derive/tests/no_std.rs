//! The derives must expand in a `#![no_std]` crate, where `Vec` is not in the
//! prelude. Each type exercises a different place the generated code names
//! `Vec`: container encode and decode, transparent encode, and union encode.
#![no_std]

extern crate alloc;
// Only for the test harness; std's prelude is still not in scope here.
extern crate std;

use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct Container {
    a: u32,
    b: alloc::vec::Vec<u8>,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
#[ssz(transparent)]
struct Wrapper(u64);

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
#[ssz(enum_behaviour = "union")]
enum Choice {
    A(u16),
    B(u32),
}

#[test]
fn container_round_trips() {
    let value = Container {
        a: 7,
        b: alloc::vec![1, 2, 3],
    };
    assert_eq!(Container::from_ssz_bytes(&value.to_ssz()), Ok(value));
}

#[test]
fn fixed_container_list_round_trips() {
    #[derive(Debug, PartialEq, SszEncode, SszDecode)]
    struct Pair {
        x: u32,
        y: u32,
    }

    let items = alloc::vec![Pair { x: 1, y: 2 }, Pair { x: 3, y: 4 }];
    let mut bytes = alloc::vec::Vec::new();
    Pair::ssz_append_fixed_slice(&items, &mut bytes);
    assert_eq!(Pair::ssz_decode_fixed_vec(&bytes), Ok(items));
}

#[test]
fn transparent_round_trips() {
    let value = Wrapper(42);
    assert_eq!(Wrapper::from_ssz_bytes(&value.to_ssz()), Ok(value));
}

#[test]
fn union_round_trips() {
    let value = Choice::B(9);
    assert_eq!(Choice::from_ssz_bytes(&value.to_ssz()), Ok(value));
}
