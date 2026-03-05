#![no_main]

//! Differential decoding fuzzer: encode the same data with libssz or lighthouse_ssz,
//! then decode with the other library and assert results match.

extern crate libssz as ssz;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::SszDecode;

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    val_bool: bool,
    val_u8: u8,
    val_u16: u16,
    val_u32: u32,
    val_u64: u64,
    val_u128: u128,
    val_bytes32: [u8; 32],
    vec_u64: Vec<u64>,
}

fuzz_target!(|input: FuzzInput| {
    // Cap vec for performance
    let vec: Vec<u64> = if input.vec_u64.len() > 1024 {
        input.vec_u64[..1024].to_vec()
    } else {
        input.vec_u64.clone()
    };

    // -- Encode with ours, decode with both, assert_eq --

    // bool
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_bool);
        let ours = bool::from_ssz_bytes(&bytes).unwrap();
        let lh = <bool as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "bool: ours-encode, both-decode");
    }

    // u8
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u8);
        let ours = u8::from_ssz_bytes(&bytes).unwrap();
        let lh = <u8 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u8: ours-encode, both-decode");
    }

    // u16
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u16);
        let ours = u16::from_ssz_bytes(&bytes).unwrap();
        let lh = <u16 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u16: ours-encode, both-decode");
    }

    // u32
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u32);
        let ours = u32::from_ssz_bytes(&bytes).unwrap();
        let lh = <u32 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u32: ours-encode, both-decode");
    }

    // u64
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u64);
        let ours = u64::from_ssz_bytes(&bytes).unwrap();
        let lh = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u64: ours-encode, both-decode");
    }

    // u128
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u128);
        let ours = u128::from_ssz_bytes(&bytes).unwrap();
        let lh = <u128 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u128: ours-encode, both-decode");
    }

    // [u8; 32]
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_bytes32);
        let ours = <[u8; 32]>::from_ssz_bytes(&bytes).unwrap();
        let lh = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "[u8;32]: ours-encode, both-decode");
    }

    // Vec<u64>
    {
        let bytes = libssz::SszEncode::to_ssz(&vec);
        let ours = Vec::<u64>::from_ssz_bytes(&bytes).unwrap();
        let lh = <Vec<u64> as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "Vec<u64>: ours-encode, both-decode");
    }

    // -- Encode with lighthouse, decode with ours --

    // bool
    {
        let bytes = <bool as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_bool);
        let ours = bool::from_ssz_bytes(&bytes).unwrap();
        let lh = <bool as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "bool: lighthouse-encode, both-decode");
    }

    // u8
    {
        let bytes = <u8 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u8);
        let ours = u8::from_ssz_bytes(&bytes).unwrap();
        let lh = <u8 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u8: lighthouse-encode, both-decode");
    }

    // u16
    {
        let bytes = <u16 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u16);
        let ours = u16::from_ssz_bytes(&bytes).unwrap();
        let lh = <u16 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u16: lighthouse-encode, both-decode");
    }

    // u32
    {
        let bytes = <u32 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u32);
        let ours = u32::from_ssz_bytes(&bytes).unwrap();
        let lh = <u32 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u32: lighthouse-encode, both-decode");
    }

    // u64
    {
        let bytes = <u64 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u64);
        let ours = u64::from_ssz_bytes(&bytes).unwrap();
        let lh = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u64: lighthouse-encode, both-decode");
    }

    // u128
    {
        let bytes = <u128 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u128);
        let ours = u128::from_ssz_bytes(&bytes).unwrap();
        let lh = <u128 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "u128: lighthouse-encode, both-decode");
    }

    // [u8; 32]
    {
        let bytes = <[u8; 32] as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_bytes32);
        let ours = <[u8; 32]>::from_ssz_bytes(&bytes).unwrap();
        let lh = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "[u8;32]: lighthouse-encode, both-decode");
    }

    // Vec<u64>
    {
        let bytes = <Vec<u64> as lighthouse_ssz::Encode>::as_ssz_bytes(&vec);
        let ours = Vec::<u64>::from_ssz_bytes(&bytes).unwrap();
        let lh = <Vec<u64> as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "Vec<u64>: lighthouse-encode, both-decode");
    }
});
