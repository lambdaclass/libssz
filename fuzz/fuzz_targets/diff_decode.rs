#![no_main]

//! Differential decoding fuzzer: encode the same data with libssz, lighthouse_ssz,
//! or ssz_rs, then decode with the other libraries and assert results match.

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

    // -- Encode with ours, decode with all three, assert_eq --

    // bool
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_bool);
        let ours = bool::from_ssz_bytes(&bytes).unwrap();
        let lh = <bool as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <bool as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "bool: ours-encode, both-decode");
        assert_eq!(ours, rs, "bool: ours-encode, ssz_rs-decode");
    }

    // u8
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u8);
        let ours = u8::from_ssz_bytes(&bytes).unwrap();
        let lh = <u8 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u8 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u8: ours-encode, both-decode");
        assert_eq!(ours, rs, "u8: ours-encode, ssz_rs-decode");
    }

    // u16
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u16);
        let ours = u16::from_ssz_bytes(&bytes).unwrap();
        let lh = <u16 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u16 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u16: ours-encode, both-decode");
        assert_eq!(ours, rs, "u16: ours-encode, ssz_rs-decode");
    }

    // u32
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u32);
        let ours = u32::from_ssz_bytes(&bytes).unwrap();
        let lh = <u32 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u32 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u32: ours-encode, both-decode");
        assert_eq!(ours, rs, "u32: ours-encode, ssz_rs-decode");
    }

    // u64
    {
        let bytes = libssz::SszEncode::to_ssz(&input.val_u64);
        let ours = u64::from_ssz_bytes(&bytes).unwrap();
        let lh = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u64 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u64: ours-encode, both-decode");
        assert_eq!(ours, rs, "u64: ours-encode, ssz_rs-decode");
    }

    // u128 (ssz_rs doesn't support u128, so only ours + lighthouse)
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
        let rs = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "[u8;32]: ours-encode, both-decode");
        assert_eq!(ours, rs, "[u8;32]: ours-encode, ssz_rs-decode");
    }

    // Vec<u64>
    {
        let bytes = libssz::SszEncode::to_ssz(&vec);
        let ours = Vec::<u64>::from_ssz_bytes(&bytes).unwrap();
        let lh = <Vec<u64> as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "Vec<u64>: ours-encode, both-decode");
        // ssz_rs: decode as List<u64, 1024>
        let rs = <ssz_rs::List<u64, 1024> as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs.to_vec(), "Vec<u64>: ours-encode, ssz_rs-decode");
    }

    // -- Encode with lighthouse, decode with ours + ssz_rs --

    // bool
    {
        let bytes = <bool as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_bool);
        let ours = bool::from_ssz_bytes(&bytes).unwrap();
        let lh = <bool as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <bool as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "bool: lighthouse-encode, both-decode");
        assert_eq!(ours, rs, "bool: lighthouse-encode, ssz_rs-decode");
    }

    // u8
    {
        let bytes = <u8 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u8);
        let ours = u8::from_ssz_bytes(&bytes).unwrap();
        let lh = <u8 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u8 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u8: lighthouse-encode, both-decode");
        assert_eq!(ours, rs, "u8: lighthouse-encode, ssz_rs-decode");
    }

    // u16
    {
        let bytes = <u16 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u16);
        let ours = u16::from_ssz_bytes(&bytes).unwrap();
        let lh = <u16 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u16 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u16: lighthouse-encode, both-decode");
        assert_eq!(ours, rs, "u16: lighthouse-encode, ssz_rs-decode");
    }

    // u32
    {
        let bytes = <u32 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u32);
        let ours = u32::from_ssz_bytes(&bytes).unwrap();
        let lh = <u32 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u32 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u32: lighthouse-encode, both-decode");
        assert_eq!(ours, rs, "u32: lighthouse-encode, ssz_rs-decode");
    }

    // u64
    {
        let bytes = <u64 as lighthouse_ssz::Encode>::as_ssz_bytes(&input.val_u64);
        let ours = u64::from_ssz_bytes(&bytes).unwrap();
        let lh = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        let rs = <u64 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "u64: lighthouse-encode, both-decode");
        assert_eq!(ours, rs, "u64: lighthouse-encode, ssz_rs-decode");
    }

    // u128 (ssz_rs doesn't support u128)
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
        let rs = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, lh, "[u8;32]: lighthouse-encode, both-decode");
        assert_eq!(ours, rs, "[u8;32]: lighthouse-encode, ssz_rs-decode");
    }

    // Vec<u64>
    {
        let bytes = <Vec<u64> as lighthouse_ssz::Encode>::as_ssz_bytes(&vec);
        let ours = Vec::<u64>::from_ssz_bytes(&bytes).unwrap();
        let lh = <Vec<u64> as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, lh, "Vec<u64>: lighthouse-encode, both-decode");
        let rs = <ssz_rs::List<u64, 1024> as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs.to_vec(), "Vec<u64>: lighthouse-encode, ssz_rs-decode");
    }

    // -- Encode with ssz_rs, decode with ours + lighthouse (skip u128) --

    // bool
    {
        let mut bytes = Vec::new();
        ssz_rs::Serialize::serialize(&input.val_bool, &mut bytes).unwrap();
        let ours = bool::from_ssz_bytes(&bytes).unwrap();
        let rs = <bool as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs, "bool: ssz_rs-encode, both-decode");
    }

    // u8
    {
        let mut bytes = Vec::new();
        ssz_rs::Serialize::serialize(&input.val_u8, &mut bytes).unwrap();
        let ours = u8::from_ssz_bytes(&bytes).unwrap();
        let rs = <u8 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs, "u8: ssz_rs-encode, both-decode");
    }

    // u16
    {
        let mut bytes = Vec::new();
        ssz_rs::Serialize::serialize(&input.val_u16, &mut bytes).unwrap();
        let ours = u16::from_ssz_bytes(&bytes).unwrap();
        let rs = <u16 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs, "u16: ssz_rs-encode, both-decode");
    }

    // u32
    {
        let mut bytes = Vec::new();
        ssz_rs::Serialize::serialize(&input.val_u32, &mut bytes).unwrap();
        let ours = u32::from_ssz_bytes(&bytes).unwrap();
        let rs = <u32 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs, "u32: ssz_rs-encode, both-decode");
    }

    // u64
    {
        let mut bytes = Vec::new();
        ssz_rs::Serialize::serialize(&input.val_u64, &mut bytes).unwrap();
        let ours = u64::from_ssz_bytes(&bytes).unwrap();
        let rs = <u64 as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs, "u64: ssz_rs-encode, both-decode");
    }

    // [u8; 32]
    {
        let mut bytes = Vec::new();
        ssz_rs::Serialize::serialize(&input.val_bytes32, &mut bytes).unwrap();
        let ours = <[u8; 32]>::from_ssz_bytes(&bytes).unwrap();
        let rs = <[u8; 32] as ssz_rs::Deserialize>::deserialize(&bytes).unwrap();
        assert_eq!(ours, rs, "[u8;32]: ssz_rs-encode, both-decode");
    }

    // Vec<u64>
    {
        let ssz_rs_list: ssz_rs::List<u64, 1024> = vec.clone().try_into().unwrap();
        let mut bytes = Vec::new();
        ssz_rs::Serialize::serialize(&ssz_rs_list, &mut bytes).unwrap();
        let ours = Vec::<u64>::from_ssz_bytes(&bytes).unwrap();
        assert_eq!(ours, vec, "Vec<u64>: ssz_rs-encode, ours-decode");
    }
});
