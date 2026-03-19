#![no_main]

//! Differential decoding fuzzer: encode the same data with libssz, lighthouse_ssz,
//! or ssz_rs, then decode with the other libraries and assert results match.

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
    // Fork
    prev_version: [u8; 4],
    cur_version: [u8; 4],
    fork_epoch: u64,
    // Checkpoint
    checkpoint_epoch: u64,
    checkpoint_root: [u8; 32],
    // Eth1Data
    deposit_root: [u8; 32],
    deposit_count: u64,
    eth1_block_hash: [u8; 32],
    // AttestationData
    att_slot: u64,
    att_index: u64,
    att_beacon_block_root: [u8; 32],
    source_epoch: u64,
    source_root: [u8; 32],
    target_epoch: u64,
    target_root: [u8; 32],
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

    // -- Fork (16 bytes: [u8;4] + [u8;4] + u64) --
    {
        // encode field-by-field with ours, decode field-by-field with lighthouse
        let bytes = {
            let mut buf = Vec::new();
            <[u8; 4] as libssz::SszEncode>::ssz_append(&input.prev_version, &mut buf);
            <[u8; 4] as libssz::SszEncode>::ssz_append(&input.cur_version, &mut buf);
            <u64 as libssz::SszEncode>::ssz_append(&input.fork_epoch, &mut buf);
            buf
        };
        let lh_prev = <[u8; 4] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..4]).unwrap();
        let lh_cur = <[u8; 4] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[4..8]).unwrap();
        let lh_epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..16]).unwrap();
        assert_eq!(input.prev_version, lh_prev, "Fork.prev_version: ours-encode, lh-decode");
        assert_eq!(input.cur_version, lh_cur, "Fork.cur_version: ours-encode, lh-decode");
        assert_eq!(input.fork_epoch, lh_epoch, "Fork.epoch: ours-encode, lh-decode");

        // encode with lighthouse, decode field-by-field with ours
        let lh_bytes = {
            let mut buf = Vec::new();
            <[u8; 4] as lighthouse_ssz::Encode>::ssz_append(&input.prev_version, &mut buf);
            <[u8; 4] as lighthouse_ssz::Encode>::ssz_append(&input.cur_version, &mut buf);
            <u64 as lighthouse_ssz::Encode>::ssz_append(&input.fork_epoch, &mut buf);
            buf
        };
        let our_prev = <[u8; 4]>::from_ssz_bytes(&lh_bytes[0..4]).unwrap();
        let our_cur = <[u8; 4]>::from_ssz_bytes(&lh_bytes[4..8]).unwrap();
        let our_epoch = u64::from_ssz_bytes(&lh_bytes[8..16]).unwrap();
        assert_eq!(input.prev_version, our_prev, "Fork.prev_version: lh-encode, ours-decode");
        assert_eq!(input.cur_version, our_cur, "Fork.cur_version: lh-encode, ours-decode");
        assert_eq!(input.fork_epoch, our_epoch, "Fork.epoch: lh-encode, ours-decode");

        // encode with ssz_rs, decode with ours
        let ssz_rs_bytes = {
            let mut buf = Vec::new();
            ssz_rs::Serialize::serialize(&input.prev_version, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.cur_version, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.fork_epoch, &mut buf).unwrap();
            buf
        };
        let our_prev = <[u8; 4]>::from_ssz_bytes(&ssz_rs_bytes[0..4]).unwrap();
        let our_cur = <[u8; 4]>::from_ssz_bytes(&ssz_rs_bytes[4..8]).unwrap();
        let our_epoch = u64::from_ssz_bytes(&ssz_rs_bytes[8..16]).unwrap();
        assert_eq!(input.prev_version, our_prev, "Fork.prev_version: ssz_rs-encode, ours-decode");
        assert_eq!(input.cur_version, our_cur, "Fork.cur_version: ssz_rs-encode, ours-decode");
        assert_eq!(input.fork_epoch, our_epoch, "Fork.epoch: ssz_rs-encode, ours-decode");
    }

    // -- Checkpoint (40 bytes: u64 + [u8;32]) --
    {
        let bytes = {
            let mut buf = Vec::new();
            <u64 as libssz::SszEncode>::ssz_append(&input.checkpoint_epoch, &mut buf);
            <[u8; 32] as libssz::SszEncode>::ssz_append(&input.checkpoint_root, &mut buf);
            buf
        };
        let lh_epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..8]).unwrap();
        let lh_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..40]).unwrap();
        assert_eq!(input.checkpoint_epoch, lh_epoch, "Checkpoint.epoch: ours-encode, lh-decode");
        assert_eq!(input.checkpoint_root, lh_root, "Checkpoint.root: ours-encode, lh-decode");

        let lh_bytes = {
            let mut buf = Vec::new();
            <u64 as lighthouse_ssz::Encode>::ssz_append(&input.checkpoint_epoch, &mut buf);
            <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.checkpoint_root, &mut buf);
            buf
        };
        let our_epoch = u64::from_ssz_bytes(&lh_bytes[0..8]).unwrap();
        let our_root = <[u8; 32]>::from_ssz_bytes(&lh_bytes[8..40]).unwrap();
        assert_eq!(input.checkpoint_epoch, our_epoch, "Checkpoint.epoch: lh-encode, ours-decode");
        assert_eq!(input.checkpoint_root, our_root, "Checkpoint.root: lh-encode, ours-decode");

        let ssz_rs_bytes = {
            let mut buf = Vec::new();
            ssz_rs::Serialize::serialize(&input.checkpoint_epoch, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.checkpoint_root, &mut buf).unwrap();
            buf
        };
        let our_epoch = u64::from_ssz_bytes(&ssz_rs_bytes[0..8]).unwrap();
        let our_root = <[u8; 32]>::from_ssz_bytes(&ssz_rs_bytes[8..40]).unwrap();
        assert_eq!(input.checkpoint_epoch, our_epoch, "Checkpoint.epoch: ssz_rs-encode, ours-decode");
        assert_eq!(input.checkpoint_root, our_root, "Checkpoint.root: ssz_rs-encode, ours-decode");
    }

    // -- Eth1Data (72 bytes: [u8;32] + u64 + [u8;32]) --
    {
        let bytes = {
            let mut buf = Vec::new();
            <[u8; 32] as libssz::SszEncode>::ssz_append(&input.deposit_root, &mut buf);
            <u64 as libssz::SszEncode>::ssz_append(&input.deposit_count, &mut buf);
            <[u8; 32] as libssz::SszEncode>::ssz_append(&input.eth1_block_hash, &mut buf);
            buf
        };
        let lh_deposit_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..32]).unwrap();
        let lh_deposit_count = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[32..40]).unwrap();
        let lh_block_hash = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[40..72]).unwrap();
        assert_eq!(input.deposit_root, lh_deposit_root, "Eth1Data.deposit_root: ours-encode, lh-decode");
        assert_eq!(input.deposit_count, lh_deposit_count, "Eth1Data.deposit_count: ours-encode, lh-decode");
        assert_eq!(input.eth1_block_hash, lh_block_hash, "Eth1Data.block_hash: ours-encode, lh-decode");

        let lh_bytes = {
            let mut buf = Vec::new();
            <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.deposit_root, &mut buf);
            <u64 as lighthouse_ssz::Encode>::ssz_append(&input.deposit_count, &mut buf);
            <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.eth1_block_hash, &mut buf);
            buf
        };
        let our_deposit_root = <[u8; 32]>::from_ssz_bytes(&lh_bytes[0..32]).unwrap();
        let our_deposit_count = u64::from_ssz_bytes(&lh_bytes[32..40]).unwrap();
        let our_block_hash = <[u8; 32]>::from_ssz_bytes(&lh_bytes[40..72]).unwrap();
        assert_eq!(input.deposit_root, our_deposit_root, "Eth1Data.deposit_root: lh-encode, ours-decode");
        assert_eq!(input.deposit_count, our_deposit_count, "Eth1Data.deposit_count: lh-encode, ours-decode");
        assert_eq!(input.eth1_block_hash, our_block_hash, "Eth1Data.block_hash: lh-encode, ours-decode");

        let ssz_rs_bytes = {
            let mut buf = Vec::new();
            ssz_rs::Serialize::serialize(&input.deposit_root, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.deposit_count, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.eth1_block_hash, &mut buf).unwrap();
            buf
        };
        let our_deposit_root = <[u8; 32]>::from_ssz_bytes(&ssz_rs_bytes[0..32]).unwrap();
        let our_deposit_count = u64::from_ssz_bytes(&ssz_rs_bytes[32..40]).unwrap();
        let our_block_hash = <[u8; 32]>::from_ssz_bytes(&ssz_rs_bytes[40..72]).unwrap();
        assert_eq!(input.deposit_root, our_deposit_root, "Eth1Data.deposit_root: ssz_rs-encode, ours-decode");
        assert_eq!(input.deposit_count, our_deposit_count, "Eth1Data.deposit_count: ssz_rs-encode, ours-decode");
        assert_eq!(input.eth1_block_hash, our_block_hash, "Eth1Data.block_hash: ssz_rs-encode, ours-decode");
    }

    // -- AttestationData (128 bytes: u64+u64+[u8;32]+u64+[u8;32]+u64+[u8;32]) --
    {
        let bytes = {
            let mut buf = Vec::new();
            <u64 as libssz::SszEncode>::ssz_append(&input.att_slot, &mut buf);
            <u64 as libssz::SszEncode>::ssz_append(&input.att_index, &mut buf);
            <[u8; 32] as libssz::SszEncode>::ssz_append(&input.att_beacon_block_root, &mut buf);
            <u64 as libssz::SszEncode>::ssz_append(&input.source_epoch, &mut buf);
            <[u8; 32] as libssz::SszEncode>::ssz_append(&input.source_root, &mut buf);
            <u64 as libssz::SszEncode>::ssz_append(&input.target_epoch, &mut buf);
            <[u8; 32] as libssz::SszEncode>::ssz_append(&input.target_root, &mut buf);
            buf
        };
        let lh_att_slot = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[0..8]).unwrap();
        let lh_att_index = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[8..16]).unwrap();
        let lh_bbr = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[16..48]).unwrap();
        let lh_src_epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[48..56]).unwrap();
        let lh_src_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[56..88]).unwrap();
        let lh_tgt_epoch = <u64 as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[88..96]).unwrap();
        let lh_tgt_root = <[u8; 32] as lighthouse_ssz::Decode>::from_ssz_bytes(&bytes[96..128]).unwrap();
        assert_eq!(input.att_slot, lh_att_slot, "AttestationData.slot: ours-encode, lh-decode");
        assert_eq!(input.att_index, lh_att_index, "AttestationData.index: ours-encode, lh-decode");
        assert_eq!(input.att_beacon_block_root, lh_bbr, "AttestationData.bbr: ours-encode, lh-decode");
        assert_eq!(input.source_epoch, lh_src_epoch, "AttestationData.source_epoch: ours-encode, lh-decode");
        assert_eq!(input.source_root, lh_src_root, "AttestationData.source_root: ours-encode, lh-decode");
        assert_eq!(input.target_epoch, lh_tgt_epoch, "AttestationData.target_epoch: ours-encode, lh-decode");
        assert_eq!(input.target_root, lh_tgt_root, "AttestationData.target_root: ours-encode, lh-decode");

        let lh_bytes = {
            let mut buf = Vec::new();
            <u64 as lighthouse_ssz::Encode>::ssz_append(&input.att_slot, &mut buf);
            <u64 as lighthouse_ssz::Encode>::ssz_append(&input.att_index, &mut buf);
            <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.att_beacon_block_root, &mut buf);
            <u64 as lighthouse_ssz::Encode>::ssz_append(&input.source_epoch, &mut buf);
            <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.source_root, &mut buf);
            <u64 as lighthouse_ssz::Encode>::ssz_append(&input.target_epoch, &mut buf);
            <[u8; 32] as lighthouse_ssz::Encode>::ssz_append(&input.target_root, &mut buf);
            buf
        };
        let our_att_slot = u64::from_ssz_bytes(&lh_bytes[0..8]).unwrap();
        let our_att_index = u64::from_ssz_bytes(&lh_bytes[8..16]).unwrap();
        let our_bbr = <[u8; 32]>::from_ssz_bytes(&lh_bytes[16..48]).unwrap();
        let our_src_epoch = u64::from_ssz_bytes(&lh_bytes[48..56]).unwrap();
        let our_src_root = <[u8; 32]>::from_ssz_bytes(&lh_bytes[56..88]).unwrap();
        let our_tgt_epoch = u64::from_ssz_bytes(&lh_bytes[88..96]).unwrap();
        let our_tgt_root = <[u8; 32]>::from_ssz_bytes(&lh_bytes[96..128]).unwrap();
        assert_eq!(input.att_slot, our_att_slot, "AttestationData.slot: lh-encode, ours-decode");
        assert_eq!(input.att_index, our_att_index, "AttestationData.index: lh-encode, ours-decode");
        assert_eq!(input.att_beacon_block_root, our_bbr, "AttestationData.bbr: lh-encode, ours-decode");
        assert_eq!(input.source_epoch, our_src_epoch, "AttestationData.source_epoch: lh-encode, ours-decode");
        assert_eq!(input.source_root, our_src_root, "AttestationData.source_root: lh-encode, ours-decode");
        assert_eq!(input.target_epoch, our_tgt_epoch, "AttestationData.target_epoch: lh-encode, ours-decode");
        assert_eq!(input.target_root, our_tgt_root, "AttestationData.target_root: lh-encode, ours-decode");

        let ssz_rs_bytes = {
            let mut buf = Vec::new();
            ssz_rs::Serialize::serialize(&input.att_slot, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.att_index, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.att_beacon_block_root, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.source_epoch, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.source_root, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.target_epoch, &mut buf).unwrap();
            ssz_rs::Serialize::serialize(&input.target_root, &mut buf).unwrap();
            buf
        };
        let our_att_slot = u64::from_ssz_bytes(&ssz_rs_bytes[0..8]).unwrap();
        let our_att_index = u64::from_ssz_bytes(&ssz_rs_bytes[8..16]).unwrap();
        let our_bbr = <[u8; 32]>::from_ssz_bytes(&ssz_rs_bytes[16..48]).unwrap();
        let our_src_epoch = u64::from_ssz_bytes(&ssz_rs_bytes[48..56]).unwrap();
        let our_src_root = <[u8; 32]>::from_ssz_bytes(&ssz_rs_bytes[56..88]).unwrap();
        let our_tgt_epoch = u64::from_ssz_bytes(&ssz_rs_bytes[88..96]).unwrap();
        let our_tgt_root = <[u8; 32]>::from_ssz_bytes(&ssz_rs_bytes[96..128]).unwrap();
        assert_eq!(input.att_slot, our_att_slot, "AttestationData.slot: ssz_rs-encode, ours-decode");
        assert_eq!(input.att_index, our_att_index, "AttestationData.index: ssz_rs-encode, ours-decode");
        assert_eq!(input.att_beacon_block_root, our_bbr, "AttestationData.bbr: ssz_rs-encode, ours-decode");
        assert_eq!(input.source_epoch, our_src_epoch, "AttestationData.source_epoch: ssz_rs-encode, ours-decode");
        assert_eq!(input.source_root, our_src_root, "AttestationData.source_root: ssz_rs-encode, ours-decode");
        assert_eq!(input.target_epoch, our_tgt_epoch, "AttestationData.target_epoch: ssz_rs-encode, ours-decode");
        assert_eq!(input.target_root, our_tgt_root, "AttestationData.target_root: ssz_rs-encode, ours-decode");
    }
});
