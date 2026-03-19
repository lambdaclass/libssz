#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use libssz::{SszDecode, SszEncode};
use libssz_derive::{SszDecode, SszEncode};
use libssz_types::{SszBitlist, SszBitvector, SszList, SszVector};

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct Validator {
    pubkey: [u8; 48],
    withdrawal_credentials: [u8; 32],
    effective_balance: u64,
    slashed: bool,
    activation_eligibility_epoch: u64,
    activation_epoch: u64,
    exit_epoch: u64,
    withdrawable_epoch: u64,
}

#[derive(Debug, PartialEq, SszEncode, SszDecode)]
struct BeaconBlockHeader {
    slot: u64,
    proposer_index: u64,
    parent_root: [u8; 32],
    state_root: [u8; 32],
    body_root: [u8; 32],
}

#[derive(Debug, Arbitrary)]
struct FuzzInput {
    pubkey: [u8; 48],
    withdrawal_credentials: [u8; 32],
    effective_balance: u64,
    slashed: bool,
    activation_eligibility_epoch: u64,
    activation_epoch: u64,
    exit_epoch: u64,
    withdrawable_epoch: u64,
    header_slot: u64,
    header_proposer_index: u64,
    header_parent_root: [u8; 32],
    header_state_root: [u8; 32],
    header_body_root: [u8; 32],
    raw: Vec<u8>,
}

fuzz_target!(|input: FuzzInput| {
    // -- Primitive roundtrips from raw bytes --

    if let Ok(val) = u64::from_ssz_bytes(&input.raw) {
        assert_eq!(u64::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = u128::from_ssz_bytes(&input.raw) {
        assert_eq!(u128::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = bool::from_ssz_bytes(&input.raw) {
        assert_eq!(bool::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = Vec::<u64>::from_ssz_bytes(&input.raw) {
        assert_eq!(Vec::<u64>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }

    // -- Bitfield roundtrips --
    if let Ok(val) = SszBitlist::<2048>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitlist::<2048>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszBitvector::<512>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitvector::<512>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }

    // -- Bounded collection roundtrips --
    if let Ok(val) = SszList::<u64, 1_048_576>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszList::<u64, 1_048_576>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszVector::<u64, 100>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszVector::<u64, 100>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }

    // -- Additional bitfield size variations --
    if let Ok(val) = SszBitlist::<1>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitlist::<1>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszBitlist::<8>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitlist::<8>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszBitvector::<1>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitvector::<1>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszBitvector::<64>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitvector::<64>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }

    // -- Boundary collections --
    if let Ok(val) = SszList::<u64, 1>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszList::<u64, 1>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszVector::<u64, 1>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszVector::<u64, 1>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }

    // -- Non-byte-aligned bitvector sizes --
    if let Ok(val) = SszBitvector::<3>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitvector::<3>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszBitvector::<7>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitvector::<7>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszBitvector::<9>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitvector::<9>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }
    if let Ok(val) = SszBitvector::<15>::from_ssz_bytes(&input.raw) {
        assert_eq!(SszBitvector::<15>::from_ssz_bytes(&val.to_ssz()).unwrap(), val);
    }

    // -- Container roundtrips from structured input --

    let validator = Validator {
        pubkey: input.pubkey,
        withdrawal_credentials: input.withdrawal_credentials,
        effective_balance: input.effective_balance,
        slashed: input.slashed,
        activation_eligibility_epoch: input.activation_eligibility_epoch,
        activation_epoch: input.activation_epoch,
        exit_epoch: input.exit_epoch,
        withdrawable_epoch: input.withdrawable_epoch,
    };
    let encoded = validator.to_ssz();
    assert_eq!(Validator::from_ssz_bytes(&encoded).unwrap(), validator);

    let header = BeaconBlockHeader {
        slot: input.header_slot,
        proposer_index: input.header_proposer_index,
        parent_root: input.header_parent_root,
        state_root: input.header_state_root,
        body_root: input.header_body_root,
    };
    let encoded = header.to_ssz();
    assert_eq!(BeaconBlockHeader::from_ssz_bytes(&encoded).unwrap(), header);

    // -- Container decode from raw (no panic) --
    let _ = Validator::from_ssz_bytes(&input.raw);
    let _ = BeaconBlockHeader::from_ssz_bytes(&input.raw);
});
