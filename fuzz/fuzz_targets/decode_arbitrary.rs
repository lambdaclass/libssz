#![no_main]

use libfuzzer_sys::fuzz_target;
use libssz::SszDecode;
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

fuzz_target!(|data: &[u8]| {
    // Primitives
    let _ = u64::from_ssz_bytes(data);
    let _ = Vec::<u64>::from_ssz_bytes(data);

    // Bitfields
    let _ = SszBitlist::<2048>::from_ssz_bytes(data);
    let _ = SszBitvector::<512>::from_ssz_bytes(data);

    // Bounded collections
    let _ = SszList::<u64, 1_048_576>::from_ssz_bytes(data);
    let _ = SszVector::<u64, 100>::from_ssz_bytes(data);
    let _ = SszVector::<[u8; 32], 64>::from_ssz_bytes(data);

    // Containers
    let _ = Validator::from_ssz_bytes(data);
    let _ = BeaconBlockHeader::from_ssz_bytes(data);
});
