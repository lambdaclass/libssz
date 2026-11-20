//! Example containers for the formal proofs of the codec against the EthLib specification.
//!
//! They all use the `#[derive(SszEncode, SszDecode)]` from `crates/ssz-derive`: Charon
//! translates exactly the code the macro generates.
//!
//! * `Example` is a variable-size container (`ContainerEncoder` / `ContainerDecoder`).
//! * The others are fixed-size consensus-layer containers (phase0), copied from
//!   `spec-tests/src/types/phase0.rs`. For those the macro uses neither `ContainerEncoder`
//!   nor `ContainerDecoder`: it checks the length and splits off each field with `split_at`.
//!
//! Only compiled with the `verif-example` feature. Not part of the API.

use alloc::vec::Vec;

use libssz_derive::{SszDecode, SszEncode};

#[derive(SszEncode, SszDecode)]
pub struct Example {
    pub a: u64,
    pub b: Vec<u8>,
    pub c: bool,
    pub d: Vec<u16>,
}

#[derive(SszEncode, SszDecode)]
pub struct Checkpoint {
    pub epoch: u64,
    pub root: [u8; 32],
}

#[derive(SszEncode, SszDecode)]
pub struct Fork {
    pub previous_version: [u8; 4],
    pub current_version: [u8; 4],
    pub epoch: u64,
}

#[derive(SszEncode, SszDecode)]
pub struct BeaconBlockHeader {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body_root: [u8; 32],
}

#[derive(SszEncode, SszDecode)]
pub struct Validator {
    pub pubkey: [u8; 48],
    pub withdrawal_credentials: [u8; 32],
    pub effective_balance: u64,
    pub slashed: bool,
    pub activation_eligibility_epoch: u64,
    pub activation_epoch: u64,
    pub exit_epoch: u64,
    pub withdrawable_epoch: u64,
}

#[derive(SszEncode, SszDecode)]
pub struct AttestationData {
    pub slot: u64,
    pub index: u64,
    pub beacon_block_root: [u8; 32],
    pub source: Checkpoint,
    pub target: Checkpoint,
}
