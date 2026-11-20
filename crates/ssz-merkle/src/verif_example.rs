//! Example containers for the formal proofs of `hash_tree_root` against the EthLib
//! specification.
//!
//! These are the fixed-size consensus-layer containers (phase0) from
//! `crates/ssz/src/verif_example.rs`, with the `#[derive(HashTreeRoot)]` from
//! `crates/ssz-derive`: Charon translates exactly the `hash_tree_root` the macro generates.
//!
//! `Lists` has three `Vec`s: one of basic items (`u64`), one of composite items
//! (`[u8; 48]`, like public keys) and one of `[u8; 4]`, where libssz does not match the
//! specification: libssz treats `[u8; N]` with `N <= 32` as a basic type and packs the items
//! together, while for SSZ a `ByteVector[N]` is composite and each item gets its own node.
//!
//! The five consensus-layer containers also derive `SszEncode`, so they can be items of an
//! `SszList` (see `ssz-types`' `verif_example`): in Rust, the `hash_tree_root` of a list
//! requires the item to implement `SszEncode`.
//!
//! Only compiled with the `verif-example` feature. Not part of the API.

use alloc::vec::Vec;

use libssz::SszEncode;
use libssz_derive::{HashTreeRoot, SszEncode};

#[derive(HashTreeRoot, SszEncode)]
pub struct Checkpoint {
    pub epoch: u64,
    pub root: [u8; 32],
}

#[derive(HashTreeRoot, SszEncode)]
pub struct Fork {
    pub previous_version: [u8; 4],
    pub current_version: [u8; 4],
    pub epoch: u64,
}

#[derive(HashTreeRoot, SszEncode)]
pub struct BeaconBlockHeader {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body_root: [u8; 32],
}

#[derive(HashTreeRoot, SszEncode)]
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

#[derive(HashTreeRoot, SszEncode)]
pub struct AttestationData {
    pub slot: u64,
    pub index: u64,
    pub beacon_block_root: [u8; 32],
    pub source: Checkpoint,
    pub target: Checkpoint,
}

/// Not from the consensus layer: it gathers the integers the containers above do not use, so
/// that their `hash_tree_root`s are part of the extraction too.
#[derive(HashTreeRoot)]
pub struct Uints {
    pub a: u8,
    pub b: u16,
    pub c: u32,
    pub d: u128,
}

/// Three lists: of basic items, of composite items and of `[u8; 4]`.
#[derive(HashTreeRoot)]
pub struct Lists {
    pub a: Vec<u64>,
    pub b: Vec<[u8; 48]>,
    pub c: Vec<[u8; 4]>,
}

/// A `Vec` of each basic type. The `hash_tree_root`s of `Vec<T>` take the item's
/// `HashTreeRoot` implementation, so the extraction brings them in full (with
/// `is_basic_type`), and `ssz-types` uses them.
#[derive(HashTreeRoot)]
pub struct BasicLists {
    pub a: Vec<bool>,
    pub b: Vec<u8>,
    pub c: Vec<u16>,
    pub d: Vec<u32>,
    pub e: Vec<u64>,
    pub f: Vec<u128>,
}

/// Calls each `SszEncode` method once. Each crate is translated to Lean separately, and
/// Charon copies into a crate's translation only the methods of another crate's trait that
/// the code names. The proofs then link that copy to the full trait from the codec's
/// translation, which needs the copy to be complete: this function names every method, so
/// every implementation brings all of them. Not used anywhere else.
pub fn ssz_encode_methods<T: SszEncode>(x: &T, items: &[T], buf: &mut Vec<u8>, out: &mut [u8]) {
    let _ = T::is_fixed_size();
    let _ = T::fixed_size();
    let _ = x.encoded_len();
    x.ssz_append(buf);
    let _ = x.to_ssz();
    T::ssz_append_fixed_slice(items, buf);
    let _ = T::ssz_has_write_fixed();
    x.ssz_write_fixed(out);
    let _ = T::ssz_fixed_slice_to_vec(items);
}
