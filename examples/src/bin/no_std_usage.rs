//! Demonstrates the no_std usage pattern for libssz.
//!
//! In a real no_std binary or library, you would configure your Cargo.toml as:
//!
//! ```toml,ignore
//! [dependencies]
//! ssz = { version = "0.1", default-features = false, features = ["alloc"] }
//! ```
//!
//! And in your crate root:
//!
//! ```rust,ignore
//! #![no_std]
//! extern crate alloc;
//!
//! use alloc::vec::Vec;
//! use ssz::{SszEncode, SszDecode};
//!
//! fn encode_slot(slot: u64) -> Vec<u8> {
//!     slot.to_ssz()
//! }
//!
//! fn decode_slot(bytes: &[u8]) -> Result<u64, ssz::DecodeError> {
//!     u64::from_ssz_bytes(bytes)
//! }
//! ```
//!
//! Key points:
//! - Use `default-features = false` to disable the `std` feature.
//! - Add `features = ["alloc"]` because SSZ encoding requires heap allocation.
//! - The `alloc` feature gives you `Vec`, `SszEncode::to_ssz()`, and all
//!   standard implementations.
//! - Without `alloc`, only the trait definitions are available (no impls).
//! - Each crate propagates features: `ssz-types = { features = ["alloc"] }`
//!   automatically enables `ssz/alloc`.

use ssz::{SszDecode, SszEncode};

fn main() {
    // This example runs in a std environment but demonstrates the same API
    // that works in no_std + alloc.
    let slot: u64 = 12345;
    let encoded = slot.to_ssz();
    let decoded = u64::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(slot, decoded);

    println!("no_std pattern: u64 round-trip OK (slot={decoded})");
    println!();
    println!("To use in a real no_std project:");
    println!("  1. Add `ssz` with default-features = false, features = [\"alloc\"]");
    println!("  2. Add #![no_std] and extern crate alloc to your crate root");
    println!("  3. Use the same SszEncode/SszDecode API as in std");
}
