#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod decode;
mod encode;
mod error;

#[cfg(feature = "ethereum_types")]
mod ethereum_types;

pub use decode::{decode_list_with_max, ContainerDecoder, SszDecode};
pub use encode::{ContainerEncoder, SszEncode};
pub use error::DecodeError;

/// Paths that `libssz-derive`'s generated code names. Not public API.
///
/// Generated code expands in the user's crate, where a `#![no_std]` crate has
/// no `Vec` in scope, so it reaches `Vec` through `libssz` instead.
#[doc(hidden)]
pub mod __private {
    #[cfg(feature = "alloc")]
    pub use alloc::vec::Vec;
}

pub const BYTES_PER_LENGTH_OFFSET: usize = 4;
pub const BYTES_PER_CHUNK: usize = 32;
