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

pub const BYTES_PER_LENGTH_OFFSET: usize = 4;
pub const BYTES_PER_CHUNK: usize = 32;
