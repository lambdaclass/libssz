#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod encode;
mod decode;
mod error;

pub use encode::{SszEncode, ContainerEncoder};
pub use decode::{SszDecode, ContainerDecoder};
pub use error::DecodeError;

pub const BYTES_PER_LENGTH_OFFSET: usize = 4;
pub const BYTES_PER_CHUNK: usize = 32;
