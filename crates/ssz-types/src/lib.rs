#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod error;
mod vector;
mod list;
mod bitvector;
mod bitlist;
mod union;
mod hash_tree_root;

pub use error::TypeError;
pub use vector::SszVector;
pub use list::SszList;
pub use bitvector::SszBitvector;
pub use bitlist::SszBitlist;
pub use union::{UnionSelector, split_union_bytes, join_union_bytes};
