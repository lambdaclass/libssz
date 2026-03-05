#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod bitlist;
mod bitvector;
mod error;
mod hash_tree_root;
mod list;
mod union;
mod vector;

pub use bitlist::SszBitlist;
pub use bitvector::SszBitvector;
pub use error::TypeError;
pub use list::SszList;
pub use union::{join_union_bytes, split_union_bytes, UnionSelector};
pub use vector::SszVector;
