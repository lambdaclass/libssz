#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod bitlist;
mod bitvector;
mod error;
mod hash_tree_root;
mod list;
#[cfg(feature = "alloc")]
mod progressive_bitlist;
#[cfg(feature = "alloc")]
mod progressive_list;
mod union;
mod vector;

pub use bitlist::SszBitlist;
pub use bitvector::SszBitvector;
pub use error::{IndexError, TypeError};
pub use list::SszList;
#[cfg(feature = "alloc")]
pub use progressive_bitlist::ProgressiveBitlist;
#[cfg(feature = "alloc")]
pub use progressive_list::ProgressiveList;
pub use union::{join_union_bytes, split_union_bytes, UnionSelector};
pub use vector::SszVector;
