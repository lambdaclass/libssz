//! SSZ types under test.
//!
//! Limits are small and deliberately not multiples of 8 or of a chunk, so
//! bitfield padding, delimiter bits and partial chunks show up often.

use libssz_derive::{HashTreeRoot, SszDecode, SszEncode};
use libssz_types::{
    ProgressiveBitlist, ProgressiveList, SszBitlist, SszBitvector, SszList, SszVector,
};

/// A container with one fixed and one variable field.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Inner {
    pub a: u16,
    pub xs: SszList<u8, 7>,
}

/// A container mixing fixed fields, lists of composites and of basic types,
/// and both bounded bitfields.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Outer {
    pub x: u32,
    pub inners: SszList<Inner, 5>,
    pub tail: SszList<u64, 3>,
    pub flag: bool,
    pub bits: SszBitlist<20>,
    pub mask: SszBitvector<11>,
}

/// A union with a `None`-like variant, a basic variant and two variable ones.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(enum_behaviour = "union")]
pub enum Choice {
    Nothing,
    Number(u64),
    Bytes(SszList<u8, 40>),
    Nested(Inner),
}

/// A progressive container with an inactive slot and progressive fields.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(progressive_container, active_fields = [1, 0, 1, 1])]
pub struct Sparse {
    pub a: u32,
    pub items: ProgressiveList<u16>,
    pub bits: ProgressiveBitlist,
}

/// Everything above nested together, plus a vector of variable-size items.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Wrapper {
    pub choices: SszList<Choice, 4>,
    pub sparse: Sparse,
    pub pair: SszVector<Inner, 2>,
}

/// An all-fixed container. The derive gives it a fast path with no offsets
/// and overrides its bulk hooks (`ssz_append_fixed_slice`,
/// `ssz_decode_fixed_vec`), which lists and vectors of it go through.
///
/// `[u8; 20]` is a byte vector shorter than a chunk, `[u8; 32]` exactly one
/// chunk; `u128` and `[u8; N]` have their own bulk copies.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Fixed {
    pub a: u32,
    pub root: [u8; 32],
    pub b: u128,
    pub addr: [u8; 20],
    pub slot: Slot,
    pub flag: bool,
}

/// A transparent wrapper around a fixed-size field: encoded and hashed as
/// the `u64` itself.
#[derive(Debug, Clone, Copy, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(transparent)]
pub struct Slot(pub u64);

/// A transparent wrapper around a variable-size field: encoded and hashed
/// as the list itself.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(transparent)]
pub struct Wrapped(pub SszList<u16, 9>);

/// A union whose non-empty variants are all fixed-size.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
#[ssz(enum_behaviour = "union")]
pub enum Tagged {
    Nothing,
    Word(u32),
    Record(Fixed),
    Records(SszVector<Fixed, 2>),
}

/// The shapes the types above leave out: containers nested directly (fixed
/// and variable), lists and vectors of all-fixed containers, vectors and
/// lists of the other basic types and byte vectors, transparent fields and a
/// fixed-variant union.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRoot)]
pub struct Shapes {
    pub record: Fixed,
    pub records: SszList<Fixed, 4>,
    pub pair: SszVector<Fixed, 2>,
    pub words: SszVector<u32, 5>,
    pub wide: SszList<u128, 3>,
    pub roots: SszList<[u8; 32], 3>,
    pub addrs: SszList<[u8; 20], 3>,
    pub slot: Slot,
    pub wrapped: Wrapped,
    pub tagged: Tagged,
    pub inner: Inner,
}
