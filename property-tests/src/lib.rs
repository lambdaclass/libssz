//! Property-based tests for libssz, written with [ephyra](https://github.com/datadog-labs/ephyra).
//!
//! The library half of this crate holds what the properties in `tests/` share:
//!
//! - [`types`]: SSZ types that mix every kind of field the derive supports
//!   (bounded and progressive collections, bitfields, unions, progressive
//!   containers, vectors of variable-size items).
//! - [`recipes`]: plain values ephyra generates and shrinks, each with a
//!   `build` that turns it into one of those types. Generating a recipe
//!   instead of the type keeps every input valid by construction and lets
//!   ephyra shrink it structurally.
//! - [`reference`](mod@reference): a deliberately naive model of the SSZ spec (full-width
//!   Merkle trees, bit-by-bit packing) that shares no code with libssz.
//! - [`edits`]: byte edits applied to a valid encoding, to reach the inputs a
//!   decoder must reject (or must decode canonically).
//! - [`oracles`]: the checks the encoding properties share.

pub mod edits;
pub mod oracles;
pub mod recipes;
pub mod reference;
pub mod types;
