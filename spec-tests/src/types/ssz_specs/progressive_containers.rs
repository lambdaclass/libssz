//! Types from the ssz-specs `test_progressive_containers` fillers.
//!
//! `SampleSquare` and `SampleCircle` are EIP-7495's own example shapes. They are
//! reused by the `test_compatible_unions` fillers, which spell them identically.

use libssz_derive::{HashTreeRoot as HashTreeRootDerive, SszDecode, SszEncode};
use libssz_types::{ProgressiveBitlist, ProgressiveList, SszList};

/// Bounded list of two-byte elements, used as a variable-size field.
pub type SampleUint16List4 = SszList<u16, 4>;

/// Progressive list of eight-byte elements, used as a variable-size field.
pub type SampleUint64ProgressiveList = ProgressiveList<u64>;

/// Progressive list whose elements are progressive containers.
pub type SampleSquareProgressiveList = ProgressiveList<SampleSquare>;

/// A field at position 0, a gap, then a field at position 2.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 0, 1])]
pub struct SampleSquare {
    pub side: u16,
    pub color: u8,
}

/// The other half of that example: a leading gap, then positions 1 and 2.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [0, 1, 1])]
pub struct SampleCircle {
    pub radius: u16,
    pub color: u8,
}

/// Narrowest legal layout: one position, occupied.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1])]
pub struct SampleOneField {
    pub a: u16,
}

/// Two leading gaps, so the sole field is merkleized at position two.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [0, 0, 1])]
pub struct SampleLeadingGaps {
    pub c: u32,
}

/// Three fields separated by gaps of differing widths.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 0, 0, 1, 0, 1])]
pub struct SampleMultipleGaps {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

/// Widest legal layout: 256 positions, the capacity of the mixed-in word.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(
    progressive_container,
    active_fields = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
)]
pub struct SampleWidestLayout {
    pub tail: u8,
}

/// Twenty-two positions, so the leaves open the width-64 level of the spine.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(
    progressive_container,
    active_fields = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
)]
pub struct SampleLevelBoundary {
    pub first: u16,
    pub last: u8,
}

/// Fixed field, a gap, then a bounded list, so the shape needs one offset.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 0, 1])]
pub struct SampleBoundedListField {
    pub head: u64,
    pub body: SampleUint16List4,
}

/// Fixed field followed by both EIP-7916 shapes, so two offsets follow it.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 1, 1])]
pub struct SampleProgressiveFields {
    pub head: u64,
    pub numbers: SampleUint64ProgressiveList,
    pub flags: ProgressiveBitlist,
}

/// Fixed-size progressive container nested inside another one.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 0, 1])]
pub struct SampleInnerShape {
    pub x: u16,
    pub y: u8,
}

/// Progressive container holding a progressive container as a field.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 0, 1])]
pub struct SampleOuterShape {
    pub head: u8,
    pub inner: SampleInnerShape,
}

/// Ordinary container holding a progressive container as its second field, so
/// it merkleizes with a padded binary tree rather than a progressive spine.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
pub struct SampleShapeContainer {
    pub tag: u8,
    pub shape: SampleSquare,
}
