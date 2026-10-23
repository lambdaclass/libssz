//! Types from the ssz-specs `test_progressive_types` fillers.

use libssz_derive::{HashTreeRoot as HashTreeRootDerive, SszDecode, SszEncode};
use libssz_types::ProgressiveList;

/// Progressive list of eight-byte elements, with no capacity.
pub type SampleUint64ProgressiveList = ProgressiveList<u64>;

/// Progressive list of composite 32-byte elements, one Merkle leaf each.
pub type SampleBytes32ProgressiveList = ProgressiveList<[u8; 32]>;

/// Progressive list of two-byte elements, used standalone and when nested.
pub type SampleUint16ProgressiveList = ProgressiveList<u16>;

/// Progressive list of variable-size elements, encoded behind an offset table.
pub type SampleNestedProgressiveList = ProgressiveList<SampleUint16ProgressiveList>;

/// Container embedding a progressive list between two fixed-size fields.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
pub struct SampleContainerWithProgressiveList {
    pub a: u16,
    pub b: SampleUint64ProgressiveList,
    pub c: u8,
}
