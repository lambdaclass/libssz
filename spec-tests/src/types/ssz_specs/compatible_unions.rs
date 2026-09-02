//! Types from the ssz-specs `test_compatible_unions` fillers.
//!
//! EIP-8016 `CompatibleUnion`s carry an explicit selector per option, so they
//! are written out by hand: the `enum_behaviour = "union"` derive assigns
//! selectors sequentially from zero, and selector 0 is reserved here.

use libssz::{DecodeError, SszDecode, SszEncode};
use libssz_derive::{HashTreeRoot as HashTreeRootDerive, SszDecode, SszEncode};
use libssz_merkle::{mix_in_selector, HashTreeRoot, Node, Sha256Hasher};
use libssz_types::{split_union_bytes, ProgressiveList};

use super::progressive_containers::{
    SampleCircle, SampleSquare, SampleSquareProgressiveList, SampleUint16List4,
};

/// Progressive list of the second shape, differing only in the element type.
pub type SampleCircleProgressiveList = ProgressiveList<SampleCircle>;

/// Progressive list of unions, whose variable-size bodies need an offset table.
pub type SampleShapeProgressiveList = ProgressiveList<SampleShape>;

// ── SampleShape ──
// CompatibleUnion({1: SampleSquare, 2: SampleCircle, 127: SampleSquare})

/// EIP-8016's own example, with the first shape repeated under the highest selector.
#[derive(Debug, Clone, PartialEq)]
pub enum SampleShape {
    V1(SampleSquare),
    V2(SampleCircle),
    V127(SampleSquare),
}

impl SszEncode for SampleShape {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V1(v) => 1 + v.encoded_len(),
            Self::V2(v) => 1 + v.encoded_len(),
            Self::V127(v) => 1 + v.encoded_len(),
        }
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        match self {
            Self::V1(v) => {
                buf.push(1);
                v.ssz_append(buf);
            }
            Self::V2(v) => {
                buf.push(2);
                v.ssz_append(buf);
            }
            Self::V127(v) => {
                buf.push(127);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for SampleShape {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            1 => Ok(Self::V1(SampleSquare::from_ssz_bytes(data)?)),
            2 => Ok(Self::V2(SampleCircle::from_ssz_bytes(data)?)),
            127 => Ok(Self::V127(SampleSquare::from_ssz_bytes(data)?)),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for SampleShape {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        match self {
            Self::V1(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 1),
            Self::V2(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 2),
            Self::V127(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 127),
        }
    }
}

// ── SampleNumbers ──
// CompatibleUnion({1: SampleUint16List4, 2: SampleUint16List4})

/// Union over a variable-size option, so the payload has no fixed width.
///
/// Both options are the same list type: `SampleUint16List4Alias` in the fillers
/// is a second spelling of `SampleUint16List4`, compatible by the identity rule.
#[derive(Debug, Clone, PartialEq)]
pub enum SampleNumbers {
    V1(SampleUint16List4),
    V2(SampleUint16List4),
}

impl SszEncode for SampleNumbers {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V1(v) => 1 + v.encoded_len(),
            Self::V2(v) => 1 + v.encoded_len(),
        }
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        match self {
            Self::V1(v) => {
                buf.push(1);
                v.ssz_append(buf);
            }
            Self::V2(v) => {
                buf.push(2);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for SampleNumbers {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            1 => Ok(Self::V1(SampleUint16List4::from_ssz_bytes(data)?)),
            2 => Ok(Self::V2(SampleUint16List4::from_ssz_bytes(data)?)),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for SampleNumbers {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        match self {
            Self::V1(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 1),
            Self::V2(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 2),
        }
    }
}

// ── SampleEmptyProne ──
// CompatibleUnion({1: SampleSquareProgressiveList, 2: SampleCircleProgressiveList})

/// Union whose options differ only in the element type of a progressive list,
/// so an empty list on either side encodes to the selector byte alone.
#[derive(Debug, Clone, PartialEq)]
pub enum SampleEmptyProne {
    V1(SampleSquareProgressiveList),
    V2(SampleCircleProgressiveList),
}

impl SszEncode for SampleEmptyProne {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V1(v) => 1 + v.encoded_len(),
            Self::V2(v) => 1 + v.encoded_len(),
        }
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        match self {
            Self::V1(v) => {
                buf.push(1);
                v.ssz_append(buf);
            }
            Self::V2(v) => {
                buf.push(2);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for SampleEmptyProne {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            1 => Ok(Self::V1(SampleSquareProgressiveList::from_ssz_bytes(data)?)),
            2 => Ok(Self::V2(SampleCircleProgressiveList::from_ssz_bytes(data)?)),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for SampleEmptyProne {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        match self {
            Self::V1(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 1),
            Self::V2(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 2),
        }
    }
}

// ── SampleSquareOnly ──
// CompatibleUnion({5: SampleSquare})

/// Single-option union, the second member of the union of unions below.
#[derive(Debug, Clone, PartialEq)]
pub enum SampleSquareOnly {
    V5(SampleSquare),
}

impl SszEncode for SampleSquareOnly {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V5(v) => 1 + v.encoded_len(),
        }
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        match self {
            Self::V5(v) => {
                buf.push(5);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for SampleSquareOnly {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            5 => Ok(Self::V5(SampleSquare::from_ssz_bytes(data)?)),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for SampleSquareOnly {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        match self {
            Self::V5(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 5),
        }
    }
}

// ── SampleNestedShape ──
// CompatibleUnion({1: SampleShape, 2: SampleSquareOnly})

/// Union of unions: each option is itself a compatible union.
#[derive(Debug, Clone, PartialEq)]
pub enum SampleNestedShape {
    V1(SampleShape),
    V2(SampleSquareOnly),
}

impl SszEncode for SampleNestedShape {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V1(v) => 1 + v.encoded_len(),
            Self::V2(v) => 1 + v.encoded_len(),
        }
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        match self {
            Self::V1(v) => {
                buf.push(1);
                v.ssz_append(buf);
            }
            Self::V2(v) => {
                buf.push(2);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for SampleNestedShape {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            1 => Ok(Self::V1(SampleShape::from_ssz_bytes(data)?)),
            2 => Ok(Self::V2(SampleSquareOnly::from_ssz_bytes(data)?)),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for SampleNestedShape {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        match self {
            Self::V1(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 1),
            Self::V2(v) => mix_in_selector(hasher, &v.hash_tree_root(hasher), 2),
        }
    }
}

// ── Containers reaching a union ──

/// Ordinary container reaching a union through an offset.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
pub struct SampleShapeContainer {
    pub tag: u64,
    pub body: SampleShape,
}

/// Progressive container reaching a union through an offset, with a gap before it.
#[derive(Debug, Clone, PartialEq, SszEncode, SszDecode, HashTreeRootDerive)]
#[ssz(progressive_container, active_fields = [1, 0, 1])]
pub struct SampleShapeProgressiveContainer {
    pub tag: u64,
    pub body: SampleShape,
}
