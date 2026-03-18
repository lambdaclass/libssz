use ssz::{DecodeError, SszDecode, SszEncode};
use ssz_merkle::{mix_in_selector, HashTreeRoot, Node};
use ssz_types::split_union_bytes;

use super::progressive_containers::{
    ProgressiveSingleFieldContainerTestStruct, ProgressiveSingleListContainerTestStruct,
    ProgressiveVarTestStruct,
};

// ── CompatibleUnionA ──
// CompatibleUnion({1: ProgressiveSingleFieldContainerTestStruct})

#[derive(Debug, Clone, PartialEq)]
pub enum CompatibleUnionA {
    V1(ProgressiveSingleFieldContainerTestStruct),
}

impl SszEncode for CompatibleUnionA {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V1(v) => 1 + v.encoded_len(),
        }
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        match self {
            Self::V1(v) => {
                buf.push(1);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for CompatibleUnionA {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            1 => Ok(Self::V1(
                ProgressiveSingleFieldContainerTestStruct::from_ssz_bytes(data)?,
            )),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for CompatibleUnionA {
    fn hash_tree_root(&self) -> Node {
        match self {
            Self::V1(v) => mix_in_selector(&v.hash_tree_root(), 1),
        }
    }
}

// ── CompatibleUnionBC ──
// CompatibleUnion({2: ProgressiveSingleListContainerTestStruct, 3: ProgressiveVarTestStruct})

#[derive(Debug, Clone, PartialEq)]
pub enum CompatibleUnionBC {
    V2(ProgressiveSingleListContainerTestStruct),
    V3(ProgressiveVarTestStruct),
}

impl SszEncode for CompatibleUnionBC {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V2(v) => 1 + v.encoded_len(),
            Self::V3(v) => 1 + v.encoded_len(),
        }
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        match self {
            Self::V2(v) => {
                buf.push(2);
                v.ssz_append(buf);
            }
            Self::V3(v) => {
                buf.push(3);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for CompatibleUnionBC {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            2 => Ok(Self::V2(
                ProgressiveSingleListContainerTestStruct::from_ssz_bytes(data)?,
            )),
            3 => Ok(Self::V3(ProgressiveVarTestStruct::from_ssz_bytes(data)?)),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for CompatibleUnionBC {
    fn hash_tree_root(&self) -> Node {
        match self {
            Self::V2(v) => mix_in_selector(&v.hash_tree_root(), 2),
            Self::V3(v) => mix_in_selector(&v.hash_tree_root(), 3),
        }
    }
}

// ── CompatibleUnionABCA ──
// CompatibleUnion({1: ProgressiveSingleFieldContainerTestStruct,
//                  2: ProgressiveSingleListContainerTestStruct,
//                  3: ProgressiveVarTestStruct,
//                  4: ProgressiveSingleFieldContainerTestStruct})

#[derive(Debug, Clone, PartialEq)]
pub enum CompatibleUnionABCA {
    V1(ProgressiveSingleFieldContainerTestStruct),
    V2(ProgressiveSingleListContainerTestStruct),
    V3(ProgressiveVarTestStruct),
    V4(ProgressiveSingleFieldContainerTestStruct),
}

impl SszEncode for CompatibleUnionABCA {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn encoded_len(&self) -> usize {
        match self {
            Self::V1(v) | Self::V4(v) => 1 + v.encoded_len(),
            Self::V2(v) => 1 + v.encoded_len(),
            Self::V3(v) => 1 + v.encoded_len(),
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
            Self::V3(v) => {
                buf.push(3);
                v.ssz_append(buf);
            }
            Self::V4(v) => {
                buf.push(4);
                v.ssz_append(buf);
            }
        }
    }
}

impl SszDecode for CompatibleUnionABCA {
    fn is_fixed_size() -> bool {
        false
    }
    fn fixed_size() -> usize {
        0
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let (selector, data) = split_union_bytes(bytes)?;
        match selector.value() {
            1 => Ok(Self::V1(
                ProgressiveSingleFieldContainerTestStruct::from_ssz_bytes(data)?,
            )),
            2 => Ok(Self::V2(
                ProgressiveSingleListContainerTestStruct::from_ssz_bytes(data)?,
            )),
            3 => Ok(Self::V3(ProgressiveVarTestStruct::from_ssz_bytes(data)?)),
            4 => Ok(Self::V4(
                ProgressiveSingleFieldContainerTestStruct::from_ssz_bytes(data)?,
            )),
            s => Err(DecodeError::InvalidUnionSelector(s)),
        }
    }
}

impl HashTreeRoot for CompatibleUnionABCA {
    fn hash_tree_root(&self) -> Node {
        match self {
            Self::V1(v) => mix_in_selector(&v.hash_tree_root(), 1),
            Self::V2(v) => mix_in_selector(&v.hash_tree_root(), 2),
            Self::V3(v) => mix_in_selector(&v.hash_tree_root(), 3),
            Self::V4(v) => mix_in_selector(&v.hash_tree_root(), 4),
        }
    }
}
