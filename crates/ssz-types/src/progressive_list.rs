use alloc::vec::Vec;
use core::ops::Deref;
use libssz::{DecodeError, SszDecode, SszEncode};
use libssz_merkle::{merkleize_progressive, mix_in_length, pack, HashTreeRoot, Node};

/// A progressive list: ordered variable-length homogeneous collection **without limit**.
///
/// Serialization is identical to `List[type, N]` / `Vec<T>`.
/// Merkleization uses progressive merkleization (EIP-7916) instead of a fixed binary tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProgressiveList<T>(Vec<T>);

impl<T> ProgressiveList<T> {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    pub fn push(&mut self, value: T) {
        self.0.push(value);
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.0.iter()
    }

    pub fn into_inner(self) -> Vec<T> {
        self.0
    }
}

impl<T> Default for ProgressiveList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Deref for ProgressiveList<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> From<Vec<T>> for ProgressiveList<T> {
    fn from(v: Vec<T>) -> Self {
        Self(v)
    }
}

impl<T> IntoIterator for ProgressiveList<T> {
    type Item = T;
    type IntoIter = alloc::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a ProgressiveList<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

// ── SszEncode: delegate to Vec<T> ──

impl<T: SszEncode> SszEncode for ProgressiveList<T> {
    fn is_fixed_size() -> bool {
        false
    }

    fn fixed_size() -> usize {
        0
    }

    fn encoded_len(&self) -> usize {
        self.0.encoded_len()
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        self.0.ssz_append(buf);
    }
}

// ── SszDecode: delegate to Vec<T> (no limit to check) ──

impl<T: SszDecode> SszDecode for ProgressiveList<T> {
    fn is_fixed_size() -> bool {
        false
    }

    fn fixed_size() -> usize {
        0
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let vec = Vec::<T>::from_ssz_bytes(bytes)?;
        Ok(Self(vec))
    }
}

// ── HashTreeRoot: progressive merkleization ──
// mix_in_length(merkleize_progressive(chunks), len)

impl<T: HashTreeRoot + SszEncode> HashTreeRoot for ProgressiveList<T> {
    fn hash_tree_root(&self) -> Node {
        let length = self.len();

        let chunks: Vec<Node> = if T::is_basic_type() {
            let mut serialized = Vec::new();
            for item in &self.0 {
                item.ssz_append(&mut serialized);
            }
            pack(&serialized)
        } else {
            self.0.iter().map(|item| item.hash_tree_root()).collect()
        };

        let root = merkleize_progressive(&chunks);
        mix_in_length(&root, length)
    }
}
