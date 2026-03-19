use alloc::vec::Vec;
use libssz::{DecodeError, SszDecode, SszEncode};
use smallvec::SmallVec;

use crate::error::IndexError;
use libssz_merkle::{merkleize_progressive, mix_in_length, pack_bits, HashTreeRoot, Node};

/// A progressive bitlist: ordered variable-length collection of booleans **without limit**.
///
/// Serialization is identical to `Bitlist[N]` (uses delimiter bit).
/// Merkleization uses progressive merkleization (EIP-7916) instead of a fixed binary tree.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProgressiveBitlist {
    bytes: SmallVec<[u8; 64]>,
    len: usize,
}

impl ProgressiveBitlist {
    pub fn new() -> Self {
        Self {
            bytes: SmallVec::new(),
            len: 0,
        }
    }

    pub fn with_length(len: usize) -> Self {
        let byte_len = len.div_ceil(8);
        Self {
            bytes: SmallVec::from_elem(0, byte_len),
            len,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len {
            return None;
        }
        let byte = self.bytes[index / 8];
        Some(byte & (1 << (index % 8)) != 0)
    }

    pub fn set(&mut self, index: usize, value: bool) -> Result<bool, IndexError> {
        if index >= self.len {
            return Err(IndexError {
                index,
                len: self.len,
            });
        }
        let byte_index = index / 8;
        let bit_index = index % 8;
        let previous = (self.bytes[byte_index] >> bit_index) & 1 == 1;
        if value {
            self.bytes[byte_index] |= 1 << bit_index;
        } else {
            self.bytes[byte_index] &= !(1 << bit_index);
        }
        Ok(previous)
    }

    pub fn push(&mut self, value: bool) {
        let byte_index = self.len / 8;
        let bit_index = self.len % 8;
        if byte_index >= self.bytes.len() {
            self.bytes.push(0);
        }
        if value {
            self.bytes[byte_index] |= 1 << bit_index;
        }
        self.len += 1;
    }

    /// Returns the underlying data bytes (without delimiter bit).
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the number of bits set to `true`.
    pub fn count_ones(&self) -> usize {
        self.bytes.iter().map(|b| b.count_ones() as usize).sum()
    }
}

impl Default for ProgressiveBitlist {
    fn default() -> Self {
        Self::new()
    }
}

// ── SszEncode: same as Bitlist (with delimiter bit) ──

impl SszEncode for ProgressiveBitlist {
    fn is_fixed_size() -> bool {
        false
    }

    fn fixed_size() -> usize {
        0
    }

    fn encoded_len(&self) -> usize {
        (self.len + 1).div_ceil(8)
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        if self.len == 0 {
            buf.push(1);
            return;
        }

        let encoded_len = self.encoded_len();
        let start = buf.len();
        buf.extend_from_slice(&self.bytes);

        while buf.len() - start < encoded_len {
            buf.push(0);
        }

        let delim_byte_index = self.len / 8;
        let delim_bit_index = self.len % 8;
        buf[start + delim_byte_index] |= 1 << delim_bit_index;
    }
}

// ── SszDecode: same as Bitlist but no limit check ──

impl SszDecode for ProgressiveBitlist {
    fn is_fixed_size() -> bool {
        false
    }

    fn fixed_size() -> usize {
        0
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.is_empty() {
            return Err(DecodeError::MissingDelimiterBit);
        }

        let last_byte = bytes[bytes.len() - 1];
        if last_byte == 0 {
            return Err(DecodeError::MissingDelimiterBit);
        }

        let highest_bit = 7 - last_byte.leading_zeros() as usize;
        let bit_len = (bytes.len() - 1) * 8 + highest_bit;

        // Copy bytes, clear the delimiter bit
        let mut data = SmallVec::from_slice(bytes);
        data[bytes.len() - 1] &= !(1 << highest_bit);

        // Trim trailing zero bytes
        let needed_bytes = bit_len.div_ceil(8);
        data.truncate(needed_bytes);

        Ok(Self {
            bytes: data,
            len: bit_len,
        })
    }
}

// ── HashTreeRoot: progressive merkleization ──
// mix_in_length(merkleize_progressive(pack_bits(bytes, len)), len)

impl HashTreeRoot for ProgressiveBitlist {
    fn hash_tree_root(&self) -> Node {
        let length = self.len;
        let chunks = pack_bits(self.as_bytes(), length);
        let root = merkleize_progressive(&chunks);
        mix_in_length(&root, length)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::IndexError;

    #[test]
    fn set_returns_previous_value() {
        let mut pb = ProgressiveBitlist::with_length(8);
        assert_eq!(pb.set(0, true), Ok(false));
        assert_eq!(pb.set(0, true), Ok(true));
        assert_eq!(pb.set(0, false), Ok(true));
        assert_eq!(pb.set(0, false), Ok(false));
    }

    #[test]
    fn set_out_of_bounds_returns_error() {
        let mut pb = ProgressiveBitlist::with_length(3);
        assert_eq!(pb.set(3, true), Err(IndexError { index: 3, len: 3 }));
        assert_eq!(pb.set(100, true), Err(IndexError { index: 100, len: 3 }));
    }

    #[test]
    fn count_ones_empty() {
        let pb = ProgressiveBitlist::new();
        assert_eq!(pb.count_ones(), 0);
    }

    #[test]
    fn count_ones_mixed() {
        let mut pb = ProgressiveBitlist::with_length(5);
        pb.set(0, true).unwrap();
        pb.set(2, true).unwrap();
        pb.set(4, true).unwrap();
        assert_eq!(pb.count_ones(), 3);
    }

    #[test]
    fn count_ones_all_zeros() {
        let pb = ProgressiveBitlist::with_length(10);
        assert_eq!(pb.count_ones(), 0);
    }

    #[test]
    fn count_ones_all_ones() {
        let mut pb = ProgressiveBitlist::with_length(8);
        for i in 0..8 {
            pb.set(i, true).unwrap();
        }
        assert_eq!(pb.count_ones(), 8);
    }

    #[test]
    fn count_ones_non_byte_aligned() {
        let mut pb = ProgressiveBitlist::with_length(5);
        for i in 0..5 {
            pb.set(i, true).unwrap();
        }
        assert_eq!(pb.count_ones(), 5);
    }
}
