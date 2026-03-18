use alloc::vec::Vec;
use smallvec::SmallVec;
use ssz::{DecodeError, SszDecode, SszEncode};
use ssz_merkle::{merkleize_progressive, mix_in_length, pack_bits, HashTreeRoot, Node};

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

    pub fn set(&mut self, index: usize, value: bool) {
        assert!(index < self.len, "index out of bounds");
        let byte_index = index / 8;
        let bit_index = index % 8;
        if value {
            self.bytes[byte_index] |= 1 << bit_index;
        } else {
            self.bytes[byte_index] &= !(1 << bit_index);
        }
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
