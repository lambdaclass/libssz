#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use smallvec::SmallVec;

use libssz::{DecodeError, SszDecode, SszEncode};

use crate::error::{IndexError, TypeError};

/// A variable-length bitlist of at most `N` bits, using LSB-first bit ordering.
///
/// SSZ encoding uses a delimiter bit: the highest set bit in the last byte marks
/// the boundary between data bits and padding. This means the serialized form is
/// `ceil((len + 1) / 8)` bytes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SszBitlist<const N: usize> {
    bytes: SmallVec<[u8; 64]>,
    len: usize,
}

impl<const N: usize> SszBitlist<N> {
    /// Create an empty bitlist.
    pub fn new() -> Self {
        Self {
            bytes: SmallVec::new(),
            len: 0,
        }
    }

    /// Create a bitlist with `len` bits, all set to zero.
    pub fn with_length(len: usize) -> Result<Self, TypeError> {
        if len > N {
            return Err(TypeError::OverCapacity { max: N, got: len });
        }
        let byte_len = len.div_ceil(8);
        Ok(Self {
            bytes: SmallVec::from_elem(0, byte_len),
            len,
        })
    }

    /// Returns the maximum capacity `N`.
    pub fn max_capacity(&self) -> usize {
        N
    }

    /// Returns the current number of bits.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the bitlist has zero bits.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the bit at position `index` (LSB-first ordering).
    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len {
            return None;
        }
        let byte_index = index / 8;
        let bit_index = index % 8;
        Some((self.bytes[byte_index] >> bit_index) & 1 == 1)
    }

    /// Set the bit at position `index` to `value` (LSB-first ordering).
    ///
    /// Returns the previous value of the bit on success, or `IndexError` if
    /// `index >= len`.
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

    /// Returns the raw data bytes (without delimiter bit).
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the number of bits set to `true`.
    pub fn count_ones(&self) -> usize {
        self.bytes.iter().map(|b| b.count_ones() as usize).sum()
    }

    /// Push a bit. Returns `Err` if at capacity.
    pub fn push(&mut self, value: bool) -> Result<(), TypeError> {
        if self.len >= N {
            return Err(TypeError::OverCapacity {
                max: N,
                got: self.len + 1,
            });
        }
        let byte_index = self.len / 8;
        let bit_index = self.len % 8;
        if byte_index >= self.bytes.len() {
            self.bytes.push(0);
        }
        if value {
            self.bytes[byte_index] |= 1 << bit_index;
        }
        self.len += 1;
        Ok(())
    }
}

impl<const N: usize> Default for SszBitlist<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> TryFrom<Vec<bool>> for SszBitlist<N> {
    type Error = TypeError;

    fn try_from(bits: Vec<bool>) -> Result<Self, Self::Error> {
        if bits.len() > N {
            return Err(TypeError::OverCapacity {
                max: N,
                got: bits.len(),
            });
        }
        let mut bl = Self::with_length(bits.len())?;
        for (i, &bit) in bits.iter().enumerate() {
            let _ = bl.set(i, bit);
        }
        Ok(bl)
    }
}

// ── SSZ Encoding ──

impl<const N: usize> SszEncode for SszBitlist<N> {
    fn is_fixed_size() -> bool {
        false
    }

    fn fixed_size() -> usize {
        0
    }

    fn encoded_len(&self) -> usize {
        // Need ceil((len + 1) / 8) bytes for data + delimiter bit
        (self.len + 1).div_ceil(8)
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        if self.len == 0 {
            // Just the delimiter bit: 0b0000_0001
            buf.push(1);
            return;
        }

        // Copy the data bytes
        let encoded_len = self.encoded_len();
        let start = buf.len();
        buf.extend_from_slice(&self.bytes);

        // Pad to encoded_len if needed
        while buf.len() - start < encoded_len {
            buf.push(0);
        }

        // Set the delimiter bit at position `self.len` (0-indexed from start of bitfield)
        let delim_byte_index = self.len / 8;
        let delim_bit_index = self.len % 8;
        buf[start + delim_byte_index] |= 1 << delim_bit_index;
    }
}

// ── SSZ Decoding ──

impl<const N: usize> SszDecode for SszBitlist<N> {
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

        // Find the delimiter bit: the highest set bit in the last byte.
        let last_byte = bytes[bytes.len() - 1];
        if last_byte == 0 {
            return Err(DecodeError::MissingDelimiterBit);
        }

        // Position of highest set bit in the last byte
        let highest_bit = 7 - last_byte.leading_zeros() as usize;
        let bit_len = (bytes.len() - 1) * 8 + highest_bit;

        if bit_len > N {
            return Err(DecodeError::InvalidByteLength {
                expected: N,
                got: bit_len,
            });
        }

        // Validate no bits are set above the delimiter.
        // When highest_bit == 7 the delimiter is the MSB — no bits above it to check.
        if highest_bit < 7 {
            let mask_above_delimiter = !((1u8 << (highest_bit + 1)) - 1);
            if last_byte & mask_above_delimiter != 0 {
                return Err(DecodeError::ExcessBitsNotZero);
            }
        }

        // Copy bytes and clear the delimiter bit
        let mut sv = SmallVec::with_capacity(bytes.len());
        sv.extend_from_slice(bytes);
        sv[bytes.len() - 1] &= !(1 << highest_bit);

        // Trim trailing zero bytes if they are beyond what the bit_len needs
        let needed_bytes = bit_len.div_ceil(8);
        sv.truncate(needed_bytes);

        Ok(Self {
            bytes: sv,
            len: bit_len,
        })
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn empty_bitlist() {
        let bl = SszBitlist::<10>::new();
        assert!(bl.is_empty());
        assert_eq!(bl.len(), 0);
    }

    #[test]
    fn push_within_capacity() {
        let mut bl = SszBitlist::<4>::new();
        bl.push(true).unwrap();
        bl.push(false).unwrap();
        bl.push(true).unwrap();
        assert_eq!(bl.len(), 3);
        assert_eq!(bl.get(0), Some(true));
        assert_eq!(bl.get(1), Some(false));
        assert_eq!(bl.get(2), Some(true));
    }

    #[test]
    fn push_over_capacity() {
        let mut bl = SszBitlist::<2>::new();
        bl.push(true).unwrap();
        bl.push(false).unwrap();
        let err = bl.push(true).unwrap_err();
        assert_eq!(err, TypeError::OverCapacity { max: 2, got: 3 });
    }

    #[test]
    fn get_out_of_bounds() {
        let bl = SszBitlist::<8>::with_length(3).unwrap();
        assert_eq!(bl.get(3), None);
    }

    #[test]
    fn set_and_get() {
        let mut bl = SszBitlist::<8>::with_length(4).unwrap();
        assert_eq!(bl.set(0, true), Ok(false));
        assert_eq!(bl.set(3, true), Ok(false));
        assert_eq!(bl.get(0), Some(true));
        assert_eq!(bl.get(1), Some(false));
        assert_eq!(bl.get(3), Some(true));
        // Setting again returns the previous value
        assert_eq!(bl.set(0, true), Ok(true));
        assert_eq!(bl.set(3, false), Ok(true));
    }

    #[test]
    fn encode_empty_bitlist() {
        let bl = SszBitlist::<10>::new();
        let encoded = bl.to_ssz();
        // Empty bitlist: just the delimiter bit => 0b0000_0001
        assert_eq!(encoded, vec![0b0000_0001]);
    }

    #[test]
    fn encode_delimiter_bit() {
        // 3 bits: [true, false, true]
        // Data bits: positions 0,1,2 => 0b00000_101 (bits 0 and 2 set)
        // Delimiter at position 3 => 0b0000_1101
        let mut bl = SszBitlist::<8>::new();
        bl.push(true).unwrap();
        bl.push(false).unwrap();
        bl.push(true).unwrap();
        let encoded = bl.to_ssz();
        assert_eq!(encoded, vec![0b0000_1101]);
    }

    #[test]
    fn encode_8_bits_needs_2_bytes() {
        // 8 data bits + delimiter = 9 bits = 2 bytes
        let mut bl = SszBitlist::<16>::with_length(8).unwrap();
        bl.set(0, true).unwrap();
        let encoded = bl.to_ssz();
        assert_eq!(encoded.len(), 2);
        // Delimiter bit at position 8 => bit 0 of byte 1
        assert_eq!(encoded[0], 0b0000_0001); // bit 0 set
        assert_eq!(encoded[1], 0b0000_0001); // delimiter
    }

    #[test]
    fn encode_decode_roundtrip_empty() {
        let bl = SszBitlist::<10>::new();
        let encoded = bl.to_ssz();
        let decoded = SszBitlist::<10>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bl, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_3bits() {
        let mut bl = SszBitlist::<8>::new();
        bl.push(true).unwrap();
        bl.push(false).unwrap();
        bl.push(true).unwrap();
        let encoded = bl.to_ssz();
        let decoded = SszBitlist::<8>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bl, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_8bits() {
        let mut bl = SszBitlist::<16>::with_length(8).unwrap();
        for i in 0..8 {
            bl.set(i, i % 2 == 0).unwrap();
        }
        let encoded = bl.to_ssz();
        let decoded = SszBitlist::<16>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bl, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_large() {
        let mut bl = SszBitlist::<512>::with_length(256).unwrap();
        bl.set(0, true).unwrap();
        bl.set(127, true).unwrap();
        bl.set(255, true).unwrap();
        let encoded = bl.to_ssz();
        let decoded = SszBitlist::<512>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bl, decoded);
    }

    #[test]
    fn decode_missing_delimiter_empty_input() {
        let err = SszBitlist::<8>::from_ssz_bytes(&[]).unwrap_err();
        assert_eq!(err, DecodeError::MissingDelimiterBit);
    }

    #[test]
    fn decode_missing_delimiter_zero_byte() {
        let err = SszBitlist::<8>::from_ssz_bytes(&[0x00]).unwrap_err();
        assert_eq!(err, DecodeError::MissingDelimiterBit);
    }

    #[test]
    fn decode_rejects_len_over_n() {
        // Encode a bitlist with 5 bits, try to decode as max 3
        let mut bl = SszBitlist::<8>::with_length(5).unwrap();
        bl.set(0, true).unwrap();
        let encoded = bl.to_ssz();
        let err = SszBitlist::<3>::from_ssz_bytes(&encoded).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidByteLength {
                expected: 3,
                got: 5
            }
        );
    }

    #[test]
    fn bitlist_is_always_variable_size() {
        assert!(!<SszBitlist<8> as SszEncode>::is_fixed_size());
        assert!(!<SszBitlist<256> as SszEncode>::is_fixed_size());
    }

    #[test]
    fn try_from_vec_bool() {
        let bl: SszBitlist<8> = SszBitlist::try_from(vec![true, false, true]).unwrap();
        assert_eq!(bl.len(), 3);
        assert_eq!(bl.get(0), Some(true));
        assert_eq!(bl.get(1), Some(false));
        assert_eq!(bl.get(2), Some(true));
    }

    #[test]
    fn try_from_vec_bool_over_capacity() {
        let err = SszBitlist::<2>::try_from(vec![true, false, true]).unwrap_err();
        assert_eq!(err, TypeError::OverCapacity { max: 2, got: 3 });
    }

    #[test]
    fn with_length_over_capacity() {
        let err = SszBitlist::<4>::with_length(5).unwrap_err();
        assert_eq!(err, TypeError::OverCapacity { max: 4, got: 5 });
    }

    #[test]
    fn max_capacity_returns_n() {
        let bl = SszBitlist::<128>::new();
        assert_eq!(bl.max_capacity(), 128);
    }

    #[test]
    fn default_creates_empty() {
        let bl = SszBitlist::<16>::default();
        assert!(bl.is_empty());
        assert_eq!(bl.len(), 0);
    }

    #[test]
    fn as_bytes_returns_raw_data() {
        let mut bl = SszBitlist::<8>::with_length(4).unwrap();
        bl.set(0, true).unwrap();
        bl.set(2, true).unwrap();
        // LSB-first: bits 0,2 set = 0b00000101 = 5
        assert_eq!(bl.as_bytes(), &[5]);
    }

    #[test]
    fn set_out_of_bounds_returns_error() {
        let mut bl = SszBitlist::<8>::with_length(3).unwrap();
        assert_eq!(bl.set(3, true), Err(IndexError { index: 3, len: 3 }));
        assert_eq!(bl.set(100, true), Err(IndexError { index: 100, len: 3 }));
    }

    #[test]
    fn push_false_bit_does_not_set() {
        let mut bl = SszBitlist::<8>::new();
        bl.push(false).unwrap();
        bl.push(false).unwrap();
        assert_eq!(bl.get(0), Some(false));
        assert_eq!(bl.get(1), Some(false));
        assert_eq!(bl.as_bytes(), &[0]);
    }

    #[test]
    fn decode_is_always_variable() {
        assert!(!<SszBitlist<8> as SszDecode>::is_fixed_size());
        assert_eq!(<SszBitlist<8> as SszDecode>::fixed_size(), 0);
    }

    #[test]
    fn count_ones_empty() {
        let bl = SszBitlist::<10>::new();
        assert_eq!(bl.count_ones(), 0);
    }

    #[test]
    fn count_ones_mixed() {
        let mut bl = SszBitlist::<8>::with_length(5).unwrap();
        bl.set(0, true).unwrap();
        bl.set(2, true).unwrap();
        bl.set(4, true).unwrap();
        assert_eq!(bl.count_ones(), 3);
    }

    #[test]
    fn count_ones_all_zeros() {
        let bl = SszBitlist::<16>::with_length(10).unwrap();
        assert_eq!(bl.count_ones(), 0);
    }

    #[test]
    fn count_ones_all_ones() {
        let mut bl = SszBitlist::<8>::with_length(8).unwrap();
        for i in 0..8 {
            bl.set(i, true).unwrap();
        }
        assert_eq!(bl.count_ones(), 8);
    }

    #[test]
    fn count_ones_non_byte_aligned() {
        let mut bl = SszBitlist::<8>::with_length(5).unwrap();
        for i in 0..5 {
            bl.set(i, true).unwrap();
        }
        assert_eq!(bl.count_ones(), 5);
    }
}
