#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use smallvec::SmallVec;

use ssz::{DecodeError, SszDecode, SszEncode};

use crate::error::IndexError;

/// A fixed-length bitvector of exactly `N` bits, using LSB-first bit ordering.
///
/// Serialized as `ceil(N/8)` bytes. Excess bits (beyond `N`) must be zero.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SszBitvector<const N: usize> {
    bytes: SmallVec<[u8; 64]>,
}

impl<const N: usize> SszBitvector<N> {
    /// The number of bytes required to store `N` bits.
    const BYTE_LEN: usize = N.div_ceil(8);

    /// Create a new bitvector with all bits set to zero.
    pub fn new() -> Self {
        Self {
            bytes: SmallVec::from_elem(0, Self::BYTE_LEN),
        }
    }

    /// Returns the fixed bit length `N`.
    pub fn len(&self) -> usize {
        N
    }

    /// Returns `true` if `N == 0`.
    pub fn is_empty(&self) -> bool {
        N == 0
    }

    /// Get the bit at position `index` (LSB-first ordering).
    ///
    /// Returns `None` if `index >= N`.
    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= N {
            return None;
        }
        let byte_index = index / 8;
        let bit_index = index % 8;
        Some((self.bytes[byte_index] >> bit_index) & 1 == 1)
    }

    /// Set the bit at position `index` to `value` (LSB-first ordering).
    ///
    /// Returns the previous value of the bit on success, or `IndexError` if
    /// `index >= N`.
    pub fn set(&mut self, index: usize, value: bool) -> Result<bool, IndexError> {
        if index >= N {
            return Err(IndexError { index, len: N });
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

    /// Returns the underlying bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the number of bits set to `true`.
    pub fn count_ones(&self) -> usize {
        self.bytes.iter().map(|b| b.count_ones() as usize).sum()
    }

    /// Validate that excess bits beyond `N` are zero.
    fn validate_excess_bits(bytes: &[u8]) -> Result<(), DecodeError> {
        if N == 0 {
            return Ok(());
        }
        let excess = N % 8;
        if excess != 0 {
            let last = bytes[bytes.len() - 1];
            let mask = !((1u8 << excess) - 1);
            if last & mask != 0 {
                return Err(DecodeError::ExcessBitsNotZero);
            }
        }
        Ok(())
    }
}

impl<const N: usize> Default for SszBitvector<N> {
    fn default() -> Self {
        Self::new()
    }
}

// ── SSZ Encoding ──

impl<const N: usize> SszEncode for SszBitvector<N> {
    fn is_fixed_size() -> bool {
        true
    }

    fn fixed_size() -> usize {
        Self::BYTE_LEN
    }

    fn encoded_len(&self) -> usize {
        Self::BYTE_LEN
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.bytes);
    }
}

// ── SSZ Decoding ──

impl<const N: usize> SszDecode for SszBitvector<N> {
    fn is_fixed_size() -> bool {
        true
    }

    fn fixed_size() -> usize {
        Self::BYTE_LEN
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != Self::BYTE_LEN {
            return Err(DecodeError::InvalidFixedLength {
                expected: Self::BYTE_LEN,
                got: bytes.len(),
            });
        }
        Self::validate_excess_bits(bytes)?;
        let mut sv = SmallVec::with_capacity(Self::BYTE_LEN);
        sv.extend_from_slice(bytes);
        Ok(Self { bytes: sv })
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn new_all_zeros() {
        let bv = SszBitvector::<16>::new();
        for i in 0..16 {
            assert_eq!(bv.get(i), Some(false));
        }
    }

    #[test]
    fn get_out_of_bounds() {
        let bv = SszBitvector::<8>::new();
        assert_eq!(bv.get(8), None);
        assert_eq!(bv.get(100), None);
    }

    #[test]
    fn set_and_get_lsb_first() {
        let mut bv = SszBitvector::<8>::new();
        assert_eq!(bv.set(0, true), Ok(false));
        assert_eq!(bv.set(2, true), Ok(false));
        assert_eq!(bv.get(0), Some(true));
        assert_eq!(bv.get(1), Some(false));
        assert_eq!(bv.get(2), Some(true));
        // LSB-first: bit 0 is least significant bit of byte 0
        // bits 0,2 set => 0b00000101 = 5
        assert_eq!(bv.as_bytes()[0], 0b0000_0101);
    }

    #[test]
    fn set_out_of_bounds() {
        let mut bv = SszBitvector::<8>::new();
        assert_eq!(bv.set(8, true), Err(IndexError { index: 8, len: 8 }));
        assert_eq!(bv.set(100, true), Err(IndexError { index: 100, len: 8 }));
    }

    #[test]
    fn set_clear_bit() {
        let mut bv = SszBitvector::<8>::new();
        assert_eq!(bv.set(3, true), Ok(false));
        assert_eq!(bv.get(3), Some(true));
        assert_eq!(bv.set(3, false), Ok(true));
        assert_eq!(bv.get(3), Some(false));
    }

    #[test]
    fn encode_packs_lsb_first() {
        let mut bv = SszBitvector::<8>::new();
        bv.set(0, true).unwrap();
        bv.set(7, true).unwrap();
        let encoded = bv.to_ssz();
        assert_eq!(encoded, vec![0b1000_0001]);
    }

    #[test]
    fn encode_decode_roundtrip_n8() {
        let mut bv = SszBitvector::<8>::new();
        bv.set(1, true).unwrap();
        bv.set(5, true).unwrap();
        let encoded = bv.to_ssz();
        let decoded = SszBitvector::<8>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bv, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_n1() {
        let mut bv = SszBitvector::<1>::new();
        bv.set(0, true).unwrap();
        let encoded = bv.to_ssz();
        assert_eq!(encoded.len(), 1);
        assert_eq!(encoded[0], 0b0000_0001);
        let decoded = SszBitvector::<1>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bv, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_n7() {
        let mut bv = SszBitvector::<7>::new();
        bv.set(6, true).unwrap();
        let encoded = bv.to_ssz();
        assert_eq!(encoded.len(), 1);
        let decoded = SszBitvector::<7>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bv, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_n9() {
        let mut bv = SszBitvector::<9>::new();
        bv.set(8, true).unwrap();
        let encoded = bv.to_ssz();
        assert_eq!(encoded.len(), 2);
        let decoded = SszBitvector::<9>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bv, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_n256() {
        let mut bv = SszBitvector::<256>::new();
        bv.set(0, true).unwrap();
        bv.set(127, true).unwrap();
        bv.set(255, true).unwrap();
        let encoded = bv.to_ssz();
        assert_eq!(encoded.len(), 32);
        let decoded = SszBitvector::<256>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(bv, decoded);
    }

    #[test]
    fn decode_wrong_length() {
        let err = SszBitvector::<8>::from_ssz_bytes(&[0, 0]).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidFixedLength {
                expected: 1,
                got: 2
            }
        );
    }

    #[test]
    fn decode_validates_excess_bits_n7() {
        // N=7: only lower 7 bits of the single byte can be set
        // Set bit 7 (the excess bit) => should fail
        let err = SszBitvector::<7>::from_ssz_bytes(&[0b1000_0000]).unwrap_err();
        assert_eq!(err, DecodeError::ExcessBitsNotZero);
    }

    #[test]
    fn decode_validates_excess_bits_n9() {
        // N=9: 2 bytes needed. Only 1 bit in the second byte (bit 0) is valid.
        // Set bit 1 of second byte => excess bit
        let err = SszBitvector::<9>::from_ssz_bytes(&[0xFF, 0b0000_0011]).unwrap_err();
        assert_eq!(err, DecodeError::ExcessBitsNotZero);
    }

    #[test]
    fn decode_valid_excess_bits_n9() {
        // N=9: second byte can have bit 0 set
        let bv = SszBitvector::<9>::from_ssz_bytes(&[0xFF, 0b0000_0001]).unwrap();
        for i in 0..9 {
            assert_eq!(bv.get(i), Some(true));
        }
    }

    #[test]
    fn bitvector_is_fixed_size() {
        assert!(<SszBitvector<8> as SszEncode>::is_fixed_size());
        assert_eq!(<SszBitvector<8> as SszEncode>::fixed_size(), 1);
        assert_eq!(<SszBitvector<9> as SszEncode>::fixed_size(), 2);
        assert_eq!(<SszBitvector<256> as SszEncode>::fixed_size(), 32);
    }

    #[test]
    fn default_creates_all_zeros() {
        let bv = SszBitvector::<16>::default();
        for i in 0..16 {
            assert_eq!(bv.get(i), Some(false));
        }
    }

    #[test]
    fn is_empty_for_zero_length() {
        let bv = SszBitvector::<0>::new();
        assert!(bv.is_empty());
        assert_eq!(bv.len(), 0);
    }

    #[test]
    fn as_bytes_returns_raw_storage() {
        let mut bv = SszBitvector::<16>::new();
        bv.set(0, true).unwrap();
        bv.set(8, true).unwrap();
        // Byte 0: bit 0 set = 0x01, Byte 1: bit 0 set = 0x01
        assert_eq!(bv.as_bytes(), &[0x01, 0x01]);
    }

    #[test]
    fn decode_is_fixed_size() {
        assert!(<SszBitvector<8> as SszDecode>::is_fixed_size());
        assert_eq!(<SszBitvector<8> as SszDecode>::fixed_size(), 1);
        assert_eq!(<SszBitvector<256> as SszDecode>::fixed_size(), 32);
    }

    #[test]
    fn excess_bits_validated_on_non_byte_aligned() {
        // N=3: only lower 3 bits valid. Byte with bit 3 set should fail.
        let err = SszBitvector::<3>::from_ssz_bytes(&[0b0000_1000]).unwrap_err();
        assert_eq!(err, DecodeError::ExcessBitsNotZero);

        // Valid: only lower 3 bits set
        let bv = SszBitvector::<3>::from_ssz_bytes(&[0b0000_0111]).unwrap();
        assert_eq!(bv.get(0), Some(true));
        assert_eq!(bv.get(1), Some(true));
        assert_eq!(bv.get(2), Some(true));
    }

    #[test]
    fn count_ones_all_zeros() {
        let bv = SszBitvector::<16>::new();
        assert_eq!(bv.count_ones(), 0);
    }

    #[test]
    fn count_ones_mixed() {
        let mut bv = SszBitvector::<8>::new();
        bv.set(0, true).unwrap();
        bv.set(3, true).unwrap();
        bv.set(7, true).unwrap();
        assert_eq!(bv.count_ones(), 3);
    }

    #[test]
    fn count_ones_all_ones() {
        let mut bv = SszBitvector::<8>::new();
        for i in 0..8 {
            bv.set(i, true).unwrap();
        }
        assert_eq!(bv.count_ones(), 8);
    }

    #[test]
    fn count_ones_non_byte_aligned() {
        let mut bv = SszBitvector::<5>::new();
        for i in 0..5 {
            bv.set(i, true).unwrap();
        }
        assert_eq!(bv.count_ones(), 5);
    }

    #[test]
    fn count_ones_zero_length() {
        let bv = SszBitvector::<0>::new();
        assert_eq!(bv.count_ones(), 0);
    }
}
