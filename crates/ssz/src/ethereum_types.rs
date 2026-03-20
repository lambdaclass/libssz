//! SszEncode and SszDecode implementations for `ethereum_types` types.

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use ethereum_types as et;

use crate::error::DecodeError;
use crate::{SszDecode, SszEncode};

// ── H-types (fixed-size byte arrays) ──

impl SszEncode for et::H32 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        4
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        4
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H32 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        4
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 4 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 4,
                got: bytes.len(),
            });
        }
        Ok(et::H32::from_slice(bytes))
    }
}

impl SszEncode for et::H64 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        8
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        8
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H64 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        8
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 8 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 8,
                got: bytes.len(),
            });
        }
        Ok(et::H64::from_slice(bytes))
    }
}

impl SszEncode for et::H128 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        16
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        16
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H128 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        16
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 16 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 16,
                got: bytes.len(),
            });
        }
        Ok(et::H128::from_slice(bytes))
    }
}

impl SszEncode for et::H160 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        20
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        20
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H160 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        20
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 20 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 20,
                got: bytes.len(),
            });
        }
        Ok(et::H160::from_slice(bytes))
    }
}

impl SszEncode for et::H256 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        32
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        32
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H256 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        32
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 32 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 32,
                got: bytes.len(),
            });
        }
        Ok(et::H256::from_slice(bytes))
    }
}

impl SszEncode for et::H264 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        33
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        33
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H264 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        33
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 33 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 33,
                got: bytes.len(),
            });
        }
        Ok(et::H264::from_slice(bytes))
    }
}

impl SszEncode for et::H512 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        64
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        64
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H512 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        64
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 64 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 64,
                got: bytes.len(),
            });
        }
        Ok(et::H512::from_slice(bytes))
    }
}

impl SszEncode for et::H520 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        65
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        65
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_bytes());
    }
}

impl SszDecode for et::H520 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        65
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 65 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 65,
                got: bytes.len(),
            });
        }
        Ok(et::H520::from_slice(bytes))
    }
}

// ── U-types (little-endian unsigned integers) ──

impl SszEncode for et::U64 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        8
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        8
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_little_endian());
    }
}

impl SszDecode for et::U64 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        8
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 8 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 8,
                got: bytes.len(),
            });
        }
        Ok(et::U64::from_little_endian(bytes))
    }
}

impl SszEncode for et::U128 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        16
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        16
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_little_endian());
    }
}

impl SszDecode for et::U128 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        16
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 16 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 16,
                got: bytes.len(),
            });
        }
        Ok(et::U128::from_little_endian(bytes))
    }
}

impl SszEncode for et::U256 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        32
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        32
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_little_endian());
    }
}

impl SszDecode for et::U256 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        32
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 32 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 32,
                got: bytes.len(),
            });
        }
        Ok(et::U256::from_little_endian(bytes))
    }
}

impl SszEncode for et::U512 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        64
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        64
    }
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_little_endian());
    }
}

impl SszDecode for et::U512 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        64
    }
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 64 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 64,
                got: bytes.len(),
            });
        }
        Ok(et::U512::from_little_endian(bytes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // H-type tests

    #[test]
    fn h32_roundtrip() {
        let mut bytes = [0u8; 4];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H32::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 4);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H32::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H32 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H32 as SszEncode>::fixed_size(), 4);
    }

    #[test]
    fn h64_roundtrip() {
        let mut bytes = [0u8; 8];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H64::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 8);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H64::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H64 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H64 as SszEncode>::fixed_size(), 8);
    }

    #[test]
    fn h128_roundtrip() {
        let mut bytes = [0u8; 16];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H128::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 16);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H128::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H128 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H128 as SszEncode>::fixed_size(), 16);
    }

    #[test]
    fn h160_roundtrip() {
        let mut bytes = [0u8; 20];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H160::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 20);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H160::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H160 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H160 as SszEncode>::fixed_size(), 20);
    }

    #[test]
    fn h256_roundtrip() {
        let mut bytes = [0u8; 32];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H256::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 32);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H256::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H256 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H256 as SszEncode>::fixed_size(), 32);
    }

    #[test]
    fn h264_roundtrip() {
        let mut bytes = [0u8; 33];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H264::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 33);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H264::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H264 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H264 as SszEncode>::fixed_size(), 33);
    }

    #[test]
    fn h512_roundtrip() {
        let mut bytes = [0u8; 64];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H512::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 64);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H512::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H512 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H512 as SszEncode>::fixed_size(), 64);
    }

    #[test]
    fn h520_roundtrip() {
        let mut bytes = [0u8; 65];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = i as u8;
        }
        let val = et::H520::from_slice(&bytes);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 65);
        assert_eq!(&encoded[..], &bytes[..]);
        let decoded = et::H520::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
        assert!(<et::H520 as SszEncode>::is_fixed_size());
        assert_eq!(<et::H520 as SszEncode>::fixed_size(), 65);
    }

    #[test]
    fn h256_wrong_length() {
        let err = et::H256::from_ssz_bytes(&[0u8; 31]).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidFixedLength {
                expected: 32,
                got: 31
            }
        );
    }

    // U-type tests
    #[test]
    fn u64_encode_decode() {
        let val = et::U64::from(256);
        let encoded = val.to_ssz();
        assert_eq!(encoded, vec![0, 1, 0, 0, 0, 0, 0, 0]);
        let decoded = et::U64::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
    }

    #[test]
    fn u128_roundtrip() {
        let val = et::U128::from(u64::MAX);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 16);
        let decoded = et::U128::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
    }

    #[test]
    fn u256_encode_one() {
        let val = et::U256::from(1);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 32);
        assert_eq!(encoded[0], 1);
        assert!(encoded[1..].iter().all(|&b| b == 0));
        let decoded = et::U256::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
    }

    #[test]
    fn u256_wrong_length() {
        let err = et::U256::from_ssz_bytes(&[0u8; 31]).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidFixedLength {
                expected: 32,
                got: 31
            }
        );
    }

    #[test]
    fn u512_roundtrip() {
        let val = et::U512::from(42);
        let encoded = val.to_ssz();
        assert_eq!(encoded.len(), 64);
        let decoded = et::U512::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
    }

    #[test]
    fn u256_max_value() {
        let val = et::U256::MAX;
        let encoded = val.to_ssz();
        assert!(encoded.iter().all(|&b| b == 0xff));
        let decoded = et::U256::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(val, decoded);
    }
}
