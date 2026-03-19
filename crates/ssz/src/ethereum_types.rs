//! SszEncode and SszDecode implementations for `ethereum_types` types.

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use ethereum_types as et;

use crate::error::DecodeError;
use crate::{SszDecode, SszEncode};

// ── H-types (fixed-size byte arrays) ──

macro_rules! impl_ssz_for_hash {
    ($type:ty, $size:expr) => {
        impl SszEncode for $type {
            #[inline(always)]
            fn is_fixed_size() -> bool {
                true
            }
            #[inline(always)]
            fn fixed_size() -> usize {
                $size
            }
            #[inline(always)]
            fn encoded_len(&self) -> usize {
                $size
            }
            #[inline(always)]
            fn ssz_append(&self, buf: &mut Vec<u8>) {
                buf.extend_from_slice(self.as_bytes());
            }
        }

        impl SszDecode for $type {
            #[inline(always)]
            fn is_fixed_size() -> bool {
                true
            }
            #[inline(always)]
            fn fixed_size() -> usize {
                $size
            }
            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
                if bytes.len() != $size {
                    return Err(DecodeError::InvalidFixedLength {
                        expected: $size,
                        got: bytes.len(),
                    });
                }
                Ok(<$type>::from_slice(bytes))
            }
        }
    };
}

impl_ssz_for_hash!(et::H32, 4);
impl_ssz_for_hash!(et::H64, 8);
impl_ssz_for_hash!(et::H128, 16);
impl_ssz_for_hash!(et::H160, 20);
impl_ssz_for_hash!(et::H256, 32);
impl_ssz_for_hash!(et::H264, 33);
impl_ssz_for_hash!(et::H512, 64);
impl_ssz_for_hash!(et::H520, 65);

// ── U-types (little-endian unsigned integers) ──

macro_rules! impl_ssz_for_uint {
    ($type:ty, $size:expr) => {
        impl SszEncode for $type {
            #[inline(always)]
            fn is_fixed_size() -> bool {
                true
            }
            #[inline(always)]
            fn fixed_size() -> usize {
                $size
            }
            #[inline(always)]
            fn encoded_len(&self) -> usize {
                $size
            }
            fn ssz_append(&self, buf: &mut Vec<u8>) {
                buf.extend_from_slice(&self.to_little_endian());
            }
        }

        impl SszDecode for $type {
            #[inline(always)]
            fn is_fixed_size() -> bool {
                true
            }
            #[inline(always)]
            fn fixed_size() -> usize {
                $size
            }
            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
                if bytes.len() != $size {
                    return Err(DecodeError::InvalidFixedLength {
                        expected: $size,
                        got: bytes.len(),
                    });
                }
                Ok(<$type>::from_little_endian(bytes))
            }
        }
    };
}

impl_ssz_for_uint!(et::U64, 8);
impl_ssz_for_uint!(et::U128, 16);
impl_ssz_for_uint!(et::U256, 32);
impl_ssz_for_uint!(et::U512, 64);

#[cfg(test)]
mod tests {
    use super::*;

    // H-type tests
    macro_rules! test_hash_roundtrip {
        ($name:ident, $type:ty, $size:expr) => {
            #[test]
            fn $name() {
                let mut bytes = [0u8; $size];
                for (i, b) in bytes.iter_mut().enumerate() {
                    *b = i as u8;
                }
                let val = <$type>::from_slice(&bytes);
                let encoded = val.to_ssz();
                assert_eq!(encoded.len(), $size);
                assert_eq!(&encoded[..], &bytes[..]);
                let decoded = <$type>::from_ssz_bytes(&encoded).unwrap();
                assert_eq!(val, decoded);

                assert!(<$type as SszEncode>::is_fixed_size());
                assert_eq!(<$type as SszEncode>::fixed_size(), $size);
            }
        };
    }

    test_hash_roundtrip!(h32_roundtrip, et::H32, 4);
    test_hash_roundtrip!(h64_roundtrip, et::H64, 8);
    test_hash_roundtrip!(h128_roundtrip, et::H128, 16);
    test_hash_roundtrip!(h160_roundtrip, et::H160, 20);
    test_hash_roundtrip!(h256_roundtrip, et::H256, 32);
    test_hash_roundtrip!(h264_roundtrip, et::H264, 33);
    test_hash_roundtrip!(h512_roundtrip, et::H512, 64);
    test_hash_roundtrip!(h520_roundtrip, et::H520, 65);

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
