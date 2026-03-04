#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use core::ops::{Deref, Index};

use ssz::{DecodeError, SszDecode, SszEncode};

use crate::error::TypeError;

/// A fixed-length SSZ vector with exactly `N` elements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SszVector<T, const N: usize>(Vec<T>);

impl<T, const N: usize> SszVector<T, N> {
    /// Returns the fixed length `N`.
    pub fn len(&self) -> usize {
        N
    }

    /// Always returns `false` — a Vector always has `N` elements.
    pub fn is_empty(&self) -> bool {
        N == 0
    }

    /// Consume and return the inner `Vec<T>`.
    pub fn into_inner(self) -> Vec<T> {
        self.0
    }
}

impl<T, const N: usize> TryFrom<Vec<T>> for SszVector<T, N> {
    type Error = TypeError;

    fn try_from(vec: Vec<T>) -> Result<Self, Self::Error> {
        if vec.len() != N {
            return Err(TypeError::InvalidLength {
                expected: N,
                got: vec.len(),
            });
        }
        Ok(Self(vec))
    }
}

impl<T, const N: usize> Deref for SszVector<T, N> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T, const N: usize, I: core::slice::SliceIndex<[T]>> Index<I> for SszVector<T, N> {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.0[index]
    }
}

impl<T, const N: usize> IntoIterator for SszVector<T, N> {
    type Item = T;
    type IntoIter = alloc::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a SszVector<T, N> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

// ── SSZ Encoding ──

impl<T: SszEncode, const N: usize> SszEncode for SszVector<T, N> {
    fn is_fixed_size() -> bool {
        T::is_fixed_size()
    }

    fn fixed_size() -> usize {
        if T::is_fixed_size() {
            T::fixed_size() * N
        } else {
            0
        }
    }

    fn encoded_len(&self) -> usize {
        self.0.encoded_len()
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        self.0.ssz_append(buf);
    }
}

// ── SSZ Decoding ──

impl<T: SszDecode, const N: usize> SszDecode for SszVector<T, N> {
    fn is_fixed_size() -> bool {
        T::is_fixed_size()
    }

    fn fixed_size() -> usize {
        if T::is_fixed_size() {
            T::fixed_size() * N
        } else {
            0
        }
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let vec = Vec::<T>::from_ssz_bytes(bytes)?;
        if vec.len() != N {
            return Err(DecodeError::InvalidFixedLength {
                expected: N,
                got: vec.len(),
            });
        }
        Ok(Self(vec))
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn try_from_correct_length() {
        let v: SszVector<u16, 3> = SszVector::try_from(vec![1u16, 2, 3]).unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(&*v, &[1, 2, 3]);
    }

    #[test]
    fn try_from_wrong_length_too_short() {
        let err = SszVector::<u16, 3>::try_from(vec![1u16, 2]).unwrap_err();
        assert_eq!(
            err,
            TypeError::InvalidLength {
                expected: 3,
                got: 2
            }
        );
    }

    #[test]
    fn try_from_wrong_length_too_long() {
        let err = SszVector::<u16, 3>::try_from(vec![1u16, 2, 3, 4]).unwrap_err();
        assert_eq!(
            err,
            TypeError::InvalidLength {
                expected: 3,
                got: 4
            }
        );
    }

    #[test]
    fn try_from_empty_vector_n0() {
        let v: SszVector<u8, 0> = SszVector::try_from(vec![]).unwrap();
        assert!(v.is_empty());
    }

    #[test]
    fn deref_and_index() {
        let v: SszVector<u32, 4> = SszVector::try_from(vec![10, 20, 30, 40]).unwrap();
        assert_eq!(v[0], 10);
        assert_eq!(v[3], 40);
        assert_eq!(&v[1..3], &[20, 30]);
    }

    #[test]
    fn into_iterator() {
        let v: SszVector<u8, 3> = SszVector::try_from(vec![1, 2, 3]).unwrap();
        let collected: Vec<u8> = v.into_iter().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn encode_decode_roundtrip_fixed() {
        let v: SszVector<u16, 4> = SszVector::try_from(vec![100, 200, 300, 400]).unwrap();
        let encoded = v.to_ssz();
        assert_eq!(encoded.len(), 8); // 4 * 2 bytes
        let decoded = SszVector::<u16, 4>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(v, decoded);
    }

    #[test]
    fn encode_decode_roundtrip_variable() {
        // Vec<Vec<u8>> is variable-length
        let inner: Vec<Vec<u8>> = vec![vec![1, 2], vec![3], vec![4, 5, 6]];
        let v: SszVector<Vec<u8>, 3> = SszVector::try_from(inner).unwrap();
        let encoded = v.to_ssz();
        let decoded = SszVector::<Vec<u8>, 3>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(v, decoded);
    }

    #[test]
    fn decode_wrong_element_count() {
        // Encode a 3-element vector, try to decode as 4-element
        let v: SszVector<u16, 3> = SszVector::try_from(vec![1u16, 2, 3]).unwrap();
        let encoded = v.to_ssz();
        let err = SszVector::<u16, 4>::from_ssz_bytes(&encoded).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidFixedLength {
                expected: 4,
                got: 3
            }
        );
    }

    #[test]
    fn vector_is_fixed_size_when_element_is_fixed() {
        assert!(<SszVector<u64, 10> as SszEncode>::is_fixed_size());
        assert_eq!(<SszVector<u64, 10> as SszEncode>::fixed_size(), 80);
    }

    #[test]
    fn vector_is_variable_size_when_element_is_variable() {
        assert!(!<SszVector<Vec<u8>, 3> as SszEncode>::is_fixed_size());
    }
}
