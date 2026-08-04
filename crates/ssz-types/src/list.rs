#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use core::ops::{Deref, Index};

use libssz::{decode_list_with_max, DecodeError, SszDecode, SszEncode};

use crate::error::TypeError;

/// A variable-length SSZ list with at most `N` elements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SszList<T, const N: usize>(Vec<T>);

impl<T, const N: usize> SszList<T, N> {
    /// Create an empty list.
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Returns the maximum capacity `N`.
    pub fn max_capacity(&self) -> usize {
        N
    }

    /// Returns the current number of elements.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the list is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Push an element. Returns `Err` if the list is at capacity.
    pub fn push(&mut self, value: T) -> Result<(), TypeError> {
        if self.0.len() >= N {
            return Err(TypeError::OverCapacity {
                max: N,
                got: self.0.len() + 1,
            });
        }
        self.0.push(value);
        Ok(())
    }

    /// Consume and return the inner `Vec<T>`.
    pub fn into_inner(self) -> Vec<T> {
        self.0
    }
}

impl<T, const N: usize> Default for SszList<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> TryFrom<Vec<T>> for SszList<T, N> {
    type Error = TypeError;

    fn try_from(vec: Vec<T>) -> Result<Self, Self::Error> {
        if vec.len() > N {
            return Err(TypeError::OverCapacity {
                max: N,
                got: vec.len(),
            });
        }
        Ok(Self(vec))
    }
}

impl<T, const N: usize> Deref for SszList<T, N> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T, const N: usize, I: core::slice::SliceIndex<[T]>> Index<I> for SszList<T, N> {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.0[index]
    }
}

impl<T, const N: usize> IntoIterator for SszList<T, N> {
    type Item = T;
    type IntoIter = alloc::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a SszList<T, N> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

// ── SSZ Encoding ──

impl<T: SszEncode, const N: usize> SszEncode for SszList<T, N> {
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

// ── SSZ Decoding ──

impl<T: SszDecode, const N: usize> SszDecode for SszList<T, N> {
    fn is_fixed_size() -> bool {
        false
    }

    fn fixed_size() -> usize {
        0
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        decode_list_with_max(bytes, N).map(Self)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[derive(Debug)]
    struct FixedTenBytes;

    impl SszDecode for FixedTenBytes {
        fn is_fixed_size() -> bool {
            true
        }

        fn fixed_size() -> usize {
            10
        }

        fn from_ssz_bytes(_bytes: &[u8]) -> Result<Self, DecodeError> {
            panic!("fixed item decoder should not run for an over-capacity list")
        }
    }

    #[derive(Debug)]
    struct VariableItem;

    impl SszDecode for VariableItem {
        fn is_fixed_size() -> bool {
            false
        }

        fn fixed_size() -> usize {
            0
        }

        fn from_ssz_bytes(_bytes: &[u8]) -> Result<Self, DecodeError> {
            panic!("variable item decoder should not run for an over-capacity list")
        }
    }

    #[test]
    fn empty_list() {
        let list: SszList<u8, 10> = SszList::new();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn push_within_capacity() {
        let mut list: SszList<u16, 3> = SszList::new();
        list.push(1).unwrap();
        list.push(2).unwrap();
        list.push(3).unwrap();
        assert_eq!(list.len(), 3);
        assert_eq!(&*list, &[1, 2, 3]);
    }

    #[test]
    fn push_over_capacity() {
        let mut list: SszList<u8, 2> = SszList::new();
        list.push(1).unwrap();
        list.push(2).unwrap();
        let err = list.push(3).unwrap_err();
        assert_eq!(err, TypeError::OverCapacity { max: 2, got: 3 });
    }

    #[test]
    fn try_from_within_capacity() {
        let list: SszList<u32, 5> = SszList::try_from(vec![10, 20, 30]).unwrap();
        assert_eq!(list.len(), 3);
    }

    #[test]
    fn try_from_at_capacity() {
        let list: SszList<u32, 3> = SszList::try_from(vec![10, 20, 30]).unwrap();
        assert_eq!(list.len(), 3);
    }

    #[test]
    fn try_from_over_capacity() {
        let err = SszList::<u32, 2>::try_from(vec![10, 20, 30]).unwrap_err();
        assert_eq!(err, TypeError::OverCapacity { max: 2, got: 3 });
    }

    #[test]
    fn try_from_empty() {
        let list: SszList<u64, 100> = SszList::try_from(vec![]).unwrap();
        assert!(list.is_empty());
    }

    #[test]
    fn encode_decode_roundtrip_fixed_elements() {
        let list: SszList<u16, 10> = SszList::try_from(vec![100, 200, 300]).unwrap();
        let encoded = list.to_ssz();
        assert_eq!(encoded.len(), 6); // 3 * 2 bytes
        let decoded = SszList::<u16, 10>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(list, decoded);
    }

    #[test]
    fn encode_decode_empty_list() {
        let list: SszList<u32, 5> = SszList::new();
        let encoded = list.to_ssz();
        assert!(encoded.is_empty());
        let decoded = SszList::<u32, 5>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(list, decoded);
    }

    #[test]
    fn encode_decode_variable_elements() {
        let inner = vec![vec![1u8, 2], vec![3], vec![4, 5, 6]];
        let list: SszList<Vec<u8>, 10> = SszList::try_from(inner).unwrap();
        let encoded = list.to_ssz();
        let decoded = SszList::<Vec<u8>, 10>::from_ssz_bytes(&encoded).unwrap();
        assert_eq!(list, decoded);
    }

    #[test]
    fn decode_over_capacity() {
        // Encode 4 items, try to decode with max 3
        let list: SszList<u16, 10> = SszList::try_from(vec![1u16, 2, 3, 4]).unwrap();
        let encoded = list.to_ssz();
        let err = SszList::<u16, 3>::from_ssz_bytes(&encoded).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidByteLength {
                expected: 3,
                got: 4
            }
        );
    }

    #[test]
    fn decode_over_capacity_fixed_elements_rejects_before_item_decode() {
        let bytes = vec![0; 40];
        let err = SszList::<FixedTenBytes, 3>::from_ssz_bytes(&bytes).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidByteLength {
                expected: 3,
                got: 4
            }
        );
    }

    #[test]
    fn decode_over_capacity_variable_elements_rejects_before_item_decode() {
        let encoded = vec![
            16, 0, 0, 0, // item 0 offset
            16, 0, 0, 0, // item 1 offset
            16, 0, 0, 0, // item 2 offset
            16, 0, 0, 0, // item 3 offset
        ];
        let err = SszList::<VariableItem, 3>::from_ssz_bytes(&encoded).unwrap_err();
        assert_eq!(
            err,
            DecodeError::InvalidByteLength {
                expected: 3,
                got: 4
            }
        );
    }

    #[test]
    fn list_is_always_variable_size() {
        assert!(!<SszList<u64, 10> as SszEncode>::is_fixed_size());
        assert!(!<SszList<Vec<u8>, 5> as SszEncode>::is_fixed_size());
    }

    #[test]
    fn max_capacity() {
        let list: SszList<u8, 42> = SszList::new();
        assert_eq!(list.max_capacity(), 42);
    }

    #[test]
    fn into_inner_returns_underlying_vec() {
        let list: SszList<u16, 10> = SszList::try_from(vec![10, 20, 30]).unwrap();
        let inner: Vec<u16> = list.into_inner();
        assert_eq!(inner, vec![10, 20, 30]);
    }

    #[test]
    fn default_creates_empty_list() {
        let list: SszList<u32, 5> = SszList::default();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn deref_allows_slice_methods() {
        let list: SszList<u32, 10> = SszList::try_from(vec![3, 1, 4, 1, 5]).unwrap();
        // Deref to &[T] lets us use slice methods
        assert!(list.contains(&4));
        assert_eq!(list.first(), Some(&3));
        assert_eq!(list.last(), Some(&5));
    }

    #[test]
    fn index_with_range() {
        let list: SszList<u16, 10> = SszList::try_from(vec![10, 20, 30, 40]).unwrap();
        assert_eq!(list[0], 10);
        assert_eq!(list[3], 40);
        assert_eq!(&list[1..3], &[20, 30]);
    }

    #[test]
    fn into_iter_owned() {
        let list: SszList<u32, 5> = SszList::try_from(vec![1, 2, 3]).unwrap();
        let collected: Vec<u32> = list.into_iter().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn into_iter_ref() {
        let list: SszList<u32, 5> = SszList::try_from(vec![1, 2, 3]).unwrap();
        let sum: u32 = (&list).into_iter().sum();
        assert_eq!(sum, 6);
    }

    #[test]
    fn encoded_len_variable_elements() {
        // List of variable-length items: offsets + data
        let inner = vec![vec![1u8, 2], vec![3]];
        let list: SszList<Vec<u8>, 10> = SszList::try_from(inner).unwrap();
        let encoded = list.to_ssz();
        assert_eq!(list.encoded_len(), encoded.len());
    }

    #[test]
    fn decode_is_always_variable_size() {
        assert!(!<SszList<u32, 10> as SszDecode>::is_fixed_size());
        assert_eq!(<SszList<u32, 10> as SszDecode>::fixed_size(), 0);
    }
}
