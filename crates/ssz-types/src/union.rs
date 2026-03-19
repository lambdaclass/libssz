#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use libssz::DecodeError;

/// Newtype for the union selector byte (0..=127).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnionSelector(u8);

impl UnionSelector {
    /// The selector value for the `None` variant.
    pub const NONE: Self = Self(0);

    /// Create a new `UnionSelector`. Returns `Err` if `value > 127`.
    pub fn new(value: u8) -> Result<Self, DecodeError> {
        if value > 127 {
            return Err(DecodeError::InvalidUnionSelector(value));
        }
        Ok(Self(value))
    }

    /// Returns the raw selector value.
    pub fn value(&self) -> u8 {
        self.0
    }
}

/// Split encoded union bytes into the selector and the remaining data.
///
/// The first byte is the selector; the rest is the variant payload.
pub fn split_union_bytes(bytes: &[u8]) -> Result<(UnionSelector, &[u8]), DecodeError> {
    if bytes.is_empty() {
        return Err(DecodeError::EmptyInput);
    }
    let selector = UnionSelector::new(bytes[0])?;
    Ok((selector, &bytes[1..]))
}

/// Join a selector and variant data into encoded union bytes.
pub fn join_union_bytes(selector: UnionSelector, data: &[u8]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(1 + data.len());
    buf.push(selector.value());
    buf.extend_from_slice(data);
    buf
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn selector_valid_values() {
        assert_eq!(UnionSelector::new(0).unwrap().value(), 0);
        assert_eq!(UnionSelector::new(1).unwrap().value(), 1);
        assert_eq!(UnionSelector::new(127).unwrap().value(), 127);
    }

    #[test]
    fn selector_invalid_above_127() {
        let err = UnionSelector::new(128).unwrap_err();
        assert_eq!(err, DecodeError::InvalidUnionSelector(128));

        let err = UnionSelector::new(255).unwrap_err();
        assert_eq!(err, DecodeError::InvalidUnionSelector(255));
    }

    #[test]
    fn none_variant() {
        assert_eq!(UnionSelector::NONE.value(), 0);
    }

    #[test]
    fn split_union_bytes_basic() {
        let bytes = [3, 0xAA, 0xBB];
        let (sel, data) = split_union_bytes(&bytes).unwrap();
        assert_eq!(sel.value(), 3);
        assert_eq!(data, &[0xAA, 0xBB]);
    }

    #[test]
    fn split_union_bytes_none_variant() {
        let bytes = [0];
        let (sel, data) = split_union_bytes(&bytes).unwrap();
        assert_eq!(sel, UnionSelector::NONE);
        assert!(data.is_empty());
    }

    #[test]
    fn split_union_bytes_empty_input() {
        let err = split_union_bytes(&[]).unwrap_err();
        assert_eq!(err, DecodeError::EmptyInput);
    }

    #[test]
    fn split_union_bytes_invalid_selector() {
        let err = split_union_bytes(&[200, 0xAA]).unwrap_err();
        assert_eq!(err, DecodeError::InvalidUnionSelector(200));
    }

    #[test]
    fn join_union_bytes_basic() {
        let sel = UnionSelector::new(5).unwrap();
        let data = [0x01, 0x02, 0x03];
        let result = join_union_bytes(sel, &data);
        assert_eq!(result, vec![5, 0x01, 0x02, 0x03]);
    }

    #[test]
    fn join_union_bytes_none_empty_data() {
        let result = join_union_bytes(UnionSelector::NONE, &[]);
        assert_eq!(result, vec![0]);
    }

    #[test]
    fn roundtrip_split_join() {
        let sel = UnionSelector::new(42).unwrap();
        let data = [0xFF, 0x00, 0xAB];
        let encoded = join_union_bytes(sel, &data);
        let (decoded_sel, decoded_data) = split_union_bytes(&encoded).unwrap();
        assert_eq!(decoded_sel, sel);
        assert_eq!(decoded_data, &data);
    }
}
