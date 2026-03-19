//! HashTreeRoot implementations for `ethereum_types` types.

use ethereum_types as et;

use crate::{HashTreeRoot, Node};

// ── H-types: delegate to inner [u8; N] ──

macro_rules! impl_htr_for_hash {
    ($type:ty, $size:expr) => {
        impl HashTreeRoot for $type {
            fn hash_tree_root(&self) -> Node {
                self.as_fixed_bytes().hash_tree_root()
            }

            fn is_basic_type() -> bool {
                <[u8; $size]>::is_basic_type()
            }
        }
    };
}

impl_htr_for_hash!(et::H32, 4);
impl_htr_for_hash!(et::H64, 8);
impl_htr_for_hash!(et::H128, 16);
impl_htr_for_hash!(et::H160, 20);
impl_htr_for_hash!(et::H256, 32);
impl_htr_for_hash!(et::H264, 33);
impl_htr_for_hash!(et::H512, 64);
impl_htr_for_hash!(et::H520, 65);

// ── U-types: serialize to LE bytes, then hash ──

macro_rules! impl_htr_for_uint {
    ($type:ty, $size:expr) => {
        impl HashTreeRoot for $type {
            fn hash_tree_root(&self) -> Node {
                self.to_little_endian().hash_tree_root()
            }

            fn is_basic_type() -> bool {
                <[u8; $size]>::is_basic_type()
            }
        }
    };
}

impl_htr_for_uint!(et::U64, 8);
impl_htr_for_uint!(et::U128, 16);
impl_htr_for_uint!(et::U256, 32);
impl_htr_for_uint!(et::U512, 64);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{merkleize, pack};

    // H-type basic type checks
    #[test]
    fn h32_is_basic() {
        assert!(et::H32::is_basic_type());
    }

    #[test]
    fn h160_is_basic() {
        assert!(et::H160::is_basic_type());
    }

    #[test]
    fn h256_is_basic() {
        assert!(et::H256::is_basic_type());
    }

    #[test]
    fn h264_is_not_basic() {
        assert!(!et::H264::is_basic_type());
    }

    #[test]
    fn h512_is_not_basic() {
        assert!(!et::H512::is_basic_type());
    }

    #[test]
    fn h520_is_not_basic() {
        assert!(!et::H520::is_basic_type());
    }

    // H-type HTR delegates to inner array
    #[test]
    fn h256_htr_equals_array_htr() {
        let bytes = [0xab_u8; 32];
        let h = et::H256::from_slice(&bytes);
        assert_eq!(h.hash_tree_root(), bytes.hash_tree_root());
    }

    #[test]
    fn h160_htr_equals_array_htr() {
        let bytes = [0xcd_u8; 20];
        let h = et::H160::from_slice(&bytes);
        assert_eq!(h.hash_tree_root(), bytes.hash_tree_root());
    }

    #[test]
    fn h512_htr_equals_array_htr() {
        let bytes = [0xef_u8; 64];
        let h = et::H512::from_slice(&bytes);
        assert_eq!(h.hash_tree_root(), bytes.hash_tree_root());
    }

    // U-type basic type checks
    #[test]
    fn u64_is_basic() {
        assert!(et::U64::is_basic_type());
    }

    #[test]
    fn u256_is_basic() {
        assert!(et::U256::is_basic_type());
    }

    #[test]
    fn u512_is_not_basic() {
        assert!(!et::U512::is_basic_type());
    }

    // U-type HTR values
    #[test]
    fn u256_htr_is_le_bytes() {
        let val = et::U256::from(42);
        let root = val.hash_tree_root();
        let expected = val.to_little_endian();
        assert_eq!(root, expected);
    }

    #[test]
    fn u64_htr_is_padded_le() {
        let val = et::U64::from(1);
        let root = val.hash_tree_root();
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(root, expected);
    }

    #[test]
    fn u512_htr_is_merkleized() {
        let val = et::U512::from(42);
        let bytes = val.to_little_endian();
        let expected = merkleize(&pack(&bytes), None);
        assert_eq!(val.hash_tree_root(), expected);
    }
}
