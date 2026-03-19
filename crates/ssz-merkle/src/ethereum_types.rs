//! HashTreeRoot implementations for `ethereum_types` types.

use ethereum_types as et;

use crate::{HashTreeRoot, Node};

// ── H-types: delegate to inner [u8; N] ──

impl HashTreeRoot for et::H32 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 4]>::is_basic_type()
    }
}

impl HashTreeRoot for et::H64 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 8]>::is_basic_type()
    }
}

impl HashTreeRoot for et::H128 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 16]>::is_basic_type()
    }
}

impl HashTreeRoot for et::H160 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 20]>::is_basic_type()
    }
}

impl HashTreeRoot for et::H256 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 32]>::is_basic_type()
    }
}

impl HashTreeRoot for et::H264 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 33]>::is_basic_type()
    }
}

impl HashTreeRoot for et::H512 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 64]>::is_basic_type()
    }
}

impl HashTreeRoot for et::H520 {
    fn hash_tree_root(&self) -> Node {
        self.as_fixed_bytes().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 65]>::is_basic_type()
    }
}

// ── U-types: serialize to LE bytes, then hash ──

impl HashTreeRoot for et::U64 {
    fn hash_tree_root(&self) -> Node {
        self.to_little_endian().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 8]>::is_basic_type()
    }
}

impl HashTreeRoot for et::U128 {
    fn hash_tree_root(&self) -> Node {
        self.to_little_endian().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 16]>::is_basic_type()
    }
}

impl HashTreeRoot for et::U256 {
    fn hash_tree_root(&self) -> Node {
        self.to_little_endian().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 32]>::is_basic_type()
    }
}

impl HashTreeRoot for et::U512 {
    fn hash_tree_root(&self) -> Node {
        self.to_little_endian().hash_tree_root()
    }
    fn is_basic_type() -> bool {
        <[u8; 64]>::is_basic_type()
    }
}

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
