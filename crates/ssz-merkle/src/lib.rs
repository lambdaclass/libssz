#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use ssz::SszEncode;

/// A 32-byte Merkle tree node.
pub type Node = [u8; 32];

include!(concat!(env!("OUT_DIR"), "/zero_hashes.rs"));

/// Hash two nodes together: SHA256(a || b).
#[inline]
pub fn hash_nodes(a: &Node, b: &Node) -> Node {
    let mut hasher = Sha256::new();
    hasher.update(a);
    hasher.update(b);
    let result = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&result);
    out
}

/// Pack serialized bytes into 32-byte chunks, zero-padding the last chunk if needed.
#[cfg(feature = "alloc")]
pub fn pack(values: &[u8]) -> Vec<Node> {
    if values.is_empty() {
        return Vec::new();
    }
    let num_chunks = values.len().div_ceil(32);
    let mut chunks = Vec::with_capacity(num_chunks);
    for i in 0..num_chunks {
        let start = i * 32;
        let end = core::cmp::min(start + 32, values.len());
        let mut chunk = [0u8; 32];
        chunk[..end - start].copy_from_slice(&values[start..end]);
        chunks.push(chunk);
    }
    chunks
}

/// Pack a bitfield into 32-byte chunks.
/// `bits` is the raw byte buffer, `num_bits` is the number of valid bits.
#[cfg(feature = "alloc")]
pub fn pack_bits(bits: &[u8], num_bits: usize) -> Vec<Node> {
    let num_bytes = num_bits.div_ceil(8);
    let effective = &bits[..core::cmp::min(num_bytes, bits.len())];
    pack(effective)
}

/// Compute the Merkle root of a list of chunks.
///
/// If `limit` is `Some(n)`, the tree is padded as if there were `n` leaf chunks
/// (using precomputed zero hashes). The padding is virtual — only the real chunks
/// are materialized, and the remaining subtree roots come from precomputed zero hashes.
#[cfg(feature = "alloc")]
pub fn merkleize(chunks: &[Node], limit: Option<usize>) -> Node {
    let count = match limit {
        Some(l) => {
            assert!(
                chunks.len() <= l,
                "chunk count {} exceeds limit {}",
                chunks.len(),
                l
            );
            l
        }
        None => chunks.len(),
    };

    if count == 0 {
        return ZERO_HASHES[0];
    }

    let leaf_count = count.next_power_of_two();
    let depth = if leaf_count == 1 {
        0
    } else {
        leaf_count.trailing_zeros() as usize
    };

    // Only allocate for real data, padded to the next power of two.
    // The rest of the tree is handled via precomputed zero hashes.
    let real_leaf_count = if chunks.is_empty() {
        1
    } else {
        chunks.len().next_power_of_two()
    };
    let real_depth = if real_leaf_count == 1 {
        0
    } else {
        real_leaf_count.trailing_zeros() as usize
    };

    // Build bottom layer from real chunks only
    let mut layer: Vec<Node> = Vec::with_capacity(real_leaf_count);
    layer.extend_from_slice(chunks);
    layer.resize(real_leaf_count, ZERO_HASHES[0]);

    // Hash layer by layer up to real_depth
    for zero_hash in ZERO_HASHES.iter().take(real_depth) {
        let mut next = Vec::with_capacity(layer.len() / 2);
        for pair in layer.chunks(2) {
            let left = &pair[0];
            let right = if pair.len() == 2 { &pair[1] } else { zero_hash };
            next.push(hash_nodes(left, right));
        }
        layer = next;
    }

    // Now layer[0] is the root of the real data subtree.
    // Merge with zero hashes for the remaining virtual depth levels.
    let mut root = layer[0];
    for zero_hash in ZERO_HASHES.iter().take(depth).skip(real_depth) {
        root = hash_nodes(&root, zero_hash);
    }

    root
}

/// Mix in a length value: hash_nodes(root, length_as_le_bytes_node).
#[inline]
pub fn mix_in_length(root: &Node, length: usize) -> Node {
    let mut length_node = [0u8; 32];
    length_node[..8].copy_from_slice(&(length as u64).to_le_bytes());
    hash_nodes(root, &length_node)
}

/// Mix in a selector value: hash_nodes(root, selector_as_le_bytes_node).
#[inline]
pub fn mix_in_selector(root: &Node, selector: u8) -> Node {
    let mut selector_node = [0u8; 32];
    selector_node[0] = selector;
    hash_nodes(root, &selector_node)
}

/// Trait for types that can compute their SSZ hash tree root.
pub trait HashTreeRoot {
    fn hash_tree_root(&self) -> Node;
}

// ── bool ──

impl HashTreeRoot for bool {
    #[inline(always)]
    fn hash_tree_root(&self) -> Node {
        let mut node = [0u8; 32];
        node[0] = if *self { 1 } else { 0 };
        node
    }
}

// ── Unsigned integers ──

macro_rules! impl_hash_tree_root_uint {
    ($ty:ty) => {
        impl HashTreeRoot for $ty {
            #[inline(always)]
            fn hash_tree_root(&self) -> Node {
                let mut node = [0u8; 32];
                let bytes = self.to_le_bytes();
                node[..bytes.len()].copy_from_slice(&bytes);
                node
            }
        }
    };
}

impl_hash_tree_root_uint!(u8);
impl_hash_tree_root_uint!(u16);
impl_hash_tree_root_uint!(u32);
impl_hash_tree_root_uint!(u64);
impl_hash_tree_root_uint!(u128);

// ── [u8; 32] ──

impl HashTreeRoot for [u8; 32] {
    #[inline(always)]
    fn hash_tree_root(&self) -> Node {
        *self
    }
}

// ── [u8; 4] ──

impl HashTreeRoot for [u8; 4] {
    #[inline(always)]
    fn hash_tree_root(&self) -> Node {
        let mut node = [0u8; 32];
        node[..4].copy_from_slice(self);
        node
    }
}

// ── [u8; 48] ──

#[cfg(feature = "alloc")]
impl HashTreeRoot for [u8; 48] {
    fn hash_tree_root(&self) -> Node {
        merkleize(&pack(self), None)
    }
}

// ── [u8; 96] ──

#[cfg(feature = "alloc")]
impl HashTreeRoot for [u8; 96] {
    fn hash_tree_root(&self) -> Node {
        merkleize(&pack(self), None)
    }
}

// ── Vec<T> for basic types ──

#[cfg(feature = "alloc")]
impl<T: HashTreeRoot + SszEncode> HashTreeRoot for Vec<T> {
    fn hash_tree_root(&self) -> Node {
        let length = self.len();
        if T::is_fixed_size() && T::fixed_size() <= 32 {
            // Basic type: pack serialized bytes
            let mut serialized = Vec::new();
            for item in self {
                item.ssz_append(&mut serialized);
            }
            let chunks = pack(&serialized);
            let root = if chunks.is_empty() {
                merkleize(&[ZERO_HASHES[0]], None)
            } else {
                merkleize(&chunks, None)
            };
            mix_in_length(&root, length)
        } else {
            // Composite type: collect roots
            let roots: Vec<Node> = self.iter().map(|item| item.hash_tree_root()).collect();
            let root = if roots.is_empty() {
                merkleize(&[ZERO_HASHES[0]], None)
            } else {
                merkleize(&roots, None)
            };
            mix_in_length(&root, length)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;
    use sha2::{Digest, Sha256};

    // ── hash_nodes tests ──

    #[test]
    fn hash_nodes_of_two_zero_nodes() {
        let zero = [0u8; 32];
        let result = hash_nodes(&zero, &zero);
        let mut hasher = Sha256::new();
        hasher.update([0u8; 64]);
        let expected: [u8; 32] = hasher.finalize().into();
        assert_eq!(result, expected);
    }

    #[test]
    fn hash_nodes_is_not_commutative() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        assert_ne!(hash_nodes(&a, &b), hash_nodes(&b, &a));
    }

    // ── Zero hashes tests ──

    #[test]
    fn zero_hash_level_0_is_all_zeros() {
        assert_eq!(ZERO_HASHES[0], [0u8; 32]);
    }

    #[test]
    fn zero_hash_level_1_is_hash_of_two_zeros() {
        let expected = hash_nodes(&[0u8; 32], &[0u8; 32]);
        assert_eq!(ZERO_HASHES[1], expected);
    }

    #[test]
    fn zero_hash_level_2_is_hash_of_two_level_1() {
        let expected = hash_nodes(&ZERO_HASHES[1], &ZERO_HASHES[1]);
        assert_eq!(ZERO_HASHES[2], expected);
    }

    // ── pack tests ──

    #[test]
    fn pack_empty_returns_empty() {
        let result = pack(&[]);
        assert!(result.is_empty());
    }

    #[test]
    fn pack_single_byte() {
        let result = pack(&[0x42]);
        assert_eq!(result.len(), 1);
        let mut expected = [0u8; 32];
        expected[0] = 0x42;
        assert_eq!(result[0], expected);
    }

    #[test]
    fn pack_exactly_32_bytes() {
        let input = [0xAB; 32];
        let result = pack(&input);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], input);
    }

    #[test]
    fn pack_33_bytes_produces_two_chunks() {
        let input = [0xFF; 33];
        let result = pack(&input);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0], [0xFF; 32]);
        let mut expected_second = [0u8; 32];
        expected_second[0] = 0xFF;
        assert_eq!(result[1], expected_second);
    }

    #[test]
    fn pack_two_u64_values() {
        let val1: u64 = 1;
        let val2: u64 = 2;
        let mut serialized = Vec::new();
        serialized.extend_from_slice(&val1.to_le_bytes());
        serialized.extend_from_slice(&val2.to_le_bytes());
        let result = pack(&serialized);
        assert_eq!(result.len(), 1); // 16 bytes fits in one 32-byte chunk
        let mut expected = [0u8; 32];
        expected[..8].copy_from_slice(&1u64.to_le_bytes());
        expected[8..16].copy_from_slice(&2u64.to_le_bytes());
        assert_eq!(result[0], expected);
    }

    // ── pack_bits tests ──

    #[test]
    fn pack_bits_7_bits() {
        let bits = [0b0111_1111u8]; // 7 bits set
        let result = pack_bits(&bits, 7);
        assert_eq!(result.len(), 1);
        let mut expected = [0u8; 32];
        expected[0] = 0b0111_1111;
        assert_eq!(result[0], expected);
    }

    #[test]
    fn pack_bits_8_bits() {
        let bits = [0xFF];
        let result = pack_bits(&bits, 8);
        assert_eq!(result.len(), 1);
        let mut expected = [0u8; 32];
        expected[0] = 0xFF;
        assert_eq!(result[0], expected);
    }

    #[test]
    fn pack_bits_9_bits() {
        let bits = [0xFF, 0x01]; // 9 bits
        let result = pack_bits(&bits, 9);
        assert_eq!(result.len(), 1);
        let mut expected = [0u8; 32];
        expected[0] = 0xFF;
        expected[1] = 0x01;
        assert_eq!(result[0], expected);
    }

    // ── merkleize tests ──

    #[test]
    fn merkleize_empty_returns_zero_hash() {
        let result = merkleize(&[], None);
        assert_eq!(result, ZERO_HASHES[0]);
    }

    #[test]
    fn merkleize_one_chunk_is_identity() {
        let chunk = [0x42u8; 32];
        let result = merkleize(&[chunk], None);
        assert_eq!(result, chunk);
    }

    #[test]
    fn merkleize_two_chunks() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        let result = merkleize(&[a, b], None);
        assert_eq!(result, hash_nodes(&a, &b));
    }

    #[test]
    fn merkleize_three_chunks_pads_to_four() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        let c = [3u8; 32];
        let result = merkleize(&[a, b, c], None);
        // Tree: hash(hash(a,b), hash(c, zero))
        let left = hash_nodes(&a, &b);
        let right = hash_nodes(&c, &ZERO_HASHES[0]);
        assert_eq!(result, hash_nodes(&left, &right));
    }

    #[test]
    fn merkleize_with_limit_pads_with_zero_hashes() {
        let a = [1u8; 32];
        // With limit=4, single chunk should be padded to 4 leaves
        let result = merkleize(&[a], Some(4));
        // Tree: hash(hash(a, zero), hash(zero, zero))
        let left = hash_nodes(&a, &ZERO_HASHES[0]);
        let right = ZERO_HASHES[1]; // hash(zero, zero)
        assert_eq!(result, hash_nodes(&left, &right));
    }

    #[test]
    fn merkleize_with_limit_equal_to_count() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        // limit=2 with 2 chunks should give same result as no limit
        assert_eq!(merkleize(&[a, b], Some(2)), merkleize(&[a, b], None));
    }

    #[test]
    #[should_panic(expected = "chunk count")]
    fn merkleize_panics_if_count_exceeds_limit() {
        let chunks = [[0u8; 32]; 3];
        merkleize(&chunks, Some(2));
    }

    // ── mix_in_length tests ──

    #[test]
    fn mix_in_length_known_value() {
        let root = [0u8; 32];
        let result = mix_in_length(&root, 5);
        let mut len_node = [0u8; 32];
        len_node[..8].copy_from_slice(&5u64.to_le_bytes());
        assert_eq!(result, hash_nodes(&root, &len_node));
    }

    #[test]
    fn mix_in_length_zero() {
        let root = [0xAB; 32];
        let result = mix_in_length(&root, 0);
        // length=0 means length_node is all zeros
        assert_eq!(result, hash_nodes(&root, &[0u8; 32]));
    }

    // ── mix_in_selector tests ──

    #[test]
    fn mix_in_selector_known_value() {
        let root = [0u8; 32];
        let result = mix_in_selector(&root, 3);
        let mut sel_node = [0u8; 32];
        sel_node[0] = 3;
        assert_eq!(result, hash_nodes(&root, &sel_node));
    }

    // ── HashTreeRoot tests ──

    #[test]
    fn hash_tree_root_bool_false() {
        let result = false.hash_tree_root();
        assert_eq!(result, [0u8; 32]);
    }

    #[test]
    fn hash_tree_root_bool_true() {
        let result = true.hash_tree_root();
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(result, expected);
    }

    #[test]
    fn hash_tree_root_u64() {
        let val: u64 = 0x0102030405060708;
        let result = val.hash_tree_root();
        let mut expected = [0u8; 32];
        expected[..8].copy_from_slice(&val.to_le_bytes());
        assert_eq!(result, expected);
    }

    #[test]
    fn hash_tree_root_u8() {
        let val: u8 = 42;
        let result = val.hash_tree_root();
        let mut expected = [0u8; 32];
        expected[0] = 42;
        assert_eq!(result, expected);
    }

    #[test]
    fn hash_tree_root_u128() {
        let val: u128 = 1;
        let result = val.hash_tree_root();
        let mut expected = [0u8; 32];
        expected[..16].copy_from_slice(&val.to_le_bytes());
        assert_eq!(result, expected);
    }

    #[test]
    fn hash_tree_root_bytes32() {
        let val = [0xAB; 32];
        let result = val.hash_tree_root();
        assert_eq!(result, val);
    }

    #[test]
    fn hash_tree_root_vec_u64_empty() {
        let val: Vec<u64> = vec![];
        let result = val.hash_tree_root();
        // Empty list: merkleize([zero]) then mix_in_length with 0
        let root = merkleize(&[ZERO_HASHES[0]], None);
        assert_eq!(result, mix_in_length(&root, 0));
    }

    #[test]
    fn hash_tree_root_vec_u64() {
        let val: Vec<u64> = vec![1, 2, 3, 4];
        let result = val.hash_tree_root();

        // 4 u64s = 32 bytes = 1 chunk
        let mut serialized = Vec::new();
        for v in &val {
            serialized.extend_from_slice(&v.to_le_bytes());
        }
        let chunks = pack(&serialized);
        let root = merkleize(&chunks, None);
        assert_eq!(result, mix_in_length(&root, 4));
    }

    #[test]
    fn hash_tree_root_vec_u64_five_elements() {
        let val: Vec<u64> = vec![1, 2, 3, 4, 5];
        let result = val.hash_tree_root();

        // 5 u64s = 40 bytes = 2 chunks
        let mut serialized = Vec::new();
        for v in &val {
            serialized.extend_from_slice(&v.to_le_bytes());
        }
        let chunks = pack(&serialized);
        assert_eq!(chunks.len(), 2);
        let root = merkleize(&chunks, None);
        assert_eq!(result, mix_in_length(&root, 5));
    }
}
