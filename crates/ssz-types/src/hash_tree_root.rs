#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use ssz::SszEncode;
use ssz_merkle::{merkleize, mix_in_length, pack, pack_bits, HashTreeRoot, Node};

use crate::bitvector::SszBitvector;
use crate::bitlist::SszBitlist;
use crate::list::SszList;
use crate::vector::SszVector;

// ── SszVector<T, N> ──
// Vector is a fixed-length composite. HTR = merkleize(field_roots) with no mix_in_length.

impl<T: HashTreeRoot + SszEncode, const N: usize> HashTreeRoot for SszVector<T, N> {
    fn hash_tree_root(&self) -> Node {
        if T::is_fixed_size() && T::fixed_size() <= 32 {
            // Basic type vector: pack serialized bytes, merkleize with limit = ceil(N * size / 32)
            let mut serialized = Vec::new();
            for item in self.iter() {
                item.ssz_append(&mut serialized);
            }
            let chunks = pack(&serialized);
            let max_chunks = (N * T::fixed_size()).div_ceil(32);
            merkleize(&chunks, Some(max_chunks))
        } else {
            // Composite type vector: collect roots, merkleize with limit = N
            let roots: Vec<Node> = self.iter().map(|item| item.hash_tree_root()).collect();
            merkleize(&roots, Some(N))
        }
    }
}

// ── SszList<T, N> ──
// List is variable-length. HTR = mix_in_length(merkleize(field_roots, limit=N), len).

impl<T: HashTreeRoot + SszEncode, const N: usize> HashTreeRoot for SszList<T, N> {
    fn hash_tree_root(&self) -> Node {
        let length = self.len();
        if T::is_fixed_size() && T::fixed_size() <= 32 {
            // Basic type list: pack serialized bytes
            let mut serialized = Vec::new();
            for item in self.iter() {
                item.ssz_append(&mut serialized);
            }
            let chunks = pack(&serialized);
            let max_chunks = (N * T::fixed_size()).div_ceil(32);
            let root = merkleize(&chunks, Some(max_chunks));
            mix_in_length(&root, length)
        } else {
            // Composite type list: collect roots
            let roots: Vec<Node> = self.iter().map(|item| item.hash_tree_root()).collect();
            let root = merkleize(&roots, Some(N));
            mix_in_length(&root, length)
        }
    }
}

// ── SszBitvector<N> ──
// Bitvector is fixed-length. HTR = merkleize(pack_bits(bytes, N)).

impl<const N: usize> HashTreeRoot for SszBitvector<N> {
    fn hash_tree_root(&self) -> Node {
        let chunks = pack_bits(self.as_bytes(), N);
        let max_chunks = N.div_ceil(256); // 256 bits per chunk
        merkleize(&chunks, Some(max_chunks))
    }
}

// ── SszBitlist<N> ──
// Bitlist is variable-length. HTR = mix_in_length(merkleize(pack_bits(bytes, len), limit), len).

impl<const N: usize> HashTreeRoot for SszBitlist<N> {
    fn hash_tree_root(&self) -> Node {
        let length = self.len();
        let chunks = pack_bits(self.as_bytes(), length);
        let max_chunks = N.div_ceil(256);
        let root = merkleize(&chunks, Some(max_chunks));
        mix_in_length(&root, length)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── SszVector ──

    #[test]
    fn vector_u64_hash_tree_root() {
        let v: SszVector<u64, 4> = vec![1u64, 2, 3, 4].try_into().unwrap();
        let root = v.hash_tree_root();

        // Manual: 4 u64s = 32 bytes = 1 chunk, max_chunks = ceil(4*8/32) = 1
        let mut serialized = Vec::new();
        for val in v.iter() {
            val.ssz_append(&mut serialized);
        }
        let chunks = pack(&serialized);
        let expected = merkleize(&chunks, Some(1));
        assert_eq!(root, expected);
    }

    #[test]
    fn vector_u64_five_elements() {
        let v: SszVector<u64, 5> = vec![1u64, 2, 3, 4, 5].try_into().unwrap();
        let root = v.hash_tree_root();

        // 5 u64s = 40 bytes = 2 chunks, max_chunks = ceil(5*8/32) = 2
        let mut serialized = Vec::new();
        for val in v.iter() {
            val.ssz_append(&mut serialized);
        }
        let chunks = pack(&serialized);
        let expected = merkleize(&chunks, Some(2));
        assert_eq!(root, expected);
    }

    // ── SszList ──

    #[test]
    fn list_u64_hash_tree_root() {
        let mut list: SszList<u64, 8> = SszList::new();
        list.push(1).unwrap();
        list.push(2).unwrap();
        list.push(3).unwrap();
        let root = list.hash_tree_root();

        // 3 u64s = 24 bytes = 1 chunk, max_chunks = ceil(8*8/32) = 2
        let mut serialized = Vec::new();
        for val in list.iter() {
            val.ssz_append(&mut serialized);
        }
        let chunks = pack(&serialized);
        let inner_root = merkleize(&chunks, Some(2));
        let expected = mix_in_length(&inner_root, 3);
        assert_eq!(root, expected);
    }

    #[test]
    fn list_empty_hash_tree_root() {
        let list: SszList<u64, 8> = SszList::new();
        let root = list.hash_tree_root();

        // Empty: merkleize([], limit=2) then mix_in_length with 0
        let inner_root = merkleize(&[], Some(2));
        let expected = mix_in_length(&inner_root, 0);
        assert_eq!(root, expected);
    }

    // ── SszBitvector ──

    #[test]
    fn bitvector_hash_tree_root() {
        let mut bv = SszBitvector::<8>::new();
        bv.set(0, true);
        bv.set(7, true);
        let root = bv.hash_tree_root();

        // 8 bits = 1 byte, pack_bits produces 1 chunk
        let chunks = pack_bits(bv.as_bytes(), 8);
        let expected = merkleize(&chunks, Some(1));
        assert_eq!(root, expected);
    }

    #[test]
    fn bitvector_256_bits() {
        let bv = SszBitvector::<256>::new();
        let root = bv.hash_tree_root();

        // 256 bits = 32 bytes = 1 chunk, max_chunks = 1
        let chunks = pack_bits(bv.as_bytes(), 256);
        let expected = merkleize(&chunks, Some(1));
        assert_eq!(root, expected);
    }

    // ── SszBitlist ──

    #[test]
    fn bitlist_hash_tree_root() {
        let mut bl = SszBitlist::<64>::new();
        bl.push(true).unwrap();
        bl.push(false).unwrap();
        bl.push(true).unwrap();
        let root = bl.hash_tree_root();

        // 3 bits, pack_bits produces 1 chunk, max_chunks = ceil(64/256) = 1
        let chunks = pack_bits(bl.as_bytes(), 3);
        let inner_root = merkleize(&chunks, Some(1));
        let expected = mix_in_length(&inner_root, 3);
        assert_eq!(root, expected);
    }

    #[test]
    fn bitlist_empty_hash_tree_root() {
        let bl = SszBitlist::<64>::new();
        let root = bl.hash_tree_root();

        let chunks = pack_bits(bl.as_bytes(), 0);
        let inner_root = merkleize(&chunks, Some(1));
        let expected = mix_in_length(&inner_root, 0);
        assert_eq!(root, expected);
    }
}
