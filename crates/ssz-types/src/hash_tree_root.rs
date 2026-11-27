#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use libssz::SszEncode;
use libssz_merkle::{merkleize, mix_in_length, pack, pack_bits, HashTreeRoot, Node, Sha256Hasher};

use crate::bitlist::SszBitlist;
use crate::bitvector::SszBitvector;
use crate::list::SszList;
use crate::vector::SszVector;

// ── SszVector<T, N> ──
// Vector is a fixed-length composite. HTR = merkleize(field_roots) with no mix_in_length.

impl<T: HashTreeRoot + SszEncode, const N: usize> HashTreeRoot for SszVector<T, N> {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        if T::is_basic_type() {
            // Basic type vector: pack serialized bytes, merkleize with limit = ceil(N * size / 32)
            let mut serialized = Vec::new();
            for item in self.iter() {
                item.ssz_append(&mut serialized);
            }
            let chunks = pack(&serialized);
            let max_chunks = (N * T::fixed_size()).div_ceil(32);
            merkleize(hasher, &chunks, Some(max_chunks))
        } else {
            // Composite type vector: collect roots, merkleize with limit = N
            let roots: Vec<Node> = self
                .iter()
                .map(|item| item.hash_tree_root(hasher))
                .collect();
            merkleize(hasher, &roots, Some(N))
        }
    }
}

// ── SszList<T, N> ──
// List is variable-length. HTR = mix_in_length(merkleize(field_roots, limit=N), len).

impl<T: HashTreeRoot + SszEncode, const N: usize> HashTreeRoot for SszList<T, N> {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let length = self.len();
        if T::is_basic_type() {
            // Basic type list: pack serialized bytes
            let mut serialized = Vec::new();
            for item in self.iter() {
                item.ssz_append(&mut serialized);
            }
            let chunks = pack(&serialized);
            let max_chunks = (N * T::fixed_size()).div_ceil(32);
            let root = merkleize(hasher, &chunks, Some(max_chunks));
            mix_in_length(hasher, &root, length)
        } else {
            // Composite type list: collect roots
            let roots: Vec<Node> = self
                .iter()
                .map(|item| item.hash_tree_root(hasher))
                .collect();
            let root = merkleize(hasher, &roots, Some(N));
            mix_in_length(hasher, &root, length)
        }
    }
}

// ── SszBitvector<N> ──
// Bitvector is fixed-length. HTR = merkleize(pack_bits(bytes, N)).

impl<const N: usize> HashTreeRoot for SszBitvector<N> {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let chunks = pack_bits(self.as_bytes(), N);
        let max_chunks = N.div_ceil(256); // 256 bits per chunk
        merkleize(hasher, &chunks, Some(max_chunks))
    }
}

// ── SszBitlist<N> ──
// Bitlist is variable-length. HTR = mix_in_length(merkleize(pack_bits(bytes, len), limit), len).

impl<const N: usize> HashTreeRoot for SszBitlist<N> {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let length = self.len();
        let chunks = pack_bits(self.as_bytes(), length);
        let max_chunks = N.div_ceil(256);
        let root = merkleize(hasher, &chunks, Some(max_chunks));
        mix_in_length(hasher, &root, length)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libssz_merkle::Sha2Hasher;

    // ── SszVector ──

    #[test]
    fn vector_u64_hash_tree_root() {
        let v: SszVector<u64, 4> = vec![1u64, 2, 3, 4].try_into().unwrap();
        let root = v.hash_tree_root(&Sha2Hasher);

        // Manual: 4 u64s = 32 bytes = 1 chunk, max_chunks = ceil(4*8/32) = 1
        let mut serialized = Vec::new();
        for val in v.iter() {
            val.ssz_append(&mut serialized);
        }
        let chunks = pack(&serialized);
        let expected = merkleize(&Sha2Hasher, &chunks, Some(1));
        assert_eq!(root, expected);
    }

    #[test]
    fn vector_u64_five_elements() {
        let v: SszVector<u64, 5> = vec![1u64, 2, 3, 4, 5].try_into().unwrap();
        let root = v.hash_tree_root(&Sha2Hasher);

        // 5 u64s = 40 bytes = 2 chunks, max_chunks = ceil(5*8/32) = 2
        let mut serialized = Vec::new();
        for val in v.iter() {
            val.ssz_append(&mut serialized);
        }
        let chunks = pack(&serialized);
        let expected = merkleize(&Sha2Hasher, &chunks, Some(2));
        assert_eq!(root, expected);
    }

    // ── SszList ──

    #[test]
    fn list_u64_hash_tree_root() {
        let mut list: SszList<u64, 8> = SszList::new();
        list.push(1).unwrap();
        list.push(2).unwrap();
        list.push(3).unwrap();
        let root = list.hash_tree_root(&Sha2Hasher);

        // 3 u64s = 24 bytes = 1 chunk, max_chunks = ceil(8*8/32) = 2
        let mut serialized = Vec::new();
        for val in list.iter() {
            val.ssz_append(&mut serialized);
        }
        let chunks = pack(&serialized);
        let inner_root = merkleize(&Sha2Hasher, &chunks, Some(2));
        let expected = mix_in_length(&Sha2Hasher, &inner_root, 3);
        assert_eq!(root, expected);
    }

    #[test]
    fn list_empty_hash_tree_root() {
        let list: SszList<u64, 8> = SszList::new();
        let root = list.hash_tree_root(&Sha2Hasher);

        // Empty: merkleize([], limit=2) then mix_in_length with 0
        let inner_root = merkleize(&Sha2Hasher, &[], Some(2));
        let expected = mix_in_length(&Sha2Hasher, &inner_root, 0);
        assert_eq!(root, expected);
    }

    // ── SszBitvector ──

    #[test]
    fn bitvector_hash_tree_root() {
        let mut bv = SszBitvector::<8>::new();
        bv.set(0, true).unwrap();
        bv.set(7, true).unwrap();
        let root = bv.hash_tree_root(&Sha2Hasher);

        // 8 bits = 1 byte, pack_bits produces 1 chunk
        let chunks = pack_bits(bv.as_bytes(), 8);
        let expected = merkleize(&Sha2Hasher, &chunks, Some(1));
        assert_eq!(root, expected);
    }

    #[test]
    fn bitvector_256_bits() {
        let bv = SszBitvector::<256>::new();
        let root = bv.hash_tree_root(&Sha2Hasher);

        // 256 bits = 32 bytes = 1 chunk, max_chunks = 1
        let chunks = pack_bits(bv.as_bytes(), 256);
        let expected = merkleize(&Sha2Hasher, &chunks, Some(1));
        assert_eq!(root, expected);
    }

    // ── SszBitlist ──

    #[test]
    fn bitlist_hash_tree_root() {
        let mut bl = SszBitlist::<64>::new();
        bl.push(true).unwrap();
        bl.push(false).unwrap();
        bl.push(true).unwrap();
        let root = bl.hash_tree_root(&Sha2Hasher);

        // 3 bits, pack_bits produces 1 chunk, max_chunks = ceil(64/256) = 1
        let chunks = pack_bits(bl.as_bytes(), 3);
        let inner_root = merkleize(&Sha2Hasher, &chunks, Some(1));
        let expected = mix_in_length(&Sha2Hasher, &inner_root, 3);
        assert_eq!(root, expected);
    }

    #[test]
    fn bitlist_empty_hash_tree_root() {
        let bl = SszBitlist::<64>::new();
        let root = bl.hash_tree_root(&Sha2Hasher);

        let chunks = pack_bits(bl.as_bytes(), 0);
        let inner_root = merkleize(&Sha2Hasher, &chunks, Some(1));
        let expected = mix_in_length(&Sha2Hasher, &inner_root, 0);
        assert_eq!(root, expected);
    }

    // ── Composite-element (variable-length) vectors and lists ──

    #[test]
    fn vector_of_variable_elements_hash_tree_root() {
        // Vector<List<u8, 10>, 3> — composite elements use per-element hash_tree_root
        let inner: Vec<SszList<u8, 10>> = vec![
            vec![1u8, 2, 3].try_into().unwrap(),
            vec![4u8, 5].try_into().unwrap(),
            vec![6u8].try_into().unwrap(),
        ];
        let v: SszVector<SszList<u8, 10>, 3> = inner.try_into().unwrap();
        let root = v.hash_tree_root(&Sha2Hasher);

        // Composite path: collect roots and merkleize with limit = N
        let roots: Vec<Node> = v
            .iter()
            .map(|item| item.hash_tree_root(&Sha2Hasher))
            .collect();
        let expected = merkleize(&Sha2Hasher, &roots, Some(3));
        assert_eq!(root, expected);
    }

    #[test]
    fn list_of_variable_elements_hash_tree_root() {
        // List<List<u8, 10>, 5> — composite elements
        let mut list: SszList<SszList<u8, 10>, 5> = SszList::new();
        list.push(vec![1u8, 2].try_into().unwrap()).unwrap();
        list.push(vec![3u8, 4, 5].try_into().unwrap()).unwrap();
        let root = list.hash_tree_root(&Sha2Hasher);

        // Composite path: collect roots, merkleize with limit = N, mix_in_length
        let roots: Vec<Node> = list
            .iter()
            .map(|item| item.hash_tree_root(&Sha2Hasher))
            .collect();
        let inner_root = merkleize(&Sha2Hasher, &roots, Some(5));
        let expected = mix_in_length(&Sha2Hasher, &inner_root, 2);
        assert_eq!(root, expected);
    }

    // ── Collections of byte arrays ──
    // `[u8; N]` is `Vector[byte, N]`, composite at every length, so each
    // element is one leaf (its own root) and the limit counts elements. The
    // expected roots below come from Lighthouse's `tree_hash` 0.12.

    fn decode_hex(hex: &str) -> Node {
        let mut node = [0u8; 32];
        for (i, byte) in node.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap();
        }
        node
    }

    #[test]
    fn list_of_short_byte_arrays_is_not_packed() {
        let empty: SszList<[u8; 20], 3> = SszList::new();
        assert_eq!(
            empty.hash_tree_root(&Sha2Hasher),
            decode_hex("28ba1834a3a7b657460ce79fa3a1d909ab8828fd557659d4d0554a9bdbc0ec30")
        );

        let two: SszList<[u8; 20], 3> = vec![[0x11; 20], [0x22; 20]].try_into().unwrap();
        assert_eq!(
            two.hash_tree_root(&Sha2Hasher),
            decode_hex("d03d6bc8b5a125c29318afccfb560d6513936076b5e8b35d30962aa07be83750")
        );
    }

    #[test]
    fn vector_of_short_byte_arrays_is_not_packed() {
        let v: SszVector<[u8; 4], 3> = vec![[1; 4], [2; 4], [3; 4]].try_into().unwrap();
        // One zero-padded leaf per element, three leaves.
        let leaves: Vec<Node> = v
            .iter()
            .map(|item| {
                let mut leaf = [0u8; 32];
                leaf[..4].copy_from_slice(item);
                leaf
            })
            .collect();
        let expected = merkleize(&Sha2Hasher, &leaves, Some(3));
        assert_eq!(v.hash_tree_root(&Sha2Hasher), expected);
    }
}
