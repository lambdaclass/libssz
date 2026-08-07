#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

#[cfg(feature = "ethereum_types")]
mod ethereum_types;

use libssz::SszEncode;

/// A 32-byte Merkle tree node.
pub type Node = [u8; 32];

include!(concat!(env!("OUT_DIR"), "/zero_hashes.rs"));

/// Trait for pluggable SHA-256 implementations.
///
/// Instance method (`&self`) enables passing `&impl Sha256Hasher` through the
/// call chain. The hasher struct is typically zero-sized so `&self` compiles away.
pub trait Sha256Hasher {
    fn hash(&self, data: &[u8]) -> [u8; 32];
}

/// Default SHA-256 hasher using the `sha2` crate.
#[cfg(feature = "sha2-backend")]
pub struct Sha2Hasher;

#[cfg(feature = "sha2-backend")]
impl Sha256Hasher for Sha2Hasher {
    fn hash(&self, data: &[u8]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).into()
    }
}

/// Hash two nodes together: SHA256(a || b).
#[inline]
pub fn hash_nodes(hasher: &impl Sha256Hasher, a: &Node, b: &Node) -> Node {
    let mut buf = [0u8; 64];
    buf[..32].copy_from_slice(a);
    buf[32..].copy_from_slice(b);
    hasher.hash(&buf)
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
/// If `limit` is `Some(n)`, the tree is padded as if there were `n` leaf chunks.
/// The padding is virtual: any subtree lying entirely beyond `chunks.len()` is
/// all zeros, so its root is read from [`ZERO_HASHES`] instead of being hashed.
///
/// Cost is `O(chunks.len())` plus one hash per virtual level above the real subtree.
/// Two buffers are allocated and reused (≈ `chunks.len()` and `chunks.len().div_ceil(2)` nodes).
#[cfg(feature = "alloc")]
pub fn merkleize(hasher: &impl Sha256Hasher, chunks: &[Node], limit: Option<usize>) -> Node {
    let count = match limit {
        Some(l) => {
            assert!(
                chunks.len() <= l,
                "bug: chunk count {} exceeds limit {} — bounded type invariant violated",
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

    let depth = count.next_power_of_two().trailing_zeros() as usize;

    // With no real chunks the whole tree is zeros, so the root is precomputed.
    if chunks.is_empty() {
        return ZERO_HASHES[depth];
    }

    // Depth of the smallest subtree covering all real chunks. Every level above
    // it pairs the running root with an all-zero sibling.
    let real_depth = chunks.len().next_power_of_two().trailing_zeros() as usize;

    // Fold the real chunks one level per iteration, swapping between two buffers
    // that are allocated once and reused, so no level allocates.
    //
    // Only full pairs of real nodes are hashed. A level with an odd node count
    // ends on the frontier, where the missing right sibling roots an all-zero
    // subtree, so `ZERO_HASHES[level]` stands in for it rather than being hashed.
    let mut layer: Vec<Node> = chunks.to_vec();
    let mut next: Vec<Node> = Vec::with_capacity(layer.len().div_ceil(2));

    for zero_hash in ZERO_HASHES.iter().take(real_depth) {
        next.clear();
        let mut pairs = layer.chunks_exact(2);
        for pair in &mut pairs {
            next.push(hash_nodes(hasher, &pair[0], &pair[1]));
        }
        if let [odd] = pairs.remainder() {
            next.push(hash_nodes(hasher, odd, zero_hash));
        }
        core::mem::swap(&mut layer, &mut next);
    }

    // `layer[0]` now roots the real-data subtree. Merge in the virtual levels.
    let mut root = layer[0];
    for zero_hash in ZERO_HASHES.iter().take(depth).skip(real_depth) {
        root = hash_nodes(hasher, &root, zero_hash);
    }

    root
}

/// Progressive merkleization: a chain of progressively larger binary subtrees.
///
/// Creates a 0-terminated sequence of binary subtrees with increasing leaf count:
/// `hash(merkleize(chunks[..1], 1), hash(merkleize(chunks[1..5], 4), hash(merkleize(chunks[5..21], 16), ...)))`
///
/// Leaf counts grow as: 1, 4, 16, 64, 256, ... (each 4x the previous).
///
/// Reference: EIP-7916 / consensus-specs simple-serialize.md
#[cfg(feature = "alloc")]
pub fn merkleize_progressive(hasher: &impl Sha256Hasher, chunks: &[Node]) -> Node {
    merkleize_progressive_inner(hasher, chunks, 1)
}

#[cfg(feature = "alloc")]
fn merkleize_progressive_inner(
    hasher: &impl Sha256Hasher,
    chunks: &[Node],
    num_leaves: usize,
) -> Node {
    if chunks.is_empty() {
        return [0u8; 32];
    }

    let take = core::cmp::min(num_leaves, chunks.len());
    let subtree = merkleize(hasher, &chunks[..take], Some(num_leaves));
    let rest = merkleize_progressive_inner(hasher, &chunks[take..], num_leaves * 4);
    // EIP-7916 computes `hash(a, b)` with `a` the fixed-size subtree over the
    // first `num_leaves` chunks and `b` the recursive remainder, so the subtree
    // is the left child and the remainder the right one.
    hash_nodes(hasher, &subtree, &rest)
}

/// Mix in an active_fields bitvector: hash_nodes(root, pack_bits(active_fields)).
#[cfg(feature = "alloc")]
pub fn mix_in_active_fields(
    hasher: &impl Sha256Hasher,
    root: &Node,
    active_fields: &[bool],
) -> Node {
    // active_fields is at most 256 bits = 1 chunk
    let mut bits_bytes = vec![0u8; active_fields.len().div_ceil(8)];
    for (i, &active) in active_fields.iter().enumerate() {
        if active {
            bits_bytes[i / 8] |= 1 << (i % 8);
        }
    }
    let chunks = pack_bits(&bits_bytes, active_fields.len());
    let af_node = chunks.first().copied().unwrap_or([0u8; 32]);
    hash_nodes(hasher, root, &af_node)
}

/// Mix in a length value: hash_nodes(root, length_as_le_bytes_node).
#[inline]
pub fn mix_in_length(hasher: &impl Sha256Hasher, root: &Node, length: usize) -> Node {
    let mut length_node = [0u8; 32];
    length_node[..8].copy_from_slice(&(length as u64).to_le_bytes());
    hash_nodes(hasher, root, &length_node)
}

/// Mix in a selector value: hash_nodes(root, selector_as_le_bytes_node).
#[inline]
pub fn mix_in_selector(hasher: &impl Sha256Hasher, root: &Node, selector: u8) -> Node {
    let mut selector_node = [0u8; 32];
    selector_node[0] = selector;
    hash_nodes(hasher, root, &selector_node)
}

/// Trait for types that can compute their SSZ hash tree root.
pub trait HashTreeRoot {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node;

    /// Returns `true` for SSZ basic types (bool, uN, byte arrays).
    /// Composite types (containers, vectors, lists) return `false`.
    /// Used by Vector/List HTR to decide between packing and per-element hashing.
    fn is_basic_type() -> bool
    where
        Self: Sized,
    {
        false
    }
}

// ── bool ──

impl HashTreeRoot for bool {
    #[inline(always)]
    fn hash_tree_root(&self, _hasher: &impl Sha256Hasher) -> Node {
        let mut node = [0u8; 32];
        node[0] = *self as u8;
        node
    }

    fn is_basic_type() -> bool {
        true
    }
}

// ── Unsigned integers ──

impl HashTreeRoot for u8 {
    #[inline(always)]
    fn hash_tree_root(&self, _hasher: &impl Sha256Hasher) -> Node {
        let mut node = [0u8; 32];
        let bytes = self.to_le_bytes();
        node[..bytes.len()].copy_from_slice(&bytes);
        node
    }

    fn is_basic_type() -> bool {
        true
    }
}

impl HashTreeRoot for u16 {
    #[inline(always)]
    fn hash_tree_root(&self, _hasher: &impl Sha256Hasher) -> Node {
        let mut node = [0u8; 32];
        let bytes = self.to_le_bytes();
        node[..bytes.len()].copy_from_slice(&bytes);
        node
    }

    fn is_basic_type() -> bool {
        true
    }
}

impl HashTreeRoot for u32 {
    #[inline(always)]
    fn hash_tree_root(&self, _hasher: &impl Sha256Hasher) -> Node {
        let mut node = [0u8; 32];
        let bytes = self.to_le_bytes();
        node[..bytes.len()].copy_from_slice(&bytes);
        node
    }

    fn is_basic_type() -> bool {
        true
    }
}

impl HashTreeRoot for u64 {
    #[inline(always)]
    fn hash_tree_root(&self, _hasher: &impl Sha256Hasher) -> Node {
        let mut node = [0u8; 32];
        let bytes = self.to_le_bytes();
        node[..bytes.len()].copy_from_slice(&bytes);
        node
    }

    fn is_basic_type() -> bool {
        true
    }
}

impl HashTreeRoot for u128 {
    #[inline(always)]
    fn hash_tree_root(&self, _hasher: &impl Sha256Hasher) -> Node {
        let mut node = [0u8; 32];
        let bytes = self.to_le_bytes();
        node[..bytes.len()].copy_from_slice(&bytes);
        node
    }

    fn is_basic_type() -> bool {
        true
    }
}

// ── [u8; N] ──

#[cfg(feature = "alloc")]
impl<const N: usize> HashTreeRoot for [u8; N] {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        if N <= 32 {
            let mut node = [0u8; 32];
            node[..N].copy_from_slice(self);
            node
        } else {
            merkleize(hasher, &pack(self), None)
        }
    }

    fn is_basic_type() -> bool {
        N <= 32
    }
}

// ── Vec<T> for basic types ──

#[cfg(feature = "alloc")]
impl<T: HashTreeRoot + SszEncode> HashTreeRoot for Vec<T> {
    fn hash_tree_root(&self, hasher: &impl Sha256Hasher) -> Node {
        let chunks: Vec<Node> = if T::is_basic_type() {
            let mut serialized = Vec::new();
            for item in self {
                item.ssz_append(&mut serialized);
            }
            pack(&serialized)
        } else {
            self.iter()
                .map(|item| item.hash_tree_root(hasher))
                .collect()
        };
        let root = if chunks.is_empty() {
            merkleize(hasher, &[ZERO_HASHES[0]], None)
        } else {
            merkleize(hasher, &chunks, None)
        };
        mix_in_length(hasher, &root, self.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use alloc::vec::Vec;

    #[cfg(feature = "sha2-backend")]
    use crate::Sha2Hasher;

    // ── hash_nodes tests ──

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_nodes_of_two_zero_nodes() {
        let zero = [0u8; 32];
        let result = hash_nodes(&Sha2Hasher, &zero, &zero);
        use sha2::{Digest, Sha256};
        let mut sha = Sha256::new();
        sha.update([0u8; 64]);
        let expected: [u8; 32] = sha.finalize().into();
        assert_eq!(result, expected);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_nodes_is_not_commutative() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        assert_ne!(
            hash_nodes(&Sha2Hasher, &a, &b),
            hash_nodes(&Sha2Hasher, &b, &a)
        );
    }

    // ── Zero hashes tests ──

    #[test]
    fn zero_hash_level_0_is_all_zeros() {
        assert_eq!(ZERO_HASHES[0], [0u8; 32]);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn zero_hash_level_1_is_hash_of_two_zeros() {
        let expected = hash_nodes(&Sha2Hasher, &[0u8; 32], &[0u8; 32]);
        assert_eq!(ZERO_HASHES[1], expected);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn zero_hash_level_2_is_hash_of_two_level_1() {
        let expected = hash_nodes(&Sha2Hasher, &ZERO_HASHES[1], &ZERO_HASHES[1]);
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

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_empty_returns_zero_hash() {
        let result = merkleize(&Sha2Hasher, &[], None);
        assert_eq!(result, ZERO_HASHES[0]);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_one_chunk_is_identity() {
        let chunk = [0x42u8; 32];
        let result = merkleize(&Sha2Hasher, &[chunk], None);
        assert_eq!(result, chunk);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_two_chunks() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        let result = merkleize(&Sha2Hasher, &[a, b], None);
        assert_eq!(result, hash_nodes(&Sha2Hasher, &a, &b));
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_three_chunks_pads_to_four() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        let c = [3u8; 32];
        let result = merkleize(&Sha2Hasher, &[a, b, c], None);
        // Tree: hash(hash(a,b), hash(c, zero))
        let left = hash_nodes(&Sha2Hasher, &a, &b);
        let right = hash_nodes(&Sha2Hasher, &c, &ZERO_HASHES[0]);
        assert_eq!(result, hash_nodes(&Sha2Hasher, &left, &right));
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_with_limit_pads_with_zero_hashes() {
        let a = [1u8; 32];
        // With limit=4, single chunk should be padded to 4 leaves
        let result = merkleize(&Sha2Hasher, &[a], Some(4));
        // Tree: hash(hash(a, zero), hash(zero, zero))
        let left = hash_nodes(&Sha2Hasher, &a, &ZERO_HASHES[0]);
        let right = ZERO_HASHES[1]; // hash(zero, zero)
        assert_eq!(result, hash_nodes(&Sha2Hasher, &left, &right));
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_with_limit_equal_to_count() {
        let a = [1u8; 32];
        let b = [2u8; 32];
        // limit=2 with 2 chunks should give same result as no limit
        assert_eq!(
            merkleize(&Sha2Hasher, &[a, b], Some(2)),
            merkleize(&Sha2Hasher, &[a, b], None)
        );
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    #[should_panic(expected = "chunk count")]
    fn merkleize_panics_if_count_exceeds_limit() {
        let chunks = [[0u8; 32]; 3];
        merkleize(&Sha2Hasher, &chunks, Some(2));
    }

    // ── merkleize: zero-subtree elision ──

    /// Naive merkleization: materializes every leaf up to `limit`, including the
    /// all-zero ones. Reference oracle for [`merkleize`], which must produce
    /// identical roots while skipping the zero subtrees.
    #[cfg(feature = "sha2-backend")]
    fn merkleize_fully_materialized(chunks: &[Node], limit: Option<usize>) -> Node {
        let count = core::cmp::max(limit.unwrap_or(chunks.len()), chunks.len());
        if count == 0 {
            return ZERO_HASHES[0];
        }
        let mut layer = chunks.to_vec();
        layer.resize(count.next_power_of_two(), ZERO_HASHES[0]);
        while layer.len() > 1 {
            layer = layer
                .chunks(2)
                .map(|pair| hash_nodes(&Sha2Hasher, &pair[0], &pair[1]))
                .collect();
        }
        layer[0]
    }

    /// Counts `hash_nodes` invocations while delegating to the real hasher, so
    /// tree shape is unaffected.
    #[cfg(feature = "sha2-backend")]
    struct CountingHasher {
        calls: core::cell::Cell<usize>,
    }

    #[cfg(feature = "sha2-backend")]
    impl CountingHasher {
        fn new() -> Self {
            Self {
                calls: core::cell::Cell::new(0),
            }
        }
    }

    #[cfg(feature = "sha2-backend")]
    impl Sha256Hasher for CountingHasher {
        fn hash(&self, data: &[u8]) -> [u8; 32] {
            self.calls.set(self.calls.get() + 1);
            Sha2Hasher.hash(data)
        }
    }

    /// Hash count for a merkleization that treats every subtree beyond
    /// `chunk_count` as a precomputed zero hash: one hash per node on the real
    /// frontier, plus one per virtual level above it.
    fn zero_aware_hash_count(chunk_count: usize, limit: Option<usize>) -> usize {
        let count = limit.unwrap_or(chunk_count);
        if count == 0 || chunk_count == 0 {
            return 0;
        }
        let depth = count.next_power_of_two().trailing_zeros() as usize;
        let real_depth = chunk_count.next_power_of_two().trailing_zeros() as usize;

        let mut total = depth - real_depth;
        let mut len = chunk_count;
        for _ in 0..real_depth {
            len = len.div_ceil(2);
            total += len;
        }
        total
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_matches_fully_materialized_oracle() {
        for n in 0..=70 {
            let chunks: Vec<Node> = (0..n).map(|i| [i as u8 + 1; 32]).collect();
            assert_eq!(
                merkleize(&Sha2Hasher, &chunks, None),
                merkleize_fully_materialized(&chunks, None),
                "no limit, {n} chunks"
            );
            for limit in [n, n + 1, n + 7, 64, 128, 1024] {
                if limit < n {
                    continue;
                }
                assert_eq!(
                    merkleize(&Sha2Hasher, &chunks, Some(limit)),
                    merkleize_fully_materialized(&chunks, Some(limit)),
                    "limit {limit}, {n} chunks"
                );
            }
        }
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_does_not_hash_zero_subtrees() {
        for n in [1usize, 2, 3, 5, 9, 17, 33, 65, 100, 1025] {
            let chunks: Vec<Node> = (0..n).map(|i| [i as u8; 32]).collect();
            for limit in [
                None,
                Some(n),
                Some(n.next_power_of_two() * 4),
                Some(1 << 18),
            ] {
                if limit.is_some_and(|l| l < n) {
                    continue;
                }
                let hasher = CountingHasher::new();
                merkleize(&hasher, &chunks, limit);
                assert_eq!(
                    hasher.calls.get(),
                    zero_aware_hash_count(n, limit),
                    "{n} chunks, limit {limit:?}"
                );
            }
        }
    }

    /// The regression this guards: crossing a power-of-two boundary used to
    /// double the hash count, because the padding leaves were materialized and
    /// hashed as if they held data.
    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_cost_is_linear_across_power_of_two_boundary() {
        let count_for = |n: usize| {
            let chunks: Vec<Node> = (0..n).map(|i| [i as u8; 32]).collect();
            let hasher = CountingHasher::new();
            merkleize(&hasher, &chunks, Some(1 << 18));
            hasher.calls.get()
        };

        let below = count_for(1024);
        let above = count_for(1025);
        assert!(
            above < below + 20,
            "one extra chunk added {} hashes (1024 -> {below}, 1025 -> {above})",
            above - below
        );
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_empty_with_limit_is_the_precomputed_zero_hash() {
        for (depth, zero_hash) in ZERO_HASHES.iter().enumerate().take(8) {
            let limit = 1usize << depth;
            assert_eq!(merkleize(&Sha2Hasher, &[], Some(limit)), *zero_hash);
        }
        // Non-power-of-two limits round up to the enclosing subtree.
        assert_eq!(merkleize(&Sha2Hasher, &[], Some(3)), ZERO_HASHES[2]);
        assert_eq!(merkleize(&Sha2Hasher, &[], Some(100)), ZERO_HASHES[7]);
    }

    // ── merkleize_progressive tests ──

    /// Decode a 64-character hex string into a `Node`.
    #[cfg(feature = "sha2-backend")]
    fn node_from_hex(s: &str) -> Node {
        let bytes = s.as_bytes();
        assert_eq!(bytes.len(), 64, "expected 64 hex characters");
        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            let hi = char::from(bytes[i * 2]).to_digit(16).expect("hex digit");
            let lo = char::from(bytes[i * 2 + 1])
                .to_digit(16)
                .expect("hex digit");
            *byte = ((hi << 4) | lo) as u8;
        }
        out
    }

    /// `hash_tree_root` of a `ProgressiveList[uint64]` holding `values`.
    #[cfg(feature = "sha2-backend")]
    fn progressive_u64_list_root(values: &[u64]) -> Node {
        let mut serialized = Vec::with_capacity(values.len() * 8);
        for value in values {
            serialized.extend_from_slice(&value.to_le_bytes());
        }
        let root = merkleize_progressive(&Sha2Hasher, &pack(&serialized));
        mix_in_length(&Sha2Hasher, &root, values.len())
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_progressive_empty_is_zero_node() {
        assert_eq!(merkleize_progressive(&Sha2Hasher, &[]), [0u8; 32]);
    }

    /// EIP-7916 puts the fixed-size subtree on the left and the recursive
    /// remainder on the right, so a lone chunk hashes as `hash(chunk, zero)`.
    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_progressive_puts_subtree_on_the_left() {
        let chunk = [0x11u8; 32];
        assert_eq!(
            merkleize_progressive(&Sha2Hasher, &[chunk]),
            hash_nodes(&Sha2Hasher, &chunk, &[0u8; 32])
        );
    }

    /// Roots of `ProgressiveList[uint64]([1, ..., n])` as computed by
    /// ethereum/remerkleable. Four `uint64`s pack into one chunk, so these
    /// sizes pack into 0, 1, 1, 2 and 6 chunks: `n = 5` spans the first two
    /// subtrees (leaf counts 1 then 4) and `n = 21` reaches the third (16),
    /// so the larger two exercise the recursion rather than the base case.
    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_progressive_matches_reference_roots() {
        let cases: [(u64, &str); 5] = [
            (
                0,
                "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b",
            ),
            (
                1,
                "905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b",
            ),
            (
                2,
                "4250789d7838bee417a2b0d7639d928b05e8b75f1fc59588a4301b6e8f70ba58",
            ),
            (
                5,
                "29918e0447260511bc5be0f7dbb9817201e16e30c56af228b9cb931a16e8799d",
            ),
            (
                21,
                "ed360c03ecbdfbb6f4b1cf5d9cbf6887038423e31121700797de968a9969aaed",
            ),
        ];
        for (n, expected) in cases {
            let values: Vec<u64> = (1..=n).collect();
            assert_eq!(
                progressive_u64_list_root(&values),
                node_from_hex(expected),
                "ProgressiveList[uint64] of 1..={n}"
            );
        }
    }

    /// Roots pinned from the consensus-specs `basic_progressive_list` vectors
    /// (v1.7.0-alpha.13, `tests/general/phase0/ssz_generic`).
    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_progressive_matches_consensus_spec_vectors() {
        let cases: [(usize, u64, &str, &str); 5] = [
            (
                1,
                u64::MAX,
                "7bea313629252f757f27d17a1ce515715beedeff41a3f7f6c9ac47bfddcf447c",
                "proglist_uint64_max_1",
            ),
            (
                4,
                u64::MAX,
                "06e8318500bbdb0b6e9b55e63e819cbed45668f6481c24c67bd1d8eaf8703ca8",
                "proglist_uint64_max_20",
            ),
            (
                21,
                u64::MAX,
                "d444bef5f61103078f3ca9bdb2857a9b5e883d738b213a1607a9f3a770a332d2",
                "proglist_uint64_max_22",
            ),
            (
                7,
                0,
                "13a56a67f02ea52c0841043aba35de738bec8519fee07860658d13e2d0442782",
                "proglist_uint64_zero_8",
            ),
            (
                53,
                0,
                "2935884058446007e2592494fe88884e83ee80ecd2041779447c30642fe63ac8",
                "proglist_uint64_zero_86",
            ),
        ];
        for (count, value, expected, case_name) in cases {
            let values = vec![value; count];
            assert_eq!(
                progressive_u64_list_root(&values),
                node_from_hex(expected),
                "{case_name}"
            );
        }
    }

    // ── mix_in_length tests ──

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn mix_in_length_known_value() {
        let root = [0u8; 32];
        let result = mix_in_length(&Sha2Hasher, &root, 5);
        let mut len_node = [0u8; 32];
        len_node[..8].copy_from_slice(&5u64.to_le_bytes());
        assert_eq!(result, hash_nodes(&Sha2Hasher, &root, &len_node));
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn mix_in_length_zero() {
        let root = [0xAB; 32];
        let result = mix_in_length(&Sha2Hasher, &root, 0);
        // length=0 means length_node is all zeros
        assert_eq!(result, hash_nodes(&Sha2Hasher, &root, &[0u8; 32]));
    }

    // ── mix_in_selector tests ──

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn mix_in_selector_known_value() {
        let root = [0u8; 32];
        let result = mix_in_selector(&Sha2Hasher, &root, 3);
        let mut sel_node = [0u8; 32];
        sel_node[0] = 3;
        assert_eq!(result, hash_nodes(&Sha2Hasher, &root, &sel_node));
    }

    // ── HashTreeRoot tests ──

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_bool_false() {
        let result = false.hash_tree_root(&Sha2Hasher);
        assert_eq!(result, [0u8; 32]);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_bool_true() {
        let result = true.hash_tree_root(&Sha2Hasher);
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(result, expected);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_u64() {
        let val: u64 = 0x0102030405060708;
        let result = val.hash_tree_root(&Sha2Hasher);
        let mut expected = [0u8; 32];
        expected[..8].copy_from_slice(&val.to_le_bytes());
        assert_eq!(result, expected);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_u8() {
        let val: u8 = 42;
        let result = val.hash_tree_root(&Sha2Hasher);
        let mut expected = [0u8; 32];
        expected[0] = 42;
        assert_eq!(result, expected);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_u128() {
        let val: u128 = 1;
        let result = val.hash_tree_root(&Sha2Hasher);
        let mut expected = [0u8; 32];
        expected[..16].copy_from_slice(&val.to_le_bytes());
        assert_eq!(result, expected);
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_byte_array_32_is_identity() {
        let arr = [0xab_u8; 32];
        assert_eq!(arr.hash_tree_root(&Sha2Hasher), arr);
        assert!(<[u8; 32]>::is_basic_type());
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_byte_array_20_is_padded() {
        let arr = [0xcd_u8; 20];
        let root = arr.hash_tree_root(&Sha2Hasher);
        assert_eq!(&root[..20], &arr[..]);
        assert_eq!(&root[20..], &[0u8; 12]);
        assert!(<[u8; 20]>::is_basic_type());
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_byte_array_4_is_padded() {
        let arr = [0x01, 0x02, 0x03, 0x04];
        let root = arr.hash_tree_root(&Sha2Hasher);
        assert_eq!(&root[..4], &arr[..]);
        assert_eq!(&root[4..], &[0u8; 28]);
        assert!(<[u8; 4]>::is_basic_type());
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_byte_array_7_is_padded() {
        let arr = [0xff_u8; 7];
        let root = arr.hash_tree_root(&Sha2Hasher);
        assert_eq!(&root[..7], &arr[..]);
        assert_eq!(&root[7..], &[0u8; 25]);
        assert!(<[u8; 7]>::is_basic_type());
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_byte_array_48_is_merkleized() {
        let arr = [0xab_u8; 48];
        let root = arr.hash_tree_root(&Sha2Hasher);
        // 48 bytes = 2 chunks (32 + 16 zero-padded), merkleize
        let expected = merkleize(&Sha2Hasher, &pack(&arr), None);
        assert_eq!(root, expected);
        assert!(!<[u8; 48]>::is_basic_type());
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_byte_array_52_is_merkleized() {
        let arr = [0xcd_u8; 52];
        let root = arr.hash_tree_root(&Sha2Hasher);
        let expected = merkleize(&Sha2Hasher, &pack(&arr), None);
        assert_eq!(root, expected);
        assert!(!<[u8; 52]>::is_basic_type());
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_byte_array_96_is_merkleized() {
        let arr = [0xff_u8; 96];
        let root = arr.hash_tree_root(&Sha2Hasher);
        let expected = merkleize(&Sha2Hasher, &pack(&arr), None);
        assert_eq!(root, expected);
        assert!(!<[u8; 96]>::is_basic_type());
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_vec_u64_empty() {
        let val: Vec<u64> = vec![];
        let result = val.hash_tree_root(&Sha2Hasher);
        // Empty list: merkleize([zero]) then mix_in_length with 0
        let root = merkleize(&Sha2Hasher, &[ZERO_HASHES[0]], None);
        assert_eq!(result, mix_in_length(&Sha2Hasher, &root, 0));
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_vec_u64() {
        let val: Vec<u64> = vec![1, 2, 3, 4];
        let result = val.hash_tree_root(&Sha2Hasher);

        // 4 u64s = 32 bytes = 1 chunk
        let mut serialized = Vec::new();
        for v in &val {
            serialized.extend_from_slice(&v.to_le_bytes());
        }
        let chunks = pack(&serialized);
        let root = merkleize(&Sha2Hasher, &chunks, None);
        assert_eq!(result, mix_in_length(&Sha2Hasher, &root, 4));
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_tree_root_vec_u64_five_elements() {
        let val: Vec<u64> = vec![1, 2, 3, 4, 5];
        let result = val.hash_tree_root(&Sha2Hasher);

        // 5 u64s = 40 bytes = 2 chunks
        let mut serialized = Vec::new();
        for v in &val {
            serialized.extend_from_slice(&v.to_le_bytes());
        }
        let chunks = pack(&serialized);
        assert_eq!(chunks.len(), 2);
        let root = merkleize(&Sha2Hasher, &chunks, None);
        assert_eq!(result, mix_in_length(&Sha2Hasher, &root, 5));
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn custom_hasher_works() {
        struct MockHasher;
        impl Sha256Hasher for MockHasher {
            fn hash(&self, data: &[u8]) -> [u8; 32] {
                let mut out = [0u8; 32];
                for (i, &b) in data.iter().enumerate() {
                    out[i % 32] ^= b;
                }
                out
            }
        }
        let val: u64 = 42;
        let root_sha2 = val.hash_tree_root(&Sha2Hasher);
        let root_mock = val.hash_tree_root(&MockHasher);
        // u64 HTR doesn't use hashing (just pads to 32 bytes), so both should be equal
        assert_eq!(root_sha2, root_mock);

        // For a type that DOES hash, they should differ
        let arr = [0xab_u8; 48];
        let root_sha2 = arr.hash_tree_root(&Sha2Hasher);
        let root_mock = arr.hash_tree_root(&MockHasher);
        assert_ne!(root_sha2, root_mock);
    }
}
