#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::{vec, vec::Vec};

#[cfg(feature = "ethereum_types")]
mod ethereum_types;

#[cfg(all(feature = "std", target_arch = "x86_64"))]
mod shani;

#[cfg(all(feature = "std", target_arch = "aarch64", target_endian = "little"))]
mod neon;

// So that the `ssz-derive` derives, which write `libssz_merkle::…`, work inside this
// crate (`verif_example`).
#[cfg(feature = "verif-example")]
extern crate self as libssz_merkle;

#[cfg(feature = "verif-example")]
pub mod verif_example;

use libssz::SszEncode;

/// A 32-byte Merkle tree node.
pub type Node = [u8; 32];

include!(concat!(env!("OUT_DIR"), "/zero_hashes.rs"));

/// Trait for pluggable SHA-256 implementations.
///
/// Instance method (`&self`) enables passing `&impl Sha256Hasher` through the
/// call chain. The hasher struct is typically zero-sized so `&self` compiles away.
///
/// Only [`hash`](Sha256Hasher::hash) is required. The other two methods say the same thing
/// for the inputs a Merkle tree has, so that a hasher with a faster way to hash two nodes,
/// or many pairs of them, can provide it.
pub trait Sha256Hasher {
    fn hash(&self, data: &[u8]) -> [u8; 32];

    /// `hash(a ‖ b)`.
    #[inline]
    fn hash_pair(&self, a: &Node, b: &Node) -> Node {
        let mut buf = [0u8; 64];
        buf[..32].copy_from_slice(a);
        buf[32..].copy_from_slice(b);
        self.hash(&buf)
    }

    /// One level of a Merkle tree: writes to `out[k]` the hash of `nodes[2 * k]` and the
    /// node after it. A last node without one is hashed with `zero_hash`. That is
    /// `nodes.len().div_ceil(2)` nodes; the rest of `out` is left as it was.
    ///
    /// # Panics
    ///
    /// If `out` is shorter than that.
    #[inline]
    fn hash_layer(&self, nodes: &[Node], out: &mut [Node], zero_hash: &Node) {
        layer(self, nodes, out, zero_hash)
    }

    /// [`hash_layer`](Sha256Hasher::hash_layer) with the level written over the start of
    /// `nodes` itself: `nodes[k]` becomes the hash of what `nodes[2 * k]` and the node
    /// after it held. The nodes from `nodes.len().div_ceil(2)` on are left as they were.
    #[inline]
    fn hash_layer_in_place(&self, nodes: &mut [Node], zero_hash: &Node) {
        layer_in_place(self, nodes, zero_hash)
    }
}

/// [`Sha256Hasher::hash_layer`] one pair at a time.
fn layer<H: Sha256Hasher + ?Sized>(hasher: &H, nodes: &[Node], out: &mut [Node], zero_hash: &Node) {
    let pairs = nodes.len() / 2;
    let mut k = 0;
    while k < pairs {
        out[k] = hasher.hash_pair(&nodes[2 * k], &nodes[2 * k + 1]);
        k += 1;
    }
    if nodes.len() % 2 == 1 {
        out[pairs] = hasher.hash_pair(&nodes[2 * pairs], zero_hash);
    }
}

/// [`Sha256Hasher::hash_layer_in_place`] one pair at a time. Every node is read before the
/// write that replaces it, since `k <= 2 * k`.
fn layer_in_place<H: Sha256Hasher + ?Sized>(hasher: &H, nodes: &mut [Node], zero_hash: &Node) {
    let pairs = nodes.len() / 2;
    let mut k = 0;
    while k < pairs {
        let parent = hasher.hash_pair(&nodes[2 * k], &nodes[2 * k + 1]);
        nodes[k] = parent;
        k += 1;
    }
    if nodes.len() % 2 == 1 {
        let parent = hasher.hash_pair(&nodes[2 * pairs], zero_hash);
        nodes[pairs] = parent;
    }
}

/// Default SHA-256 hasher using the `sha2` crate.
///
/// With the `std` feature, pairs of nodes are hashed by this crate's own kernel when the CPU
/// has the SHA-256 instructions, up to four pairs at a time: the SHA extensions on x86-64,
/// and `FEAT_SHA256` on little-endian AArch64. The result is the same SHA-256.
#[cfg(feature = "sha2-backend")]
pub struct Sha2Hasher;

#[cfg(feature = "sha2-backend")]
impl Sha256Hasher for Sha2Hasher {
    fn hash(&self, data: &[u8]) -> [u8; 32] {
        use sha2::{Digest, Sha256};
        Sha256::digest(data).into()
    }

    #[inline]
    fn hash_pair(&self, a: &Node, b: &Node) -> Node {
        #[cfg(all(feature = "std", target_arch = "x86_64"))]
        if shani::available() {
            // SAFETY: `available` has just confirmed every CPU feature the kernel enables.
            return unsafe { shani::hash_pair(a, b) };
        }
        #[cfg(all(feature = "std", target_arch = "aarch64", target_endian = "little"))]
        if neon::available() {
            // SAFETY: `available` has just confirmed every CPU feature the kernel enables.
            return unsafe { neon::hash_pair(a, b) };
        }
        let mut buf = [0u8; 64];
        buf[..32].copy_from_slice(a);
        buf[32..].copy_from_slice(b);
        self.hash(&buf)
    }

    #[inline]
    fn hash_layer(&self, nodes: &[Node], out: &mut [Node], zero_hash: &Node) {
        #[cfg(all(feature = "std", target_arch = "x86_64"))]
        if shani::available() {
            // SAFETY: `available` has just confirmed every CPU feature the kernel enables.
            return unsafe { shani::hash_layer(nodes, out, false, zero_hash) };
        }
        #[cfg(all(feature = "std", target_arch = "aarch64", target_endian = "little"))]
        if neon::available() {
            // SAFETY: `available` has just confirmed every CPU feature the kernel enables.
            return unsafe { neon::hash_layer(nodes, out, false, zero_hash) };
        }
        layer(self, nodes, out, zero_hash)
    }

    #[inline]
    fn hash_layer_in_place(&self, nodes: &mut [Node], zero_hash: &Node) {
        #[cfg(all(feature = "std", target_arch = "x86_64"))]
        if shani::available() {
            // SAFETY: `available` has just confirmed every CPU feature the kernel enables.
            return unsafe { shani::hash_layer(&[], nodes, true, zero_hash) };
        }
        #[cfg(all(feature = "std", target_arch = "aarch64", target_endian = "little"))]
        if neon::available() {
            // SAFETY: `available` has just confirmed every CPU feature the kernel enables.
            return unsafe { neon::hash_layer(&[], nodes, true, zero_hash) };
        }
        layer_in_place(self, nodes, zero_hash)
    }
}

/// Hash two nodes together: SHA256(a || b).
#[inline]
pub fn hash_nodes(hasher: &impl Sha256Hasher, a: &Node, b: &Node) -> Node {
    hasher.hash_pair(a, b)
}

/// Pack serialized bytes into 32-byte chunks, zero-padding the last chunk if needed.
#[cfg(feature = "alloc")]
pub fn pack(values: &[u8]) -> Vec<Node> {
    // The whole chunks are one copy; only a last partial chunk is built apart.
    let (whole, rest) = values.as_chunks::<32>();
    let mut chunks = Vec::with_capacity(values.len().div_ceil(32));
    chunks.extend_from_slice(whole);
    if !rest.is_empty() {
        let mut last = [0u8; 32];
        last[..rest.len()].copy_from_slice(rest);
        chunks.push(last);
    }
    chunks
}

/// The serializations of `items` one after another: the bytes a list of basic items packs.
#[cfg(feature = "alloc")]
fn basic_items_bytes<T: SszEncode>(items: &[T]) -> Vec<u8> {
    if T::is_fixed_size() {
        // The item type builds the buffer: the integers do it in bulk.
        T::ssz_fixed_slice_to_vec(items)
    } else {
        let mut serialized = Vec::new();
        for item in items {
            item.ssz_append(&mut serialized);
        }
        serialized
    }
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
/// The chunks are left as they are: up to 32 of them are hashed into a buffer on the
/// stack, and more than that are copied first. [`merkleize_in_place`] does neither.
#[cfg(feature = "alloc")]
pub fn merkleize(hasher: &impl Sha256Hasher, chunks: &[Node], limit: Option<usize>) -> Node {
    let depth = tree_depth(chunks.len(), limit);

    // With no real chunks the whole tree is zeros, so the root is precomputed.
    if chunks.is_empty() {
        return ZERO_HASHES[depth];
    }

    let root = if chunks.len() == 1 {
        chunks[0]
    } else if chunks.len() <= 8 {
        real_root_on_stack::<4>(hasher, chunks)
    } else if chunks.len() <= 32 {
        real_root_on_stack::<16>(hasher, chunks)
    } else {
        real_root(hasher, &mut chunks.to_vec(), 0)
    };

    virtual_root(hasher, root, chunks.len(), depth)
}

/// [`merkleize`] with the tree hashed over `chunks` itself, which takes no other memory.
/// What `chunks` holds afterwards is not specified.
pub fn merkleize_in_place(
    hasher: &impl Sha256Hasher,
    chunks: &mut [Node],
    limit: Option<usize>,
) -> Node {
    let depth = tree_depth(chunks.len(), limit);

    // With no real chunks the whole tree is zeros, so the root is precomputed.
    if chunks.is_empty() {
        return ZERO_HASHES[depth];
    }

    let count = chunks.len();
    let root = real_root(hasher, chunks, 0);
    virtual_root(hasher, root, count, depth)
}

/// The depth of the tree that `limit` asks for, or of the tree of `len` chunks without one.
///
/// # Panics
///
/// If there are more chunks than the limit.
fn tree_depth(len: usize, limit: Option<usize>) -> usize {
    let count = match limit {
        Some(l) => {
            assert!(
                len <= l,
                "bug: chunk count {} exceeds limit {} — bounded type invariant violated",
                len,
                l
            );
            l
        }
        None => len,
    };

    ceil_log2(count)
}

/// The depth of the smallest perfect tree with room for `count` leaves:
/// `count.next_power_of_two().trailing_zeros()`, which is 0 for no leaves or one.
///
/// It is written with `leading_zeros` and on a `u64`, because the Lean library of Aeneas
/// models `leading_zeros` but neither `next_power_of_two` nor `trailing_zeros`. Past
/// `2^63` this gives 64, which is what the other form gives in a release build, where
/// `next_power_of_two` wraps to 0; a debug build panics there instead.
#[inline]
fn ceil_log2(count: usize) -> usize {
    if count <= 1 {
        0
    } else {
        (64 - ((count - 1) as u64).leading_zeros()) as usize
    }
}

/// The root of the tree of depth `depth`, given the `root` of the smallest subtree that
/// covers its `len` real chunks. Every level above that subtree pairs the running root
/// with an all-zero sibling.
fn virtual_root(hasher: &impl Sha256Hasher, mut root: Node, len: usize, depth: usize) -> Node {
    // A `while` and not `iter().take(depth).skip(…)`: the Lean library of Aeneas has no
    // model of `skip`. `depth` is at most 64, so every index is inside `ZERO_HASHES`.
    let mut level = ceil_log2(len);
    while level < depth {
        root = hash_nodes(hasher, &root, &ZERO_HASHES[level]);
        level += 1;
    }
    root
}

/// [`real_root`] of two or more `chunks`, at most `2 * M`, which are left as they are: the
/// level above them goes to `M` nodes of the stack.
#[cfg(feature = "alloc")]
#[inline]
fn real_root_on_stack<const M: usize>(hasher: &impl Sha256Hasher, chunks: &[Node]) -> Node {
    let mut above = [[0u8; 32]; M];
    hasher.hash_layer(chunks, &mut above, &ZERO_HASHES[0]);
    real_root(hasher, &mut above[..chunks.len().div_ceil(2)], 1)
}

/// Root of the smallest subtree that covers `nodes`, of which there is at least one. They
/// are `level` levels above the chunks.
///
/// The tree is hashed over `nodes` itself, each level over the start of the one below.
/// A level with an odd node count ends on the frontier, where the missing right sibling
/// roots an all-zero subtree, so the entry of [`ZERO_HASHES`] for that level stands in for
/// it rather than being hashed.
fn real_root(hasher: &impl Sha256Hasher, nodes: &mut [Node], mut level: usize) -> Node {
    let mut len = nodes.len();
    while len > 1 {
        hasher.hash_layer_in_place(&mut nodes[..len], &ZERO_HASHES[level]);
        len = len.div_ceil(2);
        level += 1;
    }
    nodes[0]
}

/// The roots of groups of `width` nodes, all hashed together: `nodes` holds the groups one
/// after the other, and the root of group `j` ends up in `nodes[j]`. What the rest of
/// `nodes` holds afterwards is not specified.
///
/// `width` must be a power of two and `nodes.len()` a multiple of it. Each group is then a
/// perfect tree, and one [`Sha256Hasher::hash_layer_in_place`] over all of them hashes a
/// level of every group: with an even number of nodes per group, no pair crosses two
/// groups. A level of one small tree has one or two pairs; a level of many of them keeps
/// every stream of the hasher busy.
#[doc(hidden)]
pub fn merkleize_groups(hasher: &impl Sha256Hasher, nodes: &mut [Node], width: usize) {
    let mut len = nodes.len();
    let mut w = width;
    while w > 1 {
        hasher.hash_layer_in_place(&mut nodes[..len], &ZERO_HASHES[0]);
        len /= 2;
        w /= 2;
    }
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

    /// How many nodes [`hash_tree_root_row`](HashTreeRoot::hash_tree_root_row) writes: a
    /// power of two, from 1 to 256. The default is 1.
    #[doc(hidden)]
    fn hash_tree_root_width() -> usize
    where
        Self: Sized,
    {
        1
    }

    /// The bottom row of a tree whose root is the hash tree root of `self`: writes
    /// [`hash_tree_root_width`](HashTreeRoot::hash_tree_root_width) nodes to the start of
    /// `row`, and leaves the rest as it is. The default writes the root itself, a tree of
    /// one node. `#[derive(HashTreeRoot)]` writes the field roots of a container, padded
    /// with zero chunks: [`hash_tree_roots`] then hashes the trees of many items together.
    ///
    /// # Panics
    ///
    /// If `row` is shorter than the width.
    #[doc(hidden)]
    fn hash_tree_root_row(&self, hasher: &impl Sha256Hasher, row: &mut [Node]) {
        row[0] = self.hash_tree_root(hasher);
    }
}

/// Writes the hash tree root of `items[i]` to `out[i]`, for every `i`; the rest of `out` is
/// left as it is. Lists and vectors of composite items get their item roots from here.
///
/// The rows of [`HashTreeRoot::hash_tree_root_row`] of as many items as fit in 256 nodes go
/// one after the other, and [`merkleize_groups`] hashes their trees together, a level at a
/// time. A level of one container has one or two pairs; a level of many of them keeps every
/// stream of the hasher busy. The roots are the same as one by one.
///
/// # Panics
///
/// If `out` is shorter than `items`, or if the width is not from 1 to 256.
#[doc(hidden)]
pub fn hash_tree_roots<T: HashTreeRoot>(items: &[T], hasher: &impl Sha256Hasher, out: &mut [Node]) {
    let width = T::hash_tree_root_width();
    assert!(width != 0, "hash_tree_root_width is 0");
    assert!(width <= 256, "hash_tree_root_width is over 256");
    let per_block = 256 / width;
    // `while` with indices, without iterators, for Aeneas.
    let mut leaves = [[0u8; 32]; 256];
    let mut i = 0;
    while i < items.len() {
        let m = if items.len() - i < per_block {
            items.len() - i
        } else {
            per_block
        };
        let mut j = 0;
        while j < m {
            items[i + j].hash_tree_root_row(hasher, &mut leaves[j * width..(j + 1) * width]);
            j += 1;
        }
        merkleize_groups(hasher, &mut leaves[..m * width], width);
        out[i..i + m].copy_from_slice(&leaves[..m]);
        i += m;
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
        } else if N <= 256 {
            // What `pack` returns, in eight chunks of the stack.
            let mut chunks = [[0u8; 32]; 8];
            let (whole, rest) = self.as_chunks::<32>();
            chunks[..whole.len()].copy_from_slice(whole);
            if !rest.is_empty() {
                chunks[whole.len()][..rest.len()].copy_from_slice(rest);
            }
            merkleize_in_place(hasher, &mut chunks[..N.div_ceil(32)], None)
        } else {
            merkleize_in_place(hasher, &mut pack(self), None)
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
        let mut chunks: Vec<Node> = if T::is_basic_type() {
            pack(&basic_items_bytes(self))
        } else {
            let mut roots = vec![[0u8; 32]; self.len()];
            hash_tree_roots(self, hasher, &mut roots);
            roots
        };
        let root = if chunks.is_empty() {
            merkleize(hasher, &[ZERO_HASHES[0]], None)
        } else {
            merkleize_in_place(hasher, &mut chunks, None)
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

    // ── ceil_log2 ──

    #[test]
    fn ceil_log2_is_next_power_of_two_trailing_zeros() {
        let reference = |n: usize| n.next_power_of_two().trailing_zeros() as usize;
        for n in 0..5000 {
            assert_eq!(ceil_log2(n), reference(n), "n = {n}");
        }
        for k in 1..64 {
            for n in [(1usize << k) - 1, 1 << k, (1 << k) + 1] {
                if n <= 1 << 63 {
                    assert_eq!(ceil_log2(n), reference(n), "n = {n}");
                }
            }
        }
        // Past 2^63, `next_power_of_two` overflows: a release build wraps it to 0, whose
        // `trailing_zeros` is 64.
        assert_eq!(ceil_log2((1 << 63) + 1), 64);
        assert_eq!(ceil_log2(usize::MAX), 64);
    }

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

    /// The level above the chunks goes to four nodes of the stack up to 8 chunks and to
    /// sixteen up to 32; more chunks than that are copied to the heap.
    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_matches_oracle_around_buffer_sizes() {
        for n in [
            7usize, 8, 9, 15, 16, 17, 31, 32, 33, 34, 63, 64, 65, 127, 128, 129, 255, 256, 257,
            1000, 1023, 1024, 1025,
        ] {
            let chunks: Vec<Node> = (0..n)
                .map(|i| {
                    let mut chunk = [(i % 251) as u8 + 1; 32];
                    chunk[0] = (i >> 8) as u8;
                    chunk
                })
                .collect();
            for limit in [None, Some(n), Some(n + 1), Some(2 * n + 1), Some(4096)] {
                assert_eq!(
                    merkleize(&Sha2Hasher, &chunks, limit),
                    merkleize_fully_materialized(&chunks, limit),
                    "{n} chunks, limit {limit:?}"
                );
            }
        }
    }

    /// Hashing over the chunks themselves gives the root of [`merkleize`], with as many
    /// hashes.
    #[cfg(feature = "sha2-backend")]
    #[test]
    fn merkleize_groups_is_merkleize_of_each_group() {
        let all: Vec<Node> = (0..1024u32)
            .map(|i| {
                let mut n = [0u8; 32];
                n[..4].copy_from_slice(&i.wrapping_mul(2_654_435_761).to_le_bytes());
                n[31] = (i % 7) as u8;
                n
            })
            .collect();
        for width in [1usize, 2, 4, 8, 16, 32] {
            for groups in [0usize, 1, 2, 3, 5, 8, 9, 31] {
                let mut nodes = all[..width * groups].to_vec();
                merkleize_groups(&Sha2Hasher, &mut nodes, width);
                for j in 0..groups {
                    let want = merkleize(&Sha2Hasher, &all[j * width..(j + 1) * width], None);
                    assert_eq!(nodes[j], want, "width {width}, group {j} of {groups}");
                }
            }
        }
    }

    #[test]
    fn hash_tree_roots_of_width_one_is_one_by_one() {
        for n in [0usize, 1, 2, 255, 256, 257, 600] {
            let items: Vec<u64> = (0..n as u64).collect();
            let mut out = vec![[0xaa; 32]; n + 2];
            hash_tree_roots(&items, &Sha2Hasher, &mut out);
            for (i, x) in items.iter().enumerate() {
                assert_eq!(out[i], x.hash_tree_root(&Sha2Hasher));
            }
            assert_eq!(out[n..], [[0xaa; 32]; 2]);
        }
    }

    #[test]
    fn merkleize_in_place_is_merkleize() {
        for n in (0usize..=70).chain([127, 128, 129, 255, 256, 257, 1000, 1023, 1024, 1025]) {
            let chunks: Vec<Node> = (0..n)
                .map(|i| {
                    let mut chunk = [(i % 251) as u8 + 1; 32];
                    chunk[0] = (i >> 8) as u8;
                    chunk
                })
                .collect();
            for limit in [None, Some(n), Some(n + 1), Some(2 * n + 1), Some(4096)] {
                let want = merkleize_fully_materialized(&chunks, limit);
                assert_eq!(
                    merkleize_in_place(&Sha2Hasher, &mut chunks.clone(), limit),
                    want,
                    "{n} chunks, limit {limit:?}"
                );
                let counting = CountingHasher::new();
                assert_eq!(
                    merkleize_in_place(&counting, &mut chunks.clone(), limit),
                    want,
                    "{n} chunks, limit {limit:?}, one pair at a time"
                );
                assert_eq!(
                    counting.calls.get(),
                    zero_aware_hash_count(n, limit),
                    "{n} chunks, limit {limit:?}"
                );
            }
        }
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    #[should_panic(expected = "exceeds limit")]
    fn merkleize_in_place_panics_if_count_exceeds_limit() {
        let mut chunks = [[0u8; 32]; 3];
        merkleize_in_place(&Sha2Hasher, &mut chunks, Some(2));
    }

    /// A level, as the trait's two methods must write it whoever provides them.
    #[cfg(feature = "sha2-backend")]
    fn level_reference(nodes: &[Node], zero_hash: &Node) -> Vec<Node> {
        nodes
            .chunks(2)
            .map(|pair| {
                let mut both = [0u8; 64];
                both[..32].copy_from_slice(&pair[0]);
                both[32..].copy_from_slice(pair.get(1).unwrap_or(zero_hash));
                Sha2Hasher.hash(&both)
            })
            .collect()
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn hash_layer_writes_the_level_and_nothing_else() {
        let zero_hash = [0x5a; 32];
        let all: Vec<Node> = (0..67usize)
            .map(|i| {
                let mut node = [i as u8 ^ 0xc3; 32];
                node[i % 32] = i as u8;
                node
            })
            .collect();
        for len in 0..=all.len() {
            let nodes = &all[..len];
            let want = level_reference(nodes, &zero_hash);
            assert_eq!(want.len(), len.div_ceil(2));
            for spare in [0, 1, 3] {
                let mut plain = vec![[0xaa; 32]; want.len() + spare];
                CountingHasher::new().hash_layer(nodes, &mut plain, &zero_hash);
                let mut fast = plain.clone();
                fast[..want.len()].fill([0xaa; 32]);
                Sha2Hasher.hash_layer(nodes, &mut fast, &zero_hash);
                for out in [&plain, &fast] {
                    assert_eq!(out[..want.len()], want[..], "{len} nodes");
                    assert!(out[want.len()..].iter().all(|node| *node == [0xaa; 32]));
                }
            }

            let mut plain = nodes.to_vec();
            CountingHasher::new().hash_layer_in_place(&mut plain, &zero_hash);
            let mut fast = nodes.to_vec();
            Sha2Hasher.hash_layer_in_place(&mut fast, &zero_hash);
            for out in [&plain, &fast] {
                assert_eq!(out[..want.len()], want[..], "{len} nodes, in place");
                assert_eq!(
                    out[want.len()..],
                    nodes[want.len()..],
                    "{len} nodes, in place"
                );
            }
        }
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    #[should_panic]
    fn hash_layer_panics_on_a_short_output() {
        let nodes = [[1u8; 32]; 7];
        let mut out = [[0u8; 32]; 3];
        Sha2Hasher.hash_layer(&nodes, &mut out, &[0u8; 32]);
    }

    /// `pack` as the specification words it: split into chunks, pad the last with zeros.
    fn pack_reference(values: &[u8]) -> Vec<Node> {
        values
            .chunks(32)
            .map(|part| {
                let mut chunk = [0u8; 32];
                chunk[..part.len()].copy_from_slice(part);
                chunk
            })
            .collect()
    }

    #[test]
    fn pack_matches_reference() {
        let bytes: Vec<u8> = (0..2100usize).map(|i| (i * 7 + 3) as u8).collect();
        for len in (0..=200).chain([1023, 1024, 1025, 2047, 2048, 2049, 2100]) {
            assert_eq!(
                pack(&bytes[..len]),
                pack_reference(&bytes[..len]),
                "{len} bytes"
            );
        }
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn byte_array_roots_match_pack() {
        fn check<const N: usize>() {
            let mut bytes = [0u8; N];
            for (i, byte) in bytes.iter_mut().enumerate() {
                *byte = (i * 13 + 5) as u8;
            }
            let expected = if N <= 32 {
                let mut node = [0u8; 32];
                node[..N].copy_from_slice(&bytes);
                node
            } else {
                merkleize_fully_materialized(&pack_reference(&bytes), None)
            };
            assert_eq!(bytes.hash_tree_root(&Sha2Hasher), expected, "{N} bytes");
        }
        check::<0>();
        check::<1>();
        check::<31>();
        check::<32>();
        check::<33>();
        check::<48>();
        check::<63>();
        check::<64>();
        check::<65>();
        check::<96>();
        check::<128>();
        check::<224>();
        check::<225>();
        check::<255>();
        check::<256>();
        check::<257>();
        check::<300>();
        check::<1024>();
    }

    /// The root of a list of basic items: the chunks of their serializations, one after
    /// another, and the length mixed in.
    #[cfg(feature = "sha2-backend")]
    fn basic_list_root<T: SszEncode>(items: &[T]) -> Node {
        let mut serialized = Vec::new();
        for item in items {
            serialized.extend_from_slice(&item.to_ssz());
        }
        let mut chunks = pack_reference(&serialized);
        if chunks.is_empty() {
            chunks.push([0u8; 32]);
        }
        let root = merkleize_fully_materialized(&chunks, None);
        mix_in_length(&Sha2Hasher, &root, items.len())
    }

    #[cfg(feature = "sha2-backend")]
    #[test]
    fn vec_of_basic_items_packs_their_serializations() {
        for len in (0..=70usize).chain([255, 256, 257, 1000]) {
            let seed = |i: usize| (i as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let bools: Vec<bool> = (0..len).map(|i| seed(i) >> 60 & 1 == 1).collect();
            assert_eq!(bools.hash_tree_root(&Sha2Hasher), basic_list_root(&bools));
            let u8s: Vec<u8> = (0..len).map(|i| (seed(i) >> 56) as u8).collect();
            assert_eq!(u8s.hash_tree_root(&Sha2Hasher), basic_list_root(&u8s));
            let u16s: Vec<u16> = (0..len).map(|i| (seed(i) >> 48) as u16).collect();
            assert_eq!(u16s.hash_tree_root(&Sha2Hasher), basic_list_root(&u16s));
            let u32s: Vec<u32> = (0..len).map(|i| (seed(i) >> 32) as u32).collect();
            assert_eq!(u32s.hash_tree_root(&Sha2Hasher), basic_list_root(&u32s));
            let u64s: Vec<u64> = (0..len).map(seed).collect();
            assert_eq!(u64s.hash_tree_root(&Sha2Hasher), basic_list_root(&u64s));
            let u128s: Vec<u128> = (0..len)
                .map(|i| (seed(i) as u128) << 64 | seed(i + 7) as u128)
                .collect();
            assert_eq!(u128s.hash_tree_root(&Sha2Hasher), basic_list_root(&u128s));
            let arrays: Vec<[u8; 20]> = (0..len).map(|i| [(seed(i) >> 56) as u8; 20]).collect();
            assert_eq!(arrays.hash_tree_root(&Sha2Hasher), basic_list_root(&arrays));
        }
    }

    /// A hasher that only provides `hash` sees the same sequence of inputs as a tree hashed
    /// level by level, left to right, a level's unpaired node last.
    #[test]
    fn merkleize_hashes_level_by_level_in_order() {
        struct Recorder(core::cell::RefCell<Vec<Vec<u8>>>);
        impl Sha256Hasher for Recorder {
            fn hash(&self, data: &[u8]) -> [u8; 32] {
                self.0.borrow_mut().push(data.to_vec());
                let mut node = [0u8; 32];
                for (i, byte) in data.iter().enumerate() {
                    node[i % 32] = node[i % 32].wrapping_mul(31).wrapping_add(*byte ^ i as u8);
                }
                node
            }
        }
        for n in [2usize, 3, 4, 5, 8, 9, 13, 32, 33, 37, 100] {
            let chunks: Vec<Node> = (0..n).map(|i| [i as u8 + 1; 32]).collect();
            let recorder = Recorder(core::cell::RefCell::new(Vec::new()));
            let root = merkleize(&recorder, &chunks, Some(4 * n));
            let seen = recorder.0.take();

            let reference = Recorder(core::cell::RefCell::new(Vec::new()));
            let mut layer = chunks.clone();
            let mut level = 0;
            while layer.len() > 1 {
                let mut next = Vec::new();
                for pair in layer.chunks(2) {
                    let right = pair.get(1).unwrap_or(&ZERO_HASHES[level]);
                    next.push(reference.hash(&[pair[0], *right].concat()));
                }
                layer = next;
                level += 1;
            }
            let mut expected = layer[0];
            let depth = (4 * n).next_power_of_two().trailing_zeros() as usize;
            for zero_hash in &ZERO_HASHES[level..depth] {
                expected = reference.hash(&[expected, *zero_hash].concat());
            }
            assert_eq!(root, expected, "{n} chunks");
            assert_eq!(seen, reference.0.take(), "{n} chunks");
        }
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
