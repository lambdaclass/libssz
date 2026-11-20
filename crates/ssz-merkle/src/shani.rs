//! SHA-256 of two 32-byte nodes on the x86 SHA extensions, up to four pairs at a time.
//!
//! A message of 64 bytes is two blocks: the two nodes, then a padding block that is the
//! same for every pair. `PAD_WK` holds that block's schedule already added to the round
//! constants, so the second compression computes no schedule.
//!
//! One `sha256rnds2` takes four cycles to give its result, but a core can start a new one
//! every cycle (measured on an AMD Zen 3+: one chain, 4 cycles per instruction; two, 2;
//! four, 1). [`hash_pairs_x2`] and [`hash_pairs_x4`] interleave two and four independent
//! pairs, so that the processor works on one while it waits for the others. That holds
//! only while the chains stay interleaved in the machine code. Their loops therefore run
//! sixteen rounds of each pair per turn, with bounds the compiler cannot see: unrolled
//! into a single block, the compiler puts one pair's rounds after the other's, too far
//! apart for the processor to overlap them, and the pairs take the time of two or four.
//!
//! Four pairs do not take the time of one: SSE has sixteen vector registers and four
//! pairs need more, so part of the state goes to the stack. Measured, a hash costs about
//! 10% less with [`hash_pairs_x4`] than with [`hash_pairs_x2`].
//!
//! Vectors are named by their lanes from the top one down, as Intel's documentation names
//! them: `_mm_sha256rnds2_epu32` keeps the state as ABEF and CDGH.
//!
//! The code is written to be translated by Aeneas, after the `crypto_simd` crate of
//! gattaca-com/silver: `while` loops, and only intrinsics that take and return values, so
//! there is no raw pointer and no `unsafe` here. The caller checks [`available`].

use core::arch::x86_64::{
    __m128i, _mm_add_epi32, _mm_alignr_epi8, _mm_extract_epi32, _mm_set_epi32,
    _mm_sha256msg1_epu32, _mm_sha256msg2_epu32, _mm_sha256rnds2_epu32, _mm_shuffle_epi32,
};

use crate::Node;

/// The round constants of FIPS 180-4 §4.2.2, four to a row.
const K: [[u32; 4]; 16] = [
    [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5],
    [0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5],
    [0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3],
    [0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174],
    [0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc],
    [0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da],
    [0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7],
    [0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967],
    [0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13],
    [0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85],
    [0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3],
    [0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070],
    [0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5],
    [0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3],
    [0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208],
    [0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2],
];

/// `W[t] + K[t]` for the second block of every 64-byte message: the byte `0x80`, zeros,
/// and the bit length 512.
const PAD_WK: [[u32; 4]; 16] = [
    [0xc28a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5],
    [0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5],
    [0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3],
    [0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf374],
    [0x649b69c1, 0xf0fe4786, 0x0fe1edc6, 0x240cf254],
    [0x4fe9346f, 0x6cc984be, 0x61b9411e, 0x16f988fa],
    [0xf2c65152, 0xa88e5a6d, 0xb019fc65, 0xb9d99ec7],
    [0x9a1231c3, 0xe70eeaa0, 0xfdb1232b, 0xc7353eb0],
    [0x3069bad5, 0xcb976d5f, 0x5a0f118f, 0xdc1eeefd],
    [0x0a35b689, 0xde0b7a04, 0x58f4ca9d, 0xe15d5b16],
    [0x007f3e86, 0x37088980, 0xa507ea32, 0x6fab9537],
    [0x17406110, 0x0d8cd6f1, 0xcdaa3b6d, 0xc0bbbe37],
    [0x83613bda, 0xdb48a363, 0x0b02e931, 0x6fd15ca7],
    [0x521afaca, 0x31338431, 0x6ed41a95, 0x6d437890],
    [0xc39c91f2, 0x9eccabbd, 0xb5c9a0e6, 0x532fb63c],
    [0xd2c741c6, 0x07237ea3, 0xa4954b68, 0x4c191d76],
];

/// Whether this CPU runs the kernel.
pub(crate) fn available() -> bool {
    is_x86_feature_detected!("sha")
        && is_x86_feature_detected!("sse2")
        && is_x86_feature_detected!("ssse3")
        && is_x86_feature_detected!("sse4.1")
}

/// The working variables and sixteen consecutive words of the schedule, four to a vector,
/// the earliest in the low lane of `w0`.
struct Stream {
    abef: __m128i,
    cdgh: __m128i,
    w0: __m128i,
    w1: __m128i,
    w2: __m128i,
    w3: __m128i,
}

/// Four words as one vector, the last argument in the low lane.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn words(w3: u32, w2: u32, w1: u32, w0: u32) -> __m128i {
    _mm_set_epi32(w3 as i32, w2 as i32, w1 as i32, w0 as i32)
}

/// A row of four words as one vector, the first in the low lane.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn row(r: &[u32; 4]) -> __m128i {
    words(r[3], r[2], r[1], r[0])
}

/// The big-endian word at bytes `at` to `at + 3`.
#[inline]
fn be_word(d: &Node, at: usize) -> u32 {
    u32::from_be_bytes([d[at], d[at + 1], d[at + 2], d[at + 3]])
}

/// The four big-endian words at bytes `at` to `at + 15`, the first in the low lane.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn be_words(d: &Node, at: usize) -> __m128i {
    words(
        be_word(d, at + 12),
        be_word(d, at + 8),
        be_word(d, at + 4),
        be_word(d, at),
    )
}

/// The initial hash value and the sixteen words of the block `a ‖ b`.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn start(a: &Node, b: &Node) -> Stream {
    Stream {
        abef: words(0x6a09e667, 0xbb67ae85, 0x510e527f, 0x9b05688c),
        cdgh: words(0x3c6ef372, 0xa54ff53a, 0x1f83d9ab, 0x5be0cd19),
        w0: be_words(a, 0),
        w1: be_words(a, 16),
        w2: be_words(b, 0),
        w3: be_words(b, 16),
    }
}

/// Four rounds, with `wk` the sums of their words and constants.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn four_rounds(abef: __m128i, cdgh: __m128i, wk: __m128i) -> (__m128i, __m128i) {
    let cdgh = _mm_sha256rnds2_epu32(cdgh, abef, wk);
    let abef = _mm_sha256rnds2_epu32(abef, cdgh, _mm_shuffle_epi32(wk, 0x0e));
    (abef, cdgh)
}

/// Rounds `4 * quad` to `4 * quad + 3`, and the schedule moved four words on.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn scheduled_quad(s: &Stream, quad: usize) -> Stream {
    let (abef, cdgh) = four_rounds(s.abef, s.cdgh, _mm_add_epi32(s.w0, row(&K[quad])));
    let partial = _mm_sha256msg1_epu32(s.w0, s.w1);
    let next = _mm_sha256msg2_epu32(_mm_add_epi32(partial, _mm_alignr_epi8(s.w3, s.w2, 4)), s.w3);
    Stream {
        abef,
        cdgh,
        w0: s.w1,
        w1: s.w2,
        w2: s.w3,
        w3: next,
    }
}

/// Rounds 48 to 63, whose sixteen words the stream already holds, and the first block's
/// hash value: the initial one plus the working variables.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn finish_block(s: &Stream) -> (__m128i, __m128i) {
    let (abef, cdgh) = four_rounds(s.abef, s.cdgh, _mm_add_epi32(s.w0, row(&K[12])));
    let (abef, cdgh) = four_rounds(abef, cdgh, _mm_add_epi32(s.w1, row(&K[13])));
    let (abef, cdgh) = four_rounds(abef, cdgh, _mm_add_epi32(s.w2, row(&K[14])));
    let (abef, cdgh) = four_rounds(abef, cdgh, _mm_add_epi32(s.w3, row(&K[15])));
    (
        _mm_add_epi32(abef, words(0x6a09e667, 0xbb67ae85, 0x510e527f, 0x9b05688c)),
        _mm_add_epi32(cdgh, words(0x3c6ef372, 0xa54ff53a, 0x1f83d9ab, 0x5be0cd19)),
    )
}

/// The digest: the hash value `abef0`, `cdgh0` plus the working variables, big-endian.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn digest(abef0: __m128i, cdgh0: __m128i, abef: __m128i, cdgh: __m128i) -> Node {
    let abef = _mm_add_epi32(abef, abef0);
    let cdgh = _mm_add_epi32(cdgh, cdgh0);
    let a = (_mm_extract_epi32(abef, 3) as u32).to_be_bytes();
    let b = (_mm_extract_epi32(abef, 2) as u32).to_be_bytes();
    let c = (_mm_extract_epi32(cdgh, 3) as u32).to_be_bytes();
    let d = (_mm_extract_epi32(cdgh, 2) as u32).to_be_bytes();
    let e = (_mm_extract_epi32(abef, 1) as u32).to_be_bytes();
    let f = (_mm_extract_epi32(abef, 0) as u32).to_be_bytes();
    let g = (_mm_extract_epi32(cdgh, 1) as u32).to_be_bytes();
    let h = (_mm_extract_epi32(cdgh, 0) as u32).to_be_bytes();
    [
        a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3], c[0], c[1], c[2], c[3], d[0], d[1], d[2],
        d[3], e[0], e[1], e[2], e[3], f[0], f[1], f[2], f[3], g[0], g[1], g[2], g[3], h[0], h[1],
        h[2], h[3],
    ]
}

/// SHA-256 of `a ‖ b`.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
pub(crate) fn hash_pair(a: &Node, b: &Node) -> Node {
    let mut s = start(a, b);
    let mut quad = 0;
    while quad < 12 {
        s = scheduled_quad(&s, quad);
        quad += 1;
    }
    let (abef0, cdgh0) = finish_block(&s);
    let (mut abef, mut cdgh) = (abef0, cdgh0);
    let mut quad = 0;
    while quad < 16 {
        (abef, cdgh) = four_rounds(abef, cdgh, row(&PAD_WK[quad]));
        quad += 1;
    }
    digest(abef0, cdgh0, abef, cdgh)
}

/// SHA-256 of `a0 ‖ b0` and of `a1 ‖ b1`, the two computed in step.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
pub(crate) fn hash_pairs_x2(a0: &Node, b0: &Node, a1: &Node, b1: &Node) -> (Node, Node) {
    // How many turns of sixteen rounds each loop takes. The values are hidden from the
    // compiler so that it keeps the loops: see the module documentation.
    let scheduled = core::hint::black_box(3);
    let padded = core::hint::black_box(4);
    let mut s0 = start(a0, b0);
    let mut s1 = start(a1, b1);
    let mut turn = 0;
    while turn < scheduled {
        s0 = scheduled_quad(&s0, 4 * turn);
        s1 = scheduled_quad(&s1, 4 * turn);
        s0 = scheduled_quad(&s0, 4 * turn + 1);
        s1 = scheduled_quad(&s1, 4 * turn + 1);
        s0 = scheduled_quad(&s0, 4 * turn + 2);
        s1 = scheduled_quad(&s1, 4 * turn + 2);
        s0 = scheduled_quad(&s0, 4 * turn + 3);
        s1 = scheduled_quad(&s1, 4 * turn + 3);
        turn += 1;
    }
    let (abef00, cdgh00) = finish_block(&s0);
    let (abef10, cdgh10) = finish_block(&s1);
    let (mut abef0, mut cdgh0) = (abef00, cdgh00);
    let (mut abef1, mut cdgh1) = (abef10, cdgh10);
    let mut turn = 0;
    while turn < padded {
        let wk = row(&PAD_WK[4 * turn]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        let wk = row(&PAD_WK[4 * turn + 1]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        let wk = row(&PAD_WK[4 * turn + 2]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        let wk = row(&PAD_WK[4 * turn + 3]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        turn += 1;
    }
    (
        digest(abef00, cdgh00, abef0, cdgh0),
        digest(abef10, cdgh10, abef1, cdgh1),
    )
}

/// SHA-256 of `a0 ‖ b0`, `a1 ‖ b1`, `a2 ‖ b2` and `a3 ‖ b3`, the four computed in step.
#[inline]
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
#[allow(clippy::too_many_arguments)]
pub(crate) fn hash_pairs_x4(
    a0: &Node,
    b0: &Node,
    a1: &Node,
    b1: &Node,
    a2: &Node,
    b2: &Node,
    a3: &Node,
    b3: &Node,
) -> (Node, Node, Node, Node) {
    // How many turns of sixteen rounds each loop takes. The values are hidden from the
    // compiler so that it keeps the loops: see the module documentation.
    let scheduled = core::hint::black_box(3);
    let padded = core::hint::black_box(4);
    let mut s0 = start(a0, b0);
    let mut s1 = start(a1, b1);
    let mut s2 = start(a2, b2);
    let mut s3 = start(a3, b3);
    let mut turn = 0;
    while turn < scheduled {
        s0 = scheduled_quad(&s0, 4 * turn);
        s1 = scheduled_quad(&s1, 4 * turn);
        s2 = scheduled_quad(&s2, 4 * turn);
        s3 = scheduled_quad(&s3, 4 * turn);
        s0 = scheduled_quad(&s0, 4 * turn + 1);
        s1 = scheduled_quad(&s1, 4 * turn + 1);
        s2 = scheduled_quad(&s2, 4 * turn + 1);
        s3 = scheduled_quad(&s3, 4 * turn + 1);
        s0 = scheduled_quad(&s0, 4 * turn + 2);
        s1 = scheduled_quad(&s1, 4 * turn + 2);
        s2 = scheduled_quad(&s2, 4 * turn + 2);
        s3 = scheduled_quad(&s3, 4 * turn + 2);
        s0 = scheduled_quad(&s0, 4 * turn + 3);
        s1 = scheduled_quad(&s1, 4 * turn + 3);
        s2 = scheduled_quad(&s2, 4 * turn + 3);
        s3 = scheduled_quad(&s3, 4 * turn + 3);
        turn += 1;
    }
    let (abef00, cdgh00) = finish_block(&s0);
    let (abef10, cdgh10) = finish_block(&s1);
    let (abef20, cdgh20) = finish_block(&s2);
    let (abef30, cdgh30) = finish_block(&s3);
    let (mut abef0, mut cdgh0) = (abef00, cdgh00);
    let (mut abef1, mut cdgh1) = (abef10, cdgh10);
    let (mut abef2, mut cdgh2) = (abef20, cdgh20);
    let (mut abef3, mut cdgh3) = (abef30, cdgh30);
    let mut turn = 0;
    while turn < padded {
        let wk = row(&PAD_WK[4 * turn]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        (abef2, cdgh2) = four_rounds(abef2, cdgh2, wk);
        (abef3, cdgh3) = four_rounds(abef3, cdgh3, wk);
        let wk = row(&PAD_WK[4 * turn + 1]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        (abef2, cdgh2) = four_rounds(abef2, cdgh2, wk);
        (abef3, cdgh3) = four_rounds(abef3, cdgh3, wk);
        let wk = row(&PAD_WK[4 * turn + 2]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        (abef2, cdgh2) = four_rounds(abef2, cdgh2, wk);
        (abef3, cdgh3) = four_rounds(abef3, cdgh3, wk);
        let wk = row(&PAD_WK[4 * turn + 3]);
        (abef0, cdgh0) = four_rounds(abef0, cdgh0, wk);
        (abef1, cdgh1) = four_rounds(abef1, cdgh1, wk);
        (abef2, cdgh2) = four_rounds(abef2, cdgh2, wk);
        (abef3, cdgh3) = four_rounds(abef3, cdgh3, wk);
        turn += 1;
    }
    (
        digest(abef00, cdgh00, abef0, cdgh0),
        digest(abef10, cdgh10, abef1, cdgh1),
        digest(abef20, cdgh20, abef2, cdgh2),
        digest(abef30, cdgh30, abef3, cdgh3),
    )
}

/// The right sibling of `nodes[2 * k]`: the node after it, or `zero_hash` when it is the
/// last one.
#[inline]
fn sibling<'a>(nodes: &'a [Node], k: usize, zero_hash: &'a Node) -> &'a Node {
    if 2 * k + 1 < nodes.len() {
        &nodes[2 * k + 1]
    } else {
        zero_hash
    }
}

/// The nodes a level is hashed from: `below`, or the ones in `level` itself when the level
/// is hashed in place.
#[inline]
fn source<'a>(in_place: bool, below: &'a [Node], level: &'a [Node]) -> &'a [Node] {
    if in_place {
        level
    } else {
        below
    }
}

/// One level of a Merkle tree, from the nodes of [`source`]: writes the hash of
/// `nodes[2 * k]` and its [`sibling`] to `level[k]`. That is `nodes.len().div_ceil(2)`
/// nodes; the rest of `level` is left as it was.
///
/// With `in_place`, `below` is not read and the level is written over the nodes it is
/// hashed from. Every one is read before the write that replaces it: a turn reads from
/// `2 * k` on and writes below `k + 4`, which is at most `2 * k + 4`.
///
/// Four parents at a time while there are four, then two, then one.
///
/// # Panics
///
/// If `level` is shorter than what is written.
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
pub(crate) fn hash_layer(below: &[Node], level: &mut [Node], in_place: bool, zero_hash: &Node) {
    let len = source(in_place, below, level).len();
    let total = len / 2 + len % 2;
    let mut k = 0;
    while total - k >= 4 {
        let nodes = source(in_place, below, level);
        let (x, y, z, w) = hash_pairs_x4(
            &nodes[2 * k],
            &nodes[2 * k + 1],
            &nodes[2 * k + 2],
            &nodes[2 * k + 3],
            &nodes[2 * k + 4],
            &nodes[2 * k + 5],
            &nodes[2 * k + 6],
            sibling(nodes, k + 3, zero_hash),
        );
        level[k] = x;
        level[k + 1] = y;
        level[k + 2] = z;
        level[k + 3] = w;
        k += 4;
    }
    if total - k >= 2 {
        let nodes = source(in_place, below, level);
        let (x, y) = hash_pairs_x2(
            &nodes[2 * k],
            &nodes[2 * k + 1],
            &nodes[2 * k + 2],
            sibling(nodes, k + 1, zero_hash),
        );
        level[k] = x;
        level[k + 1] = y;
        k += 2;
    }
    if total - k == 1 {
        let nodes = source(in_place, below, level);
        let x = hash_pair(&nodes[2 * k], sibling(nodes, k, zero_hash));
        level[k] = x;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{merkleize, merkleize_in_place, Sha256Hasher, Sha2Hasher, ZERO_HASHES};
    use sha2::{Digest, Sha256};

    /// The `sha2` crate alone: the trait's provided methods, with no kernel.
    struct Plain;

    impl Sha256Hasher for Plain {
        fn hash(&self, data: &[u8]) -> [u8; 32] {
            Sha256::digest(data).into()
        }
    }

    fn nodes(count: usize, mut seed: u64) -> Vec<Node> {
        let mut out = Vec::with_capacity(count);
        for _ in 0..count {
            let mut node = [0u8; 32];
            for part in node.chunks_mut(8) {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                part.copy_from_slice(&seed.to_le_bytes());
            }
            out.push(node);
        }
        out
    }

    /// Nodes that put each byte value, and a lone set bit, at each position of the block.
    fn edge_nodes() -> Vec<Node> {
        let mut out = vec![[0u8; 32], [0xff; 32], [0x80; 32], [0x7f; 32]];
        for at in 0..32 {
            let mut node = [0u8; 32];
            node[at] = 0x80;
            out.push(node);
            node[at] = 0x01;
            out.push(node);
            let mut node = [0xff; 32];
            node[at] = 0;
            out.push(node);
        }
        out
    }

    #[test]
    fn two_zero_nodes() {
        assert!(
            available(),
            "this CPU lacks the SHA extensions: the kernel is not tested"
        );
        let zero = [0u8; 32];
        assert_eq!(unsafe { hash_pair(&zero, &zero) }, ZERO_HASHES[1]);
    }

    #[test]
    fn hash_pair_is_sha256() {
        assert!(available());
        let mut all = edge_nodes();
        all.extend(nodes(4096, 0x9e37_79b9_7f4a_7c15));
        for pair in all.as_chunks::<2>().0 {
            assert_eq!(
                unsafe { hash_pair(&pair[0], &pair[1]) },
                Plain.hash_pair(&pair[0], &pair[1])
            );
            assert_eq!(
                unsafe { hash_pair(&pair[1], &pair[0]) },
                Plain.hash_pair(&pair[1], &pair[0])
            );
        }
        let edges = edge_nodes();
        for a in &edges {
            for b in &edges {
                assert_eq!(unsafe { hash_pair(a, b) }, Plain.hash_pair(a, b));
            }
        }
    }

    #[test]
    fn hash_pairs_x2_is_two_hash_pairs() {
        assert!(available());
        let mut all = edge_nodes();
        all.extend(nodes(4096, 0x0123_4567_89ab_cdef));
        for four in all.as_chunks::<4>().0 {
            let (x, y) = unsafe { hash_pairs_x2(&four[0], &four[1], &four[2], &four[3]) };
            assert_eq!(x, Plain.hash_pair(&four[0], &four[1]));
            assert_eq!(y, Plain.hash_pair(&four[2], &four[3]));
        }
    }

    #[test]
    fn hash_pairs_x4_is_four_hash_pairs() {
        assert!(available());
        let mut all = edge_nodes();
        all.extend(nodes(4096, 0x0f1e_2d3c_4b5a_6978));
        for e in all.as_chunks::<8>().0 {
            let (x, y, z, w) =
                unsafe { hash_pairs_x4(&e[0], &e[1], &e[2], &e[3], &e[4], &e[5], &e[6], &e[7]) };
            assert_eq!(x, Plain.hash_pair(&e[0], &e[1]));
            assert_eq!(y, Plain.hash_pair(&e[2], &e[3]));
            assert_eq!(z, Plain.hash_pair(&e[4], &e[5]));
            assert_eq!(w, Plain.hash_pair(&e[6], &e[7]));
        }
    }

    #[test]
    fn hash_layer_is_the_plain_level() {
        assert!(available());
        let all = nodes(131, 0xdead_beef_cafe_f00d);
        let zero_hash = ZERO_HASHES[5];
        for len in 0..=all.len() {
            let level = len.div_ceil(2);
            for spare in [0, 1, 3] {
                let mut got = vec![[0xaa; 32]; level + spare];
                let mut want = got.clone();
                unsafe { hash_layer(&all[..len], &mut got, false, &zero_hash) };
                Plain.hash_layer(&all[..len], &mut want, &zero_hash);
                assert_eq!(got, want, "{len} nodes, {spare} spare");
                for (k, pair) in all[..len].chunks(2).enumerate() {
                    let right = pair.get(1).unwrap_or(&zero_hash);
                    assert_eq!(got[k], Plain.hash_pair(&pair[0], right));
                }
                assert!(got[level..].iter().all(|node| *node == [0xaa; 32]));
            }

            let mut got = all[..len].to_vec();
            let mut want = got.clone();
            unsafe { hash_layer(&[], &mut got, true, &zero_hash) };
            Plain.hash_layer_in_place(&mut want, &zero_hash);
            assert_eq!(got, want, "{len} nodes, in place");
            for (k, pair) in all[..len].chunks(2).enumerate() {
                let right = pair.get(1).unwrap_or(&zero_hash);
                assert_eq!(got[k], Plain.hash_pair(&pair[0], right));
            }
            assert_eq!(got[level..], all[level..len]);
        }
    }

    #[test]
    #[should_panic]
    fn hash_layer_panics_on_a_short_output() {
        assert!(available());
        let all = nodes(7, 1);
        let mut out = vec![[0u8; 32]; 3];
        unsafe { hash_layer(&all, &mut out, false, &ZERO_HASHES[0]) };
    }

    #[test]
    fn merkleize_agrees_with_the_sha2_crate() {
        assert!(available());
        let all = nodes(1100, 0x1357_9bdf_0246_8ace);
        for len in (0..=140).chain([255, 256, 257, 511, 512, 513, 1023, 1024, 1025, 1100]) {
            let chunks = &all[..len];
            for limit in [
                None,
                Some(len),
                Some(len + 1),
                Some(4 * len + 3),
                Some(1 << 20),
            ] {
                let want = merkleize(&Plain, chunks, limit);
                assert_eq!(
                    merkleize(&Sha2Hasher, chunks, limit),
                    want,
                    "{len} chunks, limit {limit:?}"
                );
                assert_eq!(
                    merkleize_in_place(&Sha2Hasher, &mut chunks.to_vec(), limit),
                    want,
                    "{len} chunks, limit {limit:?}, in place"
                );
            }
        }
    }
}
