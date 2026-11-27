//! Byte edits applied to a valid encoding.
//!
//! Starting from a valid encoding keeps most of the structure intact, so
//! the edited bytes get past the first length checks and reach offsets,
//! delimiters, selectors and padding bits. Positions are taken modulo the
//! current length, so every edit applies to every input.
//!
//! [`edited_encodings`] is the generator the decoding properties use. Its
//! values are the edited bytes themselves, and they shrink as bytes (see
//! [`shrink_bytes`]): shrinking the recipe instead would move every offset
//! after the change, so the edits would land somewhere else and the failure
//! would disappear.

use core::fmt::Debug;
use core::ops::ControlFlow;

use ephyra::{any, gens, BoxGen, Gen, GenExt};

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub enum Edit {
    /// Overwrite one byte.
    Set(
        #[ephyra(gen = gens::int(0usize..=4096))] usize,
        #[ephyra(gen = gens::int(0u8..=255))] u8,
    ),
    /// Add a small signed delta to one byte, wrapping. Aimed at offsets and
    /// lengths, where off-by-a-few values are the interesting ones.
    Nudge(
        #[ephyra(gen = gens::int(0usize..=4096))] usize,
        #[ephyra(gen = gens::int(-4i8..=4))] i8,
    ),
    /// Keep only the first `n % (len + 1)` bytes.
    Truncate(#[ephyra(gen = gens::int(0usize..=4096))] usize),
    /// Insert one byte.
    Insert(
        #[ephyra(gen = gens::int(0usize..=4096))] usize,
        #[ephyra(gen = gens::int(0u8..=255))] u8,
    ),
    /// Remove one byte.
    Remove(#[ephyra(gen = gens::int(0usize..=4096))] usize),
}

pub fn apply(mut bytes: Vec<u8>, edits: &[Edit]) -> Vec<u8> {
    for edit in edits {
        match edit {
            Edit::Set(pos, byte) => {
                if !bytes.is_empty() {
                    let i = pos % bytes.len();
                    bytes[i] = *byte;
                }
            }
            Edit::Nudge(pos, delta) => {
                if !bytes.is_empty() {
                    let i = pos % bytes.len();
                    bytes[i] = bytes[i].wrapping_add_signed(*delta);
                }
            }
            Edit::Truncate(n) => {
                let keep = n % (bytes.len() + 1);
                bytes.truncate(keep);
            }
            Edit::Insert(pos, byte) => {
                let i = pos % (bytes.len() + 1);
                bytes.insert(i, *byte);
            }
            Edit::Remove(pos) => {
                if !bytes.is_empty() {
                    let i = pos % bytes.len();
                    bytes.remove(i);
                }
            }
        }
    }
    bytes
}

/// Valid encodings of `recipes`, built with `encode`, with up to four
/// [`Edit`]s applied. Shrinks with [`shrink_bytes`].
pub fn edited_encodings<G>(recipes: G, encode: fn(&G::Value) -> Vec<u8>) -> BoxGen<Vec<u8>>
where
    G: Gen + Send + Sync + 'static,
    G::Value: Clone + Debug + 'static,
{
    (recipes, gens::vec(any::<Edit>()).len(0..=4))
        .map(move |(recipe, edits)| apply(encode(&recipe), &edits))
        .with_shrink(shrink_bytes)
        .boxed()
}

/// The order [`shrink_bytes`] decreases: length first, then the byte sum.
// `&Vec<u8>`, not `&[u8]`: ephyra passes `&Gen::Value`, here `&Vec<u8>`.
#[allow(clippy::ptr_arg)]
pub fn byte_size(bytes: &Vec<u8>) -> u64 {
    let sum: u64 = bytes.iter().map(|b| u64::from(*b)).sum();
    ((bytes.len() as u64) << 32) | sum
}

/// Shrink candidates for a byte string, each strictly smaller by
/// [`byte_size`], most aggressive first:
///
/// 1. remove a range, halving the range size from the largest power of two
///    that fits down to one byte. Each removal is offered twice: first with
///    every earlier 4-byte little-endian word that reads as an offset past
///    the range lowered by the range's length (see [`shift_offsets`]), so a
///    variable field's body can shrink while the container stays valid, then
///    as a plain removal;
/// 2. zero a range, with the same sizes;
/// 3. lower one byte: to 0, to half, by one.
// `&Vec<u8>`, not `&[u8]`: ephyra passes `&Gen::Value`, here `&Vec<u8>`.
#[allow(clippy::ptr_arg)]
pub fn shrink_bytes(
    bytes: &Vec<u8>,
    visit: &mut dyn FnMut(Vec<u8>) -> ControlFlow<()>,
) -> ControlFlow<()> {
    let len = bytes.len();
    if len == 0 {
        return ControlFlow::Continue(());
    }
    let largest = 1usize << (usize::BITS - 1 - len.leading_zeros());

    let mut size = largest;
    while size > 0 {
        let mut start = 0;
        while start < len {
            let end = (start + size).min(len);
            let mut candidate = Vec::with_capacity(len - (end - start));
            candidate.extend_from_slice(&bytes[..start]);
            candidate.extend_from_slice(&bytes[end..]);
            let mut nested = candidate.clone();
            let nested_changed = shift_nested_offsets(&mut nested, start, end - start, len);
            if nested_changed {
                visit(nested.clone())?;
            }
            let mut shifted = candidate.clone();
            if shift_offsets(&mut shifted, start, end - start, len) && shifted != nested {
                visit(shifted)?;
            }
            visit(candidate)?;
            start += size;
        }
        size /= 2;
    }

    let mut size = largest;
    while size > 1 {
        let mut start = 0;
        while start < len {
            let end = (start + size).min(len);
            if bytes[start..end].iter().any(|b| *b != 0) {
                let mut candidate = bytes.clone();
                candidate[start..end].fill(0);
                visit(candidate)?;
            }
            start += size;
        }
        size /= 2;
    }

    for i in 0..len {
        let b = bytes[i];
        if b == 0 {
            continue;
        }
        let mut lowered = vec![0, b / 2, b - 1];
        lowered.dedup();
        for value in lowered {
            if value < b {
                let mut candidate = bytes.clone();
                candidate[i] = value;
                visit(candidate)?;
            }
        }
    }
    ControlFlow::Continue(())
}

/// After removing `removed` bytes at `start` from a string of `old_len`
/// bytes, lower by `removed` every 4-byte little-endian word before `start`
/// whose value points at or past the end of the removed range and inside
/// the old string, the way a top-level SSZ offset would. Returns whether any word changed.
///
/// Words are tried at every position, so fixed fields can be mistaken for
/// offsets; such candidates simply fail to reproduce and are dropped. Offsets
/// of nested containers are relative to the nested start and are not
/// adjusted.
pub fn shift_offsets(bytes: &mut [u8], start: usize, removed: usize, old_len: usize) -> bool {
    let mut changed = false;
    let mut p = 0;
    while p + 4 <= start {
        let word = u32::from_le_bytes([bytes[p], bytes[p + 1], bytes[p + 2], bytes[p + 3]]);
        let value = word as usize;
        // Offsets pointing at or past the end of the removed range move
        // down with it; that also keeps `value - removed` from underflowing.
        if value >= start + removed && value <= old_len {
            let lowered = (value - removed) as u32;
            bytes[p..p + 4].copy_from_slice(&lowered.to_le_bytes());
            changed = true;
            p += 4;
        } else {
            p += 1;
        }
    }
    changed
}

/// Like [`shift_offsets`], but for offsets relative to a nested container
/// too. Scanning left to right, a word at `p` is taken as an offset relative
/// to the latest known container start `base <= p` when `base + value` lands
/// after `p` and inside the string; that target becomes a known container
/// start in turn. Offsets whose target is at or past the end of the removed
/// range are lowered by `removed`.
pub fn shift_nested_offsets(
    bytes: &mut [u8],
    start: usize,
    removed: usize,
    old_len: usize,
) -> bool {
    let mut bases: Vec<usize> = vec![0];
    let mut changed = false;
    let mut p = 0;
    while p + 4 <= start {
        let word = u32::from_le_bytes([bytes[p], bytes[p + 1], bytes[p + 2], bytes[p + 3]]);
        let value = word as usize;
        let base = bases.iter().copied().filter(|b| *b <= p).max().unwrap_or(0);
        let target = base + value;
        if value >= 4 && target > p + 3 && target <= old_len {
            // `target >= start + removed` and `base <= start` give
            // `value >= removed`, so this cannot underflow.
            if target >= start + removed {
                let lowered = (value - removed) as u32;
                bytes[p..p + 4].copy_from_slice(&lowered.to_le_bytes());
                changed = true;
            }
            if !bases.contains(&target) {
                bases.push(target);
            }
            p += 4;
        } else {
            p += 1;
        }
    }
    changed
}
