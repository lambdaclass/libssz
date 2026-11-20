#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use crate::BYTES_PER_LENGTH_OFFSET;

/// Trait for SSZ-encodable types.
///
/// Encoding is infallible — all validation happens at construction time.
pub trait SszEncode {
    /// Returns `true` if this type has a fixed SSZ size.
    fn is_fixed_size() -> bool;

    /// Returns the fixed size in bytes. Only meaningful when `is_fixed_size()` is `true`.
    fn fixed_size() -> usize;

    /// Returns the encoded length in bytes for this value.
    fn encoded_len(&self) -> usize;

    /// Appends the SSZ encoding of `self` to `buf`.
    fn ssz_append(&self, buf: &mut Vec<u8>);

    /// Returns the SSZ encoding as a new `Vec<u8>`.
    #[cfg(feature = "alloc")]
    fn to_ssz(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.encoded_len());
        self.ssz_append(&mut buf);
        buf
    }

    /// Bulk-append a slice of fixed-size items to `buf`.
    ///
    /// The default loops over items. Integer types override this with a single
    /// memcpy on little-endian platforms.
    #[cfg(feature = "alloc")]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>)
    where
        Self: Sized,
    {
        buf.reserve(Self::fixed_size() * items.len());
        let mut i = 0;
        while i < items.len() {
            items[i].ssz_append(buf);
            i += 1;
        }
    }

    /// Returns `true` if the type is fixed-size and overrides [`ssz_write_fixed`]
    /// with a direct write (no temporary buffer).
    ///
    /// Containers use it to pick the direct-write path; types that return `false`
    /// (the default) are encoded through `ssz_append`, as before.
    ///
    /// [`ssz_write_fixed`]: SszEncode::ssz_write_fixed
    #[doc(hidden)]
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        false
    }

    /// Writes the SSZ encoding of a fixed-size value into `out`.
    ///
    /// `out.len()` must be exactly `Self::fixed_size()`. Only meaningful when
    /// `is_fixed_size()` is `true`. The default goes through a temporary buffer;
    /// types that override it should also return `true` from
    /// [`ssz_has_write_fixed`](SszEncode::ssz_has_write_fixed).
    #[doc(hidden)]
    #[cfg(feature = "alloc")]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        let mut tmp = Vec::with_capacity(out.len());
        self.ssz_append(&mut tmp);
        out.copy_from_slice(&tmp);
    }

    /// Returns the concatenated encodings of a slice of fixed-size items as a new
    /// `Vec<u8>`: what `to_ssz` of a list of them returns.
    ///
    /// The default allocates the exact size and calls `ssz_append_fixed_slice`.
    #[doc(hidden)]
    #[cfg(feature = "alloc")]
    fn ssz_fixed_slice_to_vec(items: &[Self]) -> Vec<u8>
    where
        Self: Sized,
    {
        let mut buf = Vec::with_capacity(Self::fixed_size() * items.len());
        Self::ssz_append_fixed_slice(items, &mut buf);
        buf
    }
}

/// Bytes `append_le_blocks!` moves through the stack in each batch (two pages: together
/// with the batch's source and destination it fits in the L1 cache).
#[cfg(feature = "alloc")]
const BLOCK_BYTES: usize = 8192;

/// `ssz_append_fixed_slice` for the integers wider than one byte.
///
/// The list's encoding is the little-endian bytes of each item, one after the other.
/// Without `unsafe` a `&[u64]` cannot be viewed as a `&[u8]`, so the items go through a
/// `[[u8; W]; B]` block on the stack (of `BLOCK_BYTES`, it fits in the L1 cache) and from
/// there into the buffer with `extend_from_slice`. On little-endian the compiler
/// recognizes both copies as `memcpy`s and fuses them into one, from the items to the
/// buffer.
///
/// The shape matters: `as_chunks` for the full batches (constant length, no bounds
/// checks) and the remainder separately. With a single loop over variable-length batches
/// the compiler does not reach the `memcpy`.
#[cfg(feature = "alloc")]
macro_rules! append_le_blocks {
    ($items:ident, $buf:ident, $w:literal) => {{
        const B: usize = BLOCK_BYTES / $w;
        $buf.reserve($w * $items.len());
        let (blocks, rest) = $items.as_chunks::<B>();
        let mut tmp = [[0u8; $w]; B];
        let mut i = 0;
        while i < blocks.len() {
            let block = &blocks[i];
            let mut k = 0;
            while k < B {
                tmp[k] = block[k].to_le_bytes();
                k += 1;
            }
            $buf.extend_from_slice(tmp.as_flattened());
            i += 1;
        }
        let m = rest.len();
        if m > 0 {
            let out = &mut tmp[..m];
            let mut k = 0;
            while k < m {
                out[k] = rest[k].to_le_bytes();
                k += 1;
            }
            $buf.extend_from_slice(out.as_flattened());
        }
    }};
}

/// Like the remainder in `append_le_blocks!`, for lists shorter than one batch: without
/// the upfront `reserve` or the batch loop, which with a hundred items cost as much as the
/// copy itself.
#[cfg(feature = "alloc")]
macro_rules! append_le_short {
    ($items:ident, $buf:ident, $w:literal) => {{
        const B: usize = BLOCK_BYTES / $w;
        let m = $items.len();
        // Without this `if` the two copies are not fused: with the empty list the first
        // one does not run and the second one does.
        if m > 0 {
            let mut tmp = [[0u8; $w]; B];
            let out = &mut tmp[..m];
            let mut k = 0;
            while k < m {
                out[k] = $items[k].to_le_bytes();
                k += 1;
            }
            $buf.extend_from_slice(out.as_flattened());
        }
    }};
}

// The functions below are `inline(never)`: they rely on the compiler seeing `items`
// and `buf` as non-overlapping parameters. Inlined into another function they lose
// that fact and, with it, the `memcpy`.

#[cfg(feature = "alloc")]
#[inline(never)]
fn u16s_append_le_short(items: &[u16], buf: &mut Vec<u8>) {
    append_le_short!(items, buf, 2);
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u16s_append_le_blocks(items: &[u16], buf: &mut Vec<u8>) {
    append_le_blocks!(items, buf, 2);
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u32s_append_le_short(items: &[u32], buf: &mut Vec<u8>) {
    append_le_short!(items, buf, 4);
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u32s_append_le_blocks(items: &[u32], buf: &mut Vec<u8>) {
    append_le_blocks!(items, buf, 4);
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u64s_append_le_short(items: &[u64], buf: &mut Vec<u8>) {
    append_le_short!(items, buf, 8);
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u64s_append_le_blocks(items: &[u64], buf: &mut Vec<u8>) {
    append_le_blocks!(items, buf, 8);
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u128s_append_le_short(items: &[u128], buf: &mut Vec<u8>) {
    append_le_short!(items, buf, 16);
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u128s_append_le_blocks(items: &[u128], buf: &mut Vec<u8>) {
    append_le_blocks!(items, buf, 16);
}

// ── bool ──

impl SszEncode for bool {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        1
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        1
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.push(*self as u8);
    }
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        true
    }
    #[cfg(feature = "alloc")]
    #[inline(always)]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        out.copy_from_slice(&[*self as u8]);
    }
    #[cfg(feature = "alloc")]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        buf.reserve(items.len());
        let mut i = 0;
        while i < items.len() {
            items[i].ssz_append(buf);
            i += 1;
        }
    }
}

// ── Unsigned integers ──

impl SszEncode for u8 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        1
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        1
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }
    #[cfg(feature = "alloc")]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        // One byte per item: the list's encoding is the list itself (a `memcpy`).
        buf.extend_from_slice(items);
    }
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        true
    }
    #[cfg(feature = "alloc")]
    #[inline(always)]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        out.copy_from_slice(&self.to_le_bytes());
    }
}

impl SszEncode for u16 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        2
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        2
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }
    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        if items.len() < BLOCK_BYTES / 2 {
            u16s_append_le_short(items, buf);
        } else {
            u16s_append_le_blocks(items, buf);
        }
    }
    #[cfg(feature = "alloc")]
    fn ssz_fixed_slice_to_vec(items: &[Self]) -> Vec<u8> {
        // A `Vec<[u8; 2]>` of the exact length, which `into_flattened` turns into a
        // `Vec<u8>` without copying. The `collect` writes to fresh memory: a `memcpy`.
        items
            .iter()
            .map(|x| x.to_le_bytes())
            .collect::<Vec<[u8; 2]>>()
            .into_flattened()
    }
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        true
    }
    #[cfg(feature = "alloc")]
    #[inline(always)]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        out.copy_from_slice(&self.to_le_bytes());
    }
}

impl SszEncode for u32 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        4
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        4
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }
    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        if items.len() < BLOCK_BYTES / 4 {
            u32s_append_le_short(items, buf);
        } else {
            u32s_append_le_blocks(items, buf);
        }
    }
    #[cfg(feature = "alloc")]
    fn ssz_fixed_slice_to_vec(items: &[Self]) -> Vec<u8> {
        // A `Vec<[u8; 4]>` of the exact length, which `into_flattened` turns into a
        // `Vec<u8>` without copying. The `collect` writes to fresh memory: a `memcpy`.
        items
            .iter()
            .map(|x| x.to_le_bytes())
            .collect::<Vec<[u8; 4]>>()
            .into_flattened()
    }
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        true
    }
    #[cfg(feature = "alloc")]
    #[inline(always)]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        out.copy_from_slice(&self.to_le_bytes());
    }
}

impl SszEncode for u64 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        8
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        8
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }
    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        if items.len() < BLOCK_BYTES / 8 {
            u64s_append_le_short(items, buf);
        } else {
            u64s_append_le_blocks(items, buf);
        }
    }
    #[cfg(feature = "alloc")]
    fn ssz_fixed_slice_to_vec(items: &[Self]) -> Vec<u8> {
        // A `Vec<[u8; 8]>` of the exact length, which `into_flattened` turns into a
        // `Vec<u8>` without copying. The `collect` writes to fresh memory: a `memcpy`.
        items
            .iter()
            .map(|x| x.to_le_bytes())
            .collect::<Vec<[u8; 8]>>()
            .into_flattened()
    }
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        true
    }
    #[cfg(feature = "alloc")]
    #[inline(always)]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        out.copy_from_slice(&self.to_le_bytes());
    }
}

impl SszEncode for u128 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        16
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        16
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.to_le_bytes());
    }
    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        if items.len() < BLOCK_BYTES / 16 {
            u128s_append_le_short(items, buf);
        } else {
            u128s_append_le_blocks(items, buf);
        }
    }
    #[cfg(feature = "alloc")]
    fn ssz_fixed_slice_to_vec(items: &[Self]) -> Vec<u8> {
        // A `Vec<[u8; 16]>` of the exact length, which `into_flattened` turns into a
        // `Vec<u8>` without copying. The `collect` writes to fresh memory: a `memcpy`.
        items
            .iter()
            .map(|x| x.to_le_bytes())
            .collect::<Vec<[u8; 16]>>()
            .into_flattened()
    }
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        true
    }
    #[cfg(feature = "alloc")]
    #[inline(always)]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        out.copy_from_slice(&self.to_le_bytes());
    }
}

// ── Fixed-size byte arrays ──

impl<const N: usize> SszEncode for [u8; N] {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        N
    }
    #[inline(always)]
    fn encoded_len(&self) -> usize {
        N
    }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self);
    }
    #[cfg(feature = "alloc")]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        // `&[[u8; N]]` viewed as `&[u8]`: a single `memcpy`, without `unsafe`.
        buf.extend_from_slice(items.as_flattened());
    }
    #[inline(always)]
    fn ssz_has_write_fixed() -> bool {
        true
    }
    #[cfg(feature = "alloc")]
    #[inline(always)]
    fn ssz_write_fixed(&self, out: &mut [u8]) {
        out.copy_from_slice(self);
    }
}

// ── Vec<T> ──

impl<T: SszEncode> SszEncode for Vec<T> {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        false
    }

    #[inline(always)]
    fn fixed_size() -> usize {
        0
    }

    fn encoded_len(&self) -> usize {
        if T::is_fixed_size() {
            T::fixed_size() * self.len()
        } else {
            let offsets = self.len() * BYTES_PER_LENGTH_OFFSET;
            let mut data: usize = 0;
            let mut i = 0;
            while i < self.len() {
                data += self[i].encoded_len();
                i += 1;
            }
            offsets + data
        }
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        if T::is_fixed_size() {
            T::ssz_append_fixed_slice(self, buf);
        } else {
            encode_variable_length_items(self, buf);
        }
    }

    // With fixed-size items, the item type builds the new `Vec` (the integers do it
    // without going through `ssz_append`). Otherwise, it is the trait default.
    #[cfg(feature = "alloc")]
    fn to_ssz(&self) -> Vec<u8> {
        if T::is_fixed_size() {
            T::ssz_fixed_slice_to_vec(self)
        } else {
            let mut buf = Vec::with_capacity(self.encoded_len());
            self.ssz_append(&mut buf);
            buf
        }
    }

    // Same as the trait default, but written out here: the default would call
    // `ssz_append` through the very `Vec<T>` instance being defined.
    #[cfg(feature = "alloc")]
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        buf.reserve(Self::fixed_size() * items.len());
        let mut i = 0;
        while i < items.len() {
            items[i].ssz_append(buf);
            i += 1;
        }
    }
}

// ── Container encoding helper ──

/// Encodes a sequence of variable-length items with offset/data interleaving.
///
/// Pre-allocates the offset region, then appends variable data directly to `buf`
/// while patching offsets in-place — no intermediate buffer needed.
fn encode_variable_length_items<T: SszEncode>(items: &[T], buf: &mut Vec<u8>) {
    let count = items.len();
    let fixed_part_len = count * BYTES_PER_LENGTH_OFFSET;

    let start = buf.len();
    buf.resize(start + fixed_part_len, 0);

    let mut i = 0;
    while i < count {
        let offset = buf.len() - start;
        let pos = start + i * BYTES_PER_LENGTH_OFFSET;
        buf[pos..pos + BYTES_PER_LENGTH_OFFSET].copy_from_slice(&(offset as u32).to_le_bytes());
        items[i].ssz_append(buf);
        i += 1;
    }
}

/// `buf.copy_within(src..src + count, dest)`: the Aeneas library does not model
/// `copy_within`. Same panics and same `memmove` semantics (the regions may overlap);
/// when they do not overlap and the destination comes first, it copies in bulk.
fn copy_within(buf: &mut [u8], src: usize, count: usize, dest: usize) {
    assert!(
        src <= buf.len() && count <= buf.len() - src,
        "src is out of bounds"
    );
    assert!(dest <= buf.len() - count, "dest is out of bounds");
    if dest <= src {
        if count <= src - dest {
            // Disjoint regions, with the destination first: the `append_fixed` case. Split
            // the buffer in two and copy in one go (a `memcpy`).
            let (head, tail) = buf.split_at_mut(src);
            head[dest..dest + count].copy_from_slice(&tail[..count]);
        } else {
            let mut k = 0;
            while k < count {
                buf[dest + k] = buf[src + k];
                k += 1;
            }
        }
    } else {
        let mut k = count;
        while k > 0 {
            k -= 1;
            buf[dest + k] = buf[src + k];
        }
    }
}

/// Helper for encoding containers with mixed fixed/variable fields.
///
/// Pre-allocates the fixed region in the output buffer, then writes variable
/// data directly after it — no intermediate buffer. Fixed fields are patched
/// into the pre-allocated region. This eliminates the double-write that a
/// separate `variable_bytes` buffer would cause.
pub struct ContainerEncoder<'a> {
    buf: &'a mut Vec<u8>,
    /// Absolute position in `buf` where this container starts.
    start: usize,
    /// Absolute position in `buf` where the next fixed field or offset goes.
    fixed_cursor: usize,
    /// Size of the fixed region (for debug assertions).
    fixed_part_len: usize,
}

impl<'a> ContainerEncoder<'a> {
    pub fn new(buf: &'a mut Vec<u8>, fixed_part_len: usize) -> Self {
        let start = buf.len();
        buf.reserve(fixed_part_len);
        buf.resize(start + fixed_part_len, 0);
        Self {
            buf,
            start,
            fixed_cursor: start,
            fixed_part_len,
        }
    }

    /// Create with a total encoded length hint for upfront allocation.
    pub fn with_capacity(buf: &'a mut Vec<u8>, fixed_part_len: usize, total_len: usize) -> Self {
        let start = buf.len();
        buf.reserve(total_len);
        buf.resize(start + fixed_part_len, 0);
        Self {
            buf,
            start,
            fixed_cursor: start,
            fixed_part_len,
        }
    }

    /// Append a fixed-size field.
    #[inline]
    pub fn append_fixed<T: SszEncode>(&mut self, value: &T) {
        // If the type can write itself into a `&mut [u8]` and its place in the fixed
        // part already exists, write it there directly. Otherwise, the usual path.
        let pos = self.fixed_cursor;
        let len = self.buf.len();
        let size = T::fixed_size();
        if T::ssz_has_write_fixed() && pos <= len && size <= len - pos {
            value.ssz_write_fixed(&mut self.buf[pos..pos + size]);
            self.fixed_cursor = pos + size;
        } else {
            self.append_fixed_via_append(value);
        }
    }

    /// `append_fixed` for a type without a direct write: appends it at the end of the
    /// buffer, moves it to its place in the fixed part and truncates.
    #[inline]
    fn append_fixed_via_append<T: SszEncode>(&mut self, value: &T) {
        let pos = self.fixed_cursor;
        let end = self.buf.len();
        value.ssz_append(self.buf);
        let written = self.buf.len() - end;
        copy_within(self.buf, end, written, pos);
        // `resize` to a smaller length truncates: it is `truncate(end)`.
        self.buf.resize(end, 0);
        self.fixed_cursor += written;
    }

    /// Append a variable-size field.
    #[inline]
    pub fn append_variable<T: SszEncode>(&mut self, value: &T) {
        let var_offset = self.buf.len() - self.start;
        self.buf[self.fixed_cursor..self.fixed_cursor + BYTES_PER_LENGTH_OFFSET]
            .copy_from_slice(&(var_offset as u32).to_le_bytes());
        self.fixed_cursor += BYTES_PER_LENGTH_OFFSET;
        value.ssz_append(self.buf);
    }

    /// Finalize the container. All data is already in the output buffer.
    pub fn finalize(self) {
        debug_assert_eq!(self.fixed_cursor, self.start + self.fixed_part_len);
    }
}
