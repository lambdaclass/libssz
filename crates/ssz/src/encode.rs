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
        buf.reserve(items.len());
        let mut i = 0;
        while i < items.len() {
            buf.extend_from_slice(&items[i].to_le_bytes());
            i += 1;
        }
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
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        buf.reserve(2 * items.len());
        let mut i = 0;
        while i < items.len() {
            buf.extend_from_slice(&items[i].to_le_bytes());
            i += 1;
        }
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
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        buf.reserve(4 * items.len());
        let mut i = 0;
        while i < items.len() {
            buf.extend_from_slice(&items[i].to_le_bytes());
            i += 1;
        }
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
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        buf.reserve(8 * items.len());
        let mut i = 0;
        while i < items.len() {
            buf.extend_from_slice(&items[i].to_le_bytes());
            i += 1;
        }
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
    fn ssz_append_fixed_slice(items: &[Self], buf: &mut Vec<u8>) {
        buf.reserve(16 * items.len());
        let mut i = 0;
        while i < items.len() {
            buf.extend_from_slice(&items[i].to_le_bytes());
            i += 1;
        }
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
        buf.reserve(N * items.len());
        let mut i = 0;
        while i < items.len() {
            buf.extend_from_slice(&items[i]);
            i += 1;
        }
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

/// `buf.copy_within(src..src + count, dest)`, written with indices: the Aeneas library
/// does not model `copy_within`. Same panics and same `memmove` semantics (the regions
/// may overlap).
fn copy_within(buf: &mut [u8], src: usize, count: usize, dest: usize) {
    assert!(
        src <= buf.len() && count <= buf.len() - src,
        "src is out of bounds"
    );
    assert!(dest <= buf.len() - count, "dest is out of bounds");
    if dest <= src {
        let mut k = 0;
        while k < count {
            buf[dest + k] = buf[src + k];
            k += 1;
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
