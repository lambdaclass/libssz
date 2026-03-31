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
        for item in items {
            item.ssz_append(buf);
        }
    }
}

#[cfg(feature = "alloc")]
fn append_fixed_slice_as_bytes<T>(items: &[T], buf: &mut Vec<u8>) {
    // SAFETY: Callers must only invoke this with types `T` that have no
    // padding bytes and a valid representation for any bit pattern. Integer
    // callers (u8..u128) are additionally cfg-guarded to little-endian
    // platforms so the memory layout matches SSZ wire format. The [u8; N]
    // caller is endianness-independent. Current callers: u8, u16, u32, u64,
    // u128, [u8; N].
    let byte_slice = unsafe {
        core::slice::from_raw_parts(items.as_ptr().cast::<u8>(), core::mem::size_of_val(items))
    };
    buf.extend_from_slice(byte_slice);
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
        #[cfg(target_endian = "little")]
        {
            append_fixed_slice_as_bytes(items, buf);
        }
        #[cfg(not(target_endian = "little"))]
        {
            buf.reserve(1 * items.len());
            for item in items {
                item.ssz_append(buf);
            }
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
        #[cfg(target_endian = "little")]
        {
            append_fixed_slice_as_bytes(items, buf);
        }
        #[cfg(not(target_endian = "little"))]
        {
            buf.reserve(2 * items.len());
            for item in items {
                item.ssz_append(buf);
            }
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
        #[cfg(target_endian = "little")]
        {
            append_fixed_slice_as_bytes(items, buf);
        }
        #[cfg(not(target_endian = "little"))]
        {
            buf.reserve(4 * items.len());
            for item in items {
                item.ssz_append(buf);
            }
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
        #[cfg(target_endian = "little")]
        {
            append_fixed_slice_as_bytes(items, buf);
        }
        #[cfg(not(target_endian = "little"))]
        {
            buf.reserve(8 * items.len());
            for item in items {
                item.ssz_append(buf);
            }
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
        #[cfg(target_endian = "little")]
        {
            append_fixed_slice_as_bytes(items, buf);
        }
        #[cfg(not(target_endian = "little"))]
        {
            buf.reserve(16 * items.len());
            for item in items {
                item.ssz_append(buf);
            }
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
        append_fixed_slice_as_bytes(items, buf);
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
            let data: usize = self.iter().map(|item| item.encoded_len()).sum();
            offsets + data
        }
    }

    fn ssz_append(&self, buf: &mut Vec<u8>) {
        if T::is_fixed_size() {
            T::ssz_append_fixed_slice(self, buf);
        } else {
            encode_variable_length_items(self.iter(), buf);
        }
    }
}

// ── Container encoding helper ──

/// Encodes a sequence of variable-length items with offset/data interleaving.
///
/// Pre-allocates the offset region, then appends variable data directly to `buf`
/// while patching offsets in-place — no intermediate buffer needed.
fn encode_variable_length_items<'a, T: SszEncode + 'a>(
    items: impl Iterator<Item = &'a T> + Clone,
    buf: &mut Vec<u8>,
) {
    let count = items.clone().count();
    let fixed_part_len = count * BYTES_PER_LENGTH_OFFSET;

    let start = buf.len();
    buf.resize(start + fixed_part_len, 0);

    for (i, item) in items.enumerate() {
        let offset = buf.len() - start;
        let pos = start + i * BYTES_PER_LENGTH_OFFSET;
        buf[pos..pos + BYTES_PER_LENGTH_OFFSET].copy_from_slice(&(offset as u32).to_le_bytes());
        item.ssz_append(buf);
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
        self.buf.copy_within(end..end + written, pos);
        self.buf.truncate(end);
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
