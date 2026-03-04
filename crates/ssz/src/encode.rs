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
}

// ── bool ──

impl SszEncode for bool {
    #[inline(always)]
    fn is_fixed_size() -> bool { true }
    #[inline(always)]
    fn fixed_size() -> usize { 1 }
    #[inline(always)]
    fn encoded_len(&self) -> usize { 1 }
    #[inline(always)]
    fn ssz_append(&self, buf: &mut Vec<u8>) {
        buf.push(if *self { 1 } else { 0 });
    }
}

// ── Unsigned integers ──

macro_rules! impl_ssz_encode_uint {
    ($ty:ty, $size:literal) => {
        impl SszEncode for $ty {
            #[inline(always)]
            fn is_fixed_size() -> bool { true }
            #[inline(always)]
            fn fixed_size() -> usize { $size }
            #[inline(always)]
            fn encoded_len(&self) -> usize { $size }
            #[inline(always)]
            fn ssz_append(&self, buf: &mut Vec<u8>) {
                buf.extend_from_slice(&self.to_le_bytes());
            }
        }
    };
}

impl_ssz_encode_uint!(u8, 1);
impl_ssz_encode_uint!(u16, 2);
impl_ssz_encode_uint!(u32, 4);
impl_ssz_encode_uint!(u64, 8);
impl_ssz_encode_uint!(u128, 16);

// ── Fixed-size byte arrays ──

macro_rules! impl_ssz_encode_byte_array {
    ($n:literal) => {
        impl SszEncode for [u8; $n] {
            #[inline(always)]
            fn is_fixed_size() -> bool { true }
            #[inline(always)]
            fn fixed_size() -> usize { $n }
            #[inline(always)]
            fn encoded_len(&self) -> usize { $n }
            #[inline(always)]
            fn ssz_append(&self, buf: &mut Vec<u8>) {
                buf.extend_from_slice(self);
            }
        }
    };
}

impl_ssz_encode_byte_array!(4);
impl_ssz_encode_byte_array!(20);
impl_ssz_encode_byte_array!(32);
impl_ssz_encode_byte_array!(48);
impl_ssz_encode_byte_array!(96);

// ── Vec<T> ──

impl<T: SszEncode> SszEncode for Vec<T> {
    #[inline(always)]
    fn is_fixed_size() -> bool { false }

    #[inline(always)]
    fn fixed_size() -> usize { 0 }

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
            for item in self {
                item.ssz_append(buf);
            }
        } else {
            encode_variable_length_items(self.iter(), buf);
        }
    }
}

// ── Container encoding helper ──

/// Encodes a sequence of variable-length items with offset/data interleaving.
fn encode_variable_length_items<'a, T: SszEncode + 'a>(
    items: impl Iterator<Item = &'a T> + Clone,
    buf: &mut Vec<u8>,
) {
    let count = items.clone().count();
    let fixed_part_len = count * BYTES_PER_LENGTH_OFFSET;

    let encoded: Vec<Vec<u8>> = items.map(|item| item.to_ssz()).collect();

    let mut offset = fixed_part_len;
    for data in &encoded {
        buf.extend_from_slice(&(offset as u32).to_le_bytes());
        offset += data.len();
    }

    for data in &encoded {
        buf.extend_from_slice(data);
    }
}

/// Helper for encoding containers with mixed fixed/variable fields.
///
/// Call `append_fixed` and `append_variable` in field order, then `finalize`.
pub struct ContainerEncoder {
    /// Combined fixed-part buffer. Fixed fields inline, placeholders for variable offsets.
    fixed_buf: Vec<u8>,
    /// Variable-part buffers, one per variable field, in order.
    var_bufs: Vec<Vec<u8>>,
    /// Byte positions in `fixed_buf` where offset placeholders were written.
    offset_positions: Vec<usize>,
}

impl Default for ContainerEncoder {
    fn default() -> Self {
        Self::new()
    }
}

impl ContainerEncoder {
    pub fn new() -> Self {
        Self {
            fixed_buf: Vec::new(),
            var_bufs: Vec::new(),
            offset_positions: Vec::new(),
        }
    }

    /// Append a fixed-size field.
    pub fn append_fixed<T: SszEncode>(&mut self, value: &T) {
        value.ssz_append(&mut self.fixed_buf);
    }

    /// Append a variable-size field.
    pub fn append_variable<T: SszEncode>(&mut self, value: &T) {
        self.offset_positions.push(self.fixed_buf.len());
        self.fixed_buf.extend_from_slice(&[0u8; BYTES_PER_LENGTH_OFFSET]);
        self.var_bufs.push(value.to_ssz());
    }

    /// Finalize and write the complete container encoding to `buf`.
    pub fn finalize(mut self, buf: &mut Vec<u8>) {
        let fixed_len = self.fixed_buf.len();
        let mut offset = fixed_len;

        // Patch placeholder offsets with actual values.
        for (i, pos) in self.offset_positions.iter().enumerate() {
            let offset_bytes = (offset as u32).to_le_bytes();
            self.fixed_buf[*pos..*pos + BYTES_PER_LENGTH_OFFSET]
                .copy_from_slice(&offset_bytes);
            offset += self.var_bufs[i].len();
        }

        buf.extend_from_slice(&self.fixed_buf);
        for part in &self.var_bufs {
            buf.extend_from_slice(part);
        }
    }
}
