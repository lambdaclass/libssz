#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use crate::error::DecodeError;
use crate::BYTES_PER_LENGTH_OFFSET;

/// Trait for SSZ-decodable types.
pub trait SszDecode: Sized {
    /// Returns `true` if this type has a fixed SSZ size.
    fn is_fixed_size() -> bool;

    /// Returns the fixed size in bytes. Only meaningful when `is_fixed_size()` is `true`.
    fn fixed_size() -> usize;

    /// Decode from SSZ bytes.
    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError>;

    /// Bulk-decode a byte buffer into a `Vec` of fixed-size items.
    ///
    /// The default loops over chunks. Integer types override this with a single
    /// memcpy on little-endian platforms.
    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        let item_size = Self::fixed_size();
        assert!(item_size != 0, "chunk size must be non-zero");
        let count = bytes.len() / item_size;
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            let start = i * item_size;
            result.push(Self::from_ssz_bytes(&bytes[start..start + item_size])?);
            i += 1;
        }
        Ok(result)
    }
}

// ── bool ──

impl SszDecode for bool {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        1
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 1 {
            return Err(DecodeError::InvalidFixedLength {
                expected: 1,
                got: bytes.len(),
            });
        }
        match bytes[0] {
            0 => Ok(false),
            1 => Ok(true),
            b => Err(DecodeError::InvalidBooleanByte(b)),
        }
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        let count = bytes.len();
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            result.push(Self::from_ssz_bytes(&bytes[i..i + 1])?);
            i += 1;
        }
        Ok(result)
    }
}

// ── Unsigned integers ──

fn decode_uint<const N: usize>(bytes: &[u8]) -> Result<[u8; N], DecodeError> {
    if bytes.len() != N {
        return Err(DecodeError::InvalidFixedLength {
            expected: N,
            got: bytes.len(),
        });
    }
    let mut arr = [0u8; N];
    arr.copy_from_slice(bytes);
    Ok(arr)
}

impl SszDecode for u8 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        1
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let arr = decode_uint::<1>(bytes)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(1) {
            return Err(DecodeError::InvalidByteLength {
                expected: 1,
                got: bytes.len(),
            });
        }
        let count = bytes.len();
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            let mut arr = [0u8; 1];
            arr.copy_from_slice(&bytes[i..i + 1]);
            result.push(Self::from_le_bytes(arr));
            i += 1;
        }
        Ok(result)
    }
}

impl SszDecode for u16 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        2
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let arr = decode_uint::<2>(bytes)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(2) {
            return Err(DecodeError::InvalidByteLength {
                expected: 2,
                got: bytes.len(),
            });
        }
        let count = bytes.len() / 2;
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            let mut arr = [0u8; 2];
            arr.copy_from_slice(&bytes[i * 2..i * 2 + 2]);
            result.push(Self::from_le_bytes(arr));
            i += 1;
        }
        Ok(result)
    }
}

impl SszDecode for u32 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        4
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let arr = decode_uint::<4>(bytes)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(4) {
            return Err(DecodeError::InvalidByteLength {
                expected: 4,
                got: bytes.len(),
            });
        }
        let count = bytes.len() / 4;
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            let mut arr = [0u8; 4];
            arr.copy_from_slice(&bytes[i * 4..i * 4 + 4]);
            result.push(Self::from_le_bytes(arr));
            i += 1;
        }
        Ok(result)
    }
}

impl SszDecode for u64 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        8
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let arr = decode_uint::<8>(bytes)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(8) {
            return Err(DecodeError::InvalidByteLength {
                expected: 8,
                got: bytes.len(),
            });
        }
        let count = bytes.len() / 8;
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            let mut arr = [0u8; 8];
            arr.copy_from_slice(&bytes[i * 8..i * 8 + 8]);
            result.push(Self::from_le_bytes(arr));
            i += 1;
        }
        Ok(result)
    }
}

impl SszDecode for u128 {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        16
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        let arr = decode_uint::<16>(bytes)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(16) {
            return Err(DecodeError::InvalidByteLength {
                expected: 16,
                got: bytes.len(),
            });
        }
        let count = bytes.len() / 16;
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            let mut arr = [0u8; 16];
            arr.copy_from_slice(&bytes[i * 16..i * 16 + 16]);
            result.push(Self::from_le_bytes(arr));
            i += 1;
        }
        Ok(result)
    }
}

// ── Fixed-size byte arrays ──

fn decode_byte_array<const N: usize>(bytes: &[u8]) -> Result<[u8; N], DecodeError> {
    if bytes.len() != N {
        return Err(DecodeError::InvalidFixedLength {
            expected: N,
            got: bytes.len(),
        });
    }
    Ok(bytes
        .try_into()
        .expect("bug: length already validated above"))
}

#[cfg(feature = "alloc")]
fn decode_byte_array_vec<const N: usize>(bytes: &[u8]) -> Result<Vec<[u8; N]>, DecodeError> {
    if !bytes.len().is_multiple_of(N) {
        return Err(DecodeError::InvalidByteLength {
            expected: N,
            got: bytes.len(),
        });
    }
    let count = bytes.len() / N;
    let mut result = Vec::<[u8; N]>::with_capacity(count);
    let mut i = 0;
    while i < count {
        let mut arr = [0u8; N];
        arr.copy_from_slice(&bytes[i * N..i * N + N]);
        result.push(arr);
        i += 1;
    }
    Ok(result)
}

impl<const N: usize> SszDecode for [u8; N] {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        true
    }
    #[inline(always)]
    fn fixed_size() -> usize {
        N
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        decode_byte_array::<N>(bytes)
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        decode_byte_array_vec::<N>(bytes)
    }
}

// ── Vec<T> ──

impl<T: SszDecode> SszDecode for Vec<T> {
    #[inline(always)]
    fn is_fixed_size() -> bool {
        false
    }

    #[inline(always)]
    fn fixed_size() -> usize {
        0
    }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        decode_list_with_max(bytes, usize::MAX)
    }

    // Same as the trait default (`fixed_size()` is 0, so it panics like
    // `chunks_exact(0)`), written out here for the same reason as in `SszEncode`.
    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        let item_size = Self::fixed_size();
        assert!(item_size != 0, "chunk size must be non-zero");
        let count = bytes.len() / item_size;
        let mut result = Vec::with_capacity(count);
        let mut i = 0;
        while i < count {
            let start = i * item_size;
            result.push(Self::from_ssz_bytes(&bytes[start..start + item_size])?);
            i += 1;
        }
        Ok(result)
    }
}

/// Decode an SSZ list, rejecting inputs with more than `max_len` items before
/// decoding item bodies.
#[inline]
pub fn decode_list_with_max<T: SszDecode>(
    bytes: &[u8],
    max_len: usize,
) -> Result<Vec<T>, DecodeError> {
    if bytes.is_empty() {
        return Ok(Vec::new());
    }

    if T::is_fixed_size() {
        let item_size = T::fixed_size();
        if item_size == 0 {
            return Err(DecodeError::InvalidByteLength {
                expected: 0,
                got: bytes.len(),
            });
        }

        if !bytes.len().is_multiple_of(item_size) {
            return Err(DecodeError::InvalidByteLength {
                expected: item_size,
                got: bytes.len(),
            });
        }

        let len = bytes.len() / item_size;
        if len > max_len {
            return Err(DecodeError::InvalidByteLength {
                expected: max_len,
                got: len,
            });
        }

        T::ssz_decode_fixed_vec(bytes)
    } else {
        decode_variable_length_items_with_max(bytes, max_len)
    }
}

/// Decode a bounded list of variable-length items from SSZ bytes.
fn decode_variable_length_items_with_max<T: SszDecode>(
    bytes: &[u8],
    max_len: usize,
) -> Result<Vec<T>, DecodeError> {
    if bytes.len() < BYTES_PER_LENGTH_OFFSET {
        return Err(DecodeError::InvalidByteLength {
            expected: BYTES_PER_LENGTH_OFFSET,
            got: bytes.len(),
        });
    }

    // Read the first offset to determine the number of items.
    let first_offset = read_offset(bytes, 0)?;
    if first_offset % BYTES_PER_LENGTH_OFFSET != 0 {
        return Err(DecodeError::InvalidFirstOffset {
            expected: 0, // placeholder — must be multiple of 4
            got: first_offset,
        });
    }

    if first_offset > bytes.len() {
        return Err(DecodeError::OffsetOutOfBounds {
            offset: first_offset,
            length: bytes.len(),
        });
    }

    let num_items = first_offset / BYTES_PER_LENGTH_OFFSET;
    if num_items == 0 {
        return Err(DecodeError::InvalidFirstOffset {
            expected: BYTES_PER_LENGTH_OFFSET,
            got: 0,
        });
    }
    if num_items > max_len {
        return Err(DecodeError::InvalidByteLength {
            expected: max_len,
            got: num_items,
        });
    }

    // Read all offsets, with bytes.len() as a sentinel for the last item's end.
    let offsets = read_item_offsets(bytes, num_items)?;

    // Decode each item from its slice.
    decode_items(bytes, &offsets, num_items)
}

/// The `num_items` offsets of a list of variable-size items, validated (increasing and
/// within `bytes`), followed by `bytes.len()`.
fn read_item_offsets(bytes: &[u8], num_items: usize) -> Result<Vec<usize>, DecodeError> {
    let mut offsets: Vec<usize> = Vec::with_capacity(num_items + 1);
    let mut i = 0;
    while i < num_items {
        let offset = read_offset(bytes, i * BYTES_PER_LENGTH_OFFSET)?;
        if i > 0 && offset < offsets[i - 1] {
            return Err(DecodeError::OffsetsAreNotMonotonicallyIncreasing);
        }
        if offset > bytes.len() {
            return Err(DecodeError::OffsetOutOfBounds {
                offset,
                length: bytes.len(),
            });
        }
        offsets.push(offset);
        i += 1;
    }
    offsets.push(bytes.len());
    Ok(offsets)
}

/// Decodes item `j` from `bytes[offsets[j]..offsets[j + 1]]`, for `j < num_items`.
fn decode_items<T: SszDecode>(
    bytes: &[u8],
    offsets: &[usize],
    num_items: usize,
) -> Result<Vec<T>, DecodeError> {
    let mut result = Vec::with_capacity(num_items);
    let mut j = 0;
    while j < num_items {
        result.push(T::from_ssz_bytes(&bytes[offsets[j]..offsets[j + 1]])?);
        j += 1;
    }
    Ok(result)
}

/// Read a 4-byte little-endian offset at the given byte position.
fn read_offset(bytes: &[u8], pos: usize) -> Result<usize, DecodeError> {
    if pos + BYTES_PER_LENGTH_OFFSET > bytes.len() {
        return Err(DecodeError::OffsetOutOfBounds {
            offset: pos,
            length: bytes.len(),
        });
    }
    let mut buf = [0u8; 4];
    buf.copy_from_slice(&bytes[pos..pos + 4]);
    Ok(u32::from_le_bytes(buf) as usize)
}

/// Helper for decoding containers with mixed fixed/variable fields.
///
/// Parses the fixed part to extract field slices and variable-field offsets.
pub struct ContainerDecoder<'a> {
    bytes: &'a [u8],
    fixed_part_len: usize,
    cursor: usize,
    offsets: Vec<usize>,
    variable_index: usize,
}

impl<'a> ContainerDecoder<'a> {
    /// Create a new decoder. `fixed_part_len` is the expected total size of the
    /// fixed portion (sum of fixed field sizes + 4 bytes per variable field).
    pub fn new(bytes: &'a [u8], fixed_part_len: usize) -> Result<Self, DecodeError> {
        if bytes.len() < fixed_part_len {
            return Err(DecodeError::InvalidByteLength {
                expected: fixed_part_len,
                got: bytes.len(),
            });
        }

        Ok(Self {
            bytes,
            fixed_part_len,
            cursor: 0,
            offsets: Vec::new(),
            variable_index: 0,
        })
    }

    /// Decode a fixed-size field at the current cursor position.
    pub fn decode_fixed<T: SszDecode>(&mut self) -> Result<T, DecodeError> {
        let size = T::fixed_size();
        let end = self.cursor + size;
        if end > self.bytes.len() {
            return Err(DecodeError::InvalidByteLength {
                expected: end,
                got: self.bytes.len(),
            });
        }
        let result = T::from_ssz_bytes(&self.bytes[self.cursor..end])?;
        self.cursor = end;
        Ok(result)
    }

    /// Read a variable-field offset at the current cursor position.
    /// Call this for each variable field in order during the fixed-part pass.
    pub fn read_variable_offset(&mut self) -> Result<(), DecodeError> {
        let offset = read_offset(self.bytes, self.cursor)?;
        // First offset must point to the start of the variable part
        if self.offsets.is_empty() {
            if offset != self.fixed_part_len {
                return Err(DecodeError::InvalidFirstOffset {
                    expected: self.fixed_part_len,
                    got: offset,
                });
            }
        } else if offset < self.offsets[self.offsets.len() - 1] {
            return Err(DecodeError::OffsetsAreNotMonotonicallyIncreasing);
        }
        if offset > self.bytes.len() {
            return Err(DecodeError::OffsetOutOfBounds {
                offset,
                length: self.bytes.len(),
            });
        }
        self.offsets.push(offset);
        self.cursor += BYTES_PER_LENGTH_OFFSET;
        Ok(())
    }

    /// Decode the next variable-length field. Must be called after all
    /// fixed-part reads (decode_fixed / read_variable_offset) are done.
    pub fn decode_variable<T: SszDecode>(&mut self) -> Result<T, DecodeError> {
        let idx = self.variable_index;
        if idx >= self.offsets.len() {
            return Err(DecodeError::InvalidByteLength {
                expected: idx + 1,
                got: self.offsets.len(),
            });
        }

        let start = self.offsets[idx];
        let end = if idx + 1 < self.offsets.len() {
            self.offsets[idx + 1]
        } else {
            self.bytes.len()
        };

        self.variable_index += 1;
        T::from_ssz_bytes(&self.bytes[start..end])
    }

    /// Verify there are no unconsumed bytes (for all-fixed containers).
    pub fn finish_fixed(self) -> Result<(), DecodeError> {
        if self.cursor != self.bytes.len() {
            return Err(DecodeError::AdditionalBytes {
                expected: self.cursor,
                got: self.bytes.len(),
            });
        }
        Ok(())
    }

    /// Fixed-part step for one field, as `ssz-derive` used to write it inline: a fixed-size
    /// field is decoded, a variable-size one records its offset. The macro calls this method
    /// so that each field is a single call with `?` (see `ssz-derive`).
    #[doc(hidden)]
    pub fn decode_fixed_part<T: SszDecode>(&mut self) -> Result<Option<T>, DecodeError> {
        if T::is_fixed_size() {
            Ok(Some(self.decode_fixed::<T>()?))
        } else {
            self.read_variable_offset()?;
            Ok(None)
        }
    }

    /// Variable-part step for one field: the already decoded value if it is fixed-size, or
    /// its body if it is variable-size.
    #[doc(hidden)]
    pub fn decode_variable_part<T: SszDecode>(
        &mut self,
        fixed: Option<T>,
    ) -> Result<T, DecodeError> {
        if T::is_fixed_size() {
            Ok(fixed.unwrap())
        } else {
            self.decode_variable::<T>()
        }
    }
}
