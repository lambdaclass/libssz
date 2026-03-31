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
        bytes
            .chunks_exact(item_size)
            .map(Self::from_ssz_bytes)
            .collect()
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
}

// ── Unsigned integers ──

fn decode_uint<const N: usize, T>(
    bytes: &[u8],
    from_le_bytes: impl FnOnce([u8; N]) -> T,
) -> Result<T, DecodeError> {
    if bytes.len() != N {
        return Err(DecodeError::InvalidFixedLength {
            expected: N,
            got: bytes.len(),
        });
    }
    let mut arr = [0u8; N];
    arr.copy_from_slice(bytes);
    Ok(from_le_bytes(arr))
}

#[cfg(feature = "alloc")]
fn decode_fixed_vec_le<T>(bytes: &[u8], item_size: usize) -> Result<Vec<T>, DecodeError> {
    #[cfg(target_endian = "little")]
    {
        if !bytes.len().is_multiple_of(item_size) {
            return Err(DecodeError::InvalidByteLength {
                expected: item_size,
                got: bytes.len(),
            });
        }
        let count = bytes.len() / item_size;
        let mut result = Vec::<T>::with_capacity(count);
        unsafe {
            core::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                result.as_mut_ptr() as *mut u8,
                bytes.len(),
            );
            result.set_len(count);
        }
        Ok(result)
    }
    #[cfg(not(target_endian = "little"))]
    {
        let _ = bytes;
        let _ = item_size;
        unreachable!()
    }
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
        decode_uint::<1, Self>(bytes, Self::from_le_bytes)
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        #[cfg(target_endian = "little")]
        {
            decode_fixed_vec_le(bytes, 1)
        }
        #[cfg(not(target_endian = "little"))]
        {
            bytes.chunks_exact(1).map(Self::from_ssz_bytes).collect()
        }
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
        decode_uint::<2, Self>(bytes, Self::from_le_bytes)
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        #[cfg(target_endian = "little")]
        {
            decode_fixed_vec_le(bytes, 2)
        }
        #[cfg(not(target_endian = "little"))]
        {
            bytes.chunks_exact(2).map(Self::from_ssz_bytes).collect()
        }
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
        decode_uint::<4, Self>(bytes, Self::from_le_bytes)
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        #[cfg(target_endian = "little")]
        {
            decode_fixed_vec_le(bytes, 4)
        }
        #[cfg(not(target_endian = "little"))]
        {
            bytes.chunks_exact(4).map(Self::from_ssz_bytes).collect()
        }
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
        decode_uint::<8, Self>(bytes, Self::from_le_bytes)
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        #[cfg(target_endian = "little")]
        {
            decode_fixed_vec_le(bytes, 8)
        }
        #[cfg(not(target_endian = "little"))]
        {
            bytes.chunks_exact(8).map(Self::from_ssz_bytes).collect()
        }
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
        decode_uint::<16, Self>(bytes, Self::from_le_bytes)
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        #[cfg(target_endian = "little")]
        {
            decode_fixed_vec_le(bytes, 16)
        }
        #[cfg(not(target_endian = "little"))]
        {
            bytes.chunks_exact(16).map(Self::from_ssz_bytes).collect()
        }
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
    // SAFETY: `[u8; N]` has size `N`, alignment 1, no padding, and is valid
    // for any bit pattern. The length check guarantees `count * N ==
    // bytes.len()`, and `with_capacity(count)` allocates at least `count * N`
    // bytes, so the copy stays in bounds. No endianness concern since the
    // element type is raw bytes.
    unsafe {
        core::ptr::copy_nonoverlapping(bytes.as_ptr(), result.as_mut_ptr() as *mut u8, bytes.len());
        result.set_len(count);
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
        if bytes.is_empty() {
            return Ok(Vec::new());
        }

        if T::is_fixed_size() {
            let item_size = T::fixed_size();
            if !bytes.len().is_multiple_of(item_size) {
                return Err(DecodeError::InvalidByteLength {
                    expected: item_size,
                    got: bytes.len(),
                });
            }
            T::ssz_decode_fixed_vec(bytes)
        } else {
            decode_variable_length_items(bytes)
        }
    }
}

/// Decode a list of variable-length items from SSZ bytes.
fn decode_variable_length_items<T: SszDecode>(bytes: &[u8]) -> Result<Vec<T>, DecodeError> {
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

    let num_items = first_offset / BYTES_PER_LENGTH_OFFSET;
    if num_items == 0 {
        return Err(DecodeError::InvalidFirstOffset {
            expected: BYTES_PER_LENGTH_OFFSET,
            got: 0,
        });
    }

    // Read all offsets, with bytes.len() as a sentinel for the last item's end.
    let mut offsets = Vec::with_capacity(num_items + 1);
    for i in 0..num_items {
        let offset = read_offset(bytes, i * BYTES_PER_LENGTH_OFFSET)?;
        if offsets.last().is_some_and(|&last| offset < last) {
            return Err(DecodeError::OffsetsAreNotMonotonicallyIncreasing);
        }
        if offset > bytes.len() {
            return Err(DecodeError::OffsetOutOfBounds {
                offset,
                length: bytes.len(),
            });
        }
        offsets.push(offset);
    }
    offsets.push(bytes.len());

    // Decode each item from its slice.
    offsets
        .windows(2)
        .map(|pair| T::from_ssz_bytes(&bytes[pair[0]..pair[1]]))
        .collect()
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
        } else if offset
            < *self
                .offsets
                .last()
                .expect("bug: offsets verified non-empty")
        {
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
}
