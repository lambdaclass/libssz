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
}

// ── bool ──

impl SszDecode for bool {
    #[inline(always)]
    fn is_fixed_size() -> bool { true }
    #[inline(always)]
    fn fixed_size() -> usize { 1 }

    fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        if bytes.len() != 1 {
            return Err(DecodeError::InvalidFixedLength { expected: 1, got: bytes.len() });
        }
        match bytes[0] {
            0 => Ok(false),
            1 => Ok(true),
            b => Err(DecodeError::InvalidBooleanByte(b)),
        }
    }
}

// ── Unsigned integers ──

macro_rules! impl_ssz_decode_uint {
    ($ty:ty, $size:literal) => {
        impl SszDecode for $ty {
            #[inline(always)]
            fn is_fixed_size() -> bool { true }
            #[inline(always)]
            fn fixed_size() -> usize { $size }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
                if bytes.len() != $size {
                    return Err(DecodeError::InvalidFixedLength { expected: $size, got: bytes.len() });
                }
                let mut arr = [0u8; $size];
                arr.copy_from_slice(bytes);
                Ok(<$ty>::from_le_bytes(arr))
            }
        }
    };
}

impl_ssz_decode_uint!(u8, 1);
impl_ssz_decode_uint!(u16, 2);
impl_ssz_decode_uint!(u32, 4);
impl_ssz_decode_uint!(u64, 8);
impl_ssz_decode_uint!(u128, 16);

// ── Fixed-size byte arrays ──

macro_rules! impl_ssz_decode_byte_array {
    ($n:literal) => {
        impl SszDecode for [u8; $n] {
            #[inline(always)]
            fn is_fixed_size() -> bool { true }
            #[inline(always)]
            fn fixed_size() -> usize { $n }

            fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
                if bytes.len() != $n {
                    return Err(DecodeError::InvalidFixedLength { expected: $n, got: bytes.len() });
                }
                let mut arr = [0u8; $n];
                arr.copy_from_slice(bytes);
                Ok(arr)
            }
        }
    };
}

impl_ssz_decode_byte_array!(4);
impl_ssz_decode_byte_array!(20);
impl_ssz_decode_byte_array!(32);
impl_ssz_decode_byte_array!(48);
impl_ssz_decode_byte_array!(96);

// ── Vec<T> ──

impl<T: SszDecode> SszDecode for Vec<T> {
    #[inline(always)]
    fn is_fixed_size() -> bool { false }

    #[inline(always)]
    fn fixed_size() -> usize { 0 }

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
            bytes
                .chunks_exact(item_size)
                .map(T::from_ssz_bytes)
                .collect()
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
        return Err(DecodeError::InvalidFirstOffset { expected: BYTES_PER_LENGTH_OFFSET, got: 0 });
    }

    // Read all offsets.
    let mut offsets = Vec::with_capacity(num_items);
    for i in 0..num_items {
        let offset = read_offset(bytes, i * BYTES_PER_LENGTH_OFFSET)?;
        if !offsets.is_empty() && offset < *offsets.last().unwrap() {
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

    // Decode each item from its slice.
    let mut items = Vec::with_capacity(num_items);
    for i in 0..num_items {
        let start = offsets[i];
        let end = if i + 1 < num_items { offsets[i + 1] } else { bytes.len() };
        items.push(T::from_ssz_bytes(&bytes[start..end])?);
    }

    Ok(items)
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

        // Extract all variable-field offsets from the fixed part.
        // The caller will tell us which fields are variable via decode_variable.
        Ok(Self {
            bytes,
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
        if !self.offsets.is_empty() && offset < *self.offsets.last().unwrap() {
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
