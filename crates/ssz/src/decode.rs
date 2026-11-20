#[cfg(feature = "alloc")]
use alloc::boxed::Box;
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

/// Copies `bytes` into `arr` if it has exactly `N` bytes.
///
/// The caller provides the array instead of getting it back inside the `Result`: in a
/// `Result<[u8; N], DecodeError>` the array is misaligned (it comes after the discriminant
/// byte) and, for `N = 16`, the compiler ended up assembling the `u128` piece by piece.
#[inline(always)]
fn decode_uint<const N: usize>(bytes: &[u8], arr: &mut [u8; N]) -> Result<(), DecodeError> {
    if bytes.len() != N {
        return Err(DecodeError::InvalidFixedLength {
            expected: N,
            got: bytes.len(),
        });
    }
    arr.copy_from_slice(bytes);
    Ok(())
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
        let mut arr = [0u8; 1];
        decode_uint::<1>(bytes, &mut arr)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        // One byte per item: the list is the input itself (a `memcpy`).
        Ok(bytes.to_vec())
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
        let mut arr = [0u8; 2];
        decode_uint::<2>(bytes, &mut arr)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(2) {
            return Err(DecodeError::InvalidByteLength {
                expected: 2,
                got: bytes.len(),
            });
        }
        // `&[u8]` viewed as `&[[u8; 2]]`, one chunk per item; the copy happens separately.
        let (chunks, _) = bytes.as_chunks::<2>();
        Ok(u16s_from_le_chunks(chunks).into_vec())
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
        let mut arr = [0u8; 4];
        decode_uint::<4>(bytes, &mut arr)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(4) {
            return Err(DecodeError::InvalidByteLength {
                expected: 4,
                got: bytes.len(),
            });
        }
        // `&[u8]` viewed as `&[[u8; 4]]`, one chunk per item; the copy happens separately.
        let (chunks, _) = bytes.as_chunks::<4>();
        Ok(u32s_from_le_chunks(chunks).into_vec())
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
        let mut arr = [0u8; 8];
        decode_uint::<8>(bytes, &mut arr)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(8) {
            return Err(DecodeError::InvalidByteLength {
                expected: 8,
                got: bytes.len(),
            });
        }
        // `&[u8]` viewed as `&[[u8; 8]]`, one chunk per item; the copy happens separately.
        let (chunks, _) = bytes.as_chunks::<8>();
        Ok(u64s_from_le_chunks(chunks).into_vec())
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
        let mut arr = [0u8; 16];
        decode_uint::<16>(bytes, &mut arr)?;
        Ok(Self::from_le_bytes(arr))
    }

    #[cfg(feature = "alloc")]
    #[inline]
    fn ssz_decode_fixed_vec(bytes: &[u8]) -> Result<Vec<Self>, DecodeError> {
        if !bytes.len().is_multiple_of(16) {
            return Err(DecodeError::InvalidByteLength {
                expected: 16,
                got: bytes.len(),
            });
        }
        // `&[u8]` viewed as `&[[u8; 16]]`, one chunk per item; the copy happens separately.
        let (chunks, _) = bytes.as_chunks::<16>();
        Ok(u128s_from_le_chunks(chunks).into_vec())
    }
}

// ── From little-endian chunks to integers (for `ssz_decode_fixed_vec`) ──
//
// The iterator knows its exact length, so `collect` allocates once and writes without
// zeroing first; on little-endian the compiler turns the loop into a `memcpy`... as long
// as it knows that `chunks` and the new `Vec` do not overlap, and it only knows that for
// sure when `chunks` is a parameter of the function containing the loop. Hence
// `inline(never)`: inlined into an arbitrary caller they become a loop of 32 bytes at a
// time (with a thousand `u64`s, ~75% slower). Two more details, both measured:
//
//  - the empty list is handled separately. Otherwise the loop's destination is "the empty
//    `Vec`'s pointer or the freshly allocated memory", and with that doubt there is no
//    `memcpy` either;
//  - they return `Box<[T]>`, not `Vec<T>`. A `Box<[T]>` is a pointer and a length, and is
//    returned in two registers; a `Vec<T>` is three words, is returned through memory, and
//    re-reading them cost the caller up to ~8 ns per call. `into_vec` is free.

#[cfg(feature = "alloc")]
#[inline(never)]
fn u16s_from_le_chunks(chunks: &[[u8; 2]]) -> Box<[u16]> {
    if chunks.is_empty() {
        return Vec::new().into_boxed_slice();
    }
    let items: Vec<u16> = chunks.iter().map(|c| u16::from_le_bytes(*c)).collect();
    items.into_boxed_slice()
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u32s_from_le_chunks(chunks: &[[u8; 4]]) -> Box<[u32]> {
    if chunks.is_empty() {
        return Vec::new().into_boxed_slice();
    }
    let items: Vec<u32> = chunks.iter().map(|c| u32::from_le_bytes(*c)).collect();
    items.into_boxed_slice()
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u64s_from_le_chunks(chunks: &[[u8; 8]]) -> Box<[u64]> {
    if chunks.is_empty() {
        return Vec::new().into_boxed_slice();
    }
    let items: Vec<u64> = chunks.iter().map(|c| u64::from_le_bytes(*c)).collect();
    items.into_boxed_slice()
}

#[cfg(feature = "alloc")]
#[inline(never)]
fn u128s_from_le_chunks(chunks: &[[u8; 16]]) -> Box<[u128]> {
    if chunks.is_empty() {
        return Vec::new().into_boxed_slice();
    }
    let items: Vec<u128> = chunks.iter().map(|c| u128::from_le_bytes(*c)).collect();
    items.into_boxed_slice()
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
    // `&[u8]` viewed as `&[[u8; N]]` and copied in one go (a `memcpy`), without `unsafe`.
    let (chunks, _) = bytes.as_chunks::<N>();
    Ok(chunks.to_vec())
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
    // The offsets of the variable fields read so far, in order: the first
    // `INLINE_OFFSETS` in `inline_offsets` and the rest in `spilled_offsets`. This way a
    // container with up to `INLINE_OFFSETS` variable fields is decoded without allocating
    // memory for the offsets.
    inline_offsets: [usize; INLINE_OFFSETS],
    spilled_offsets: Vec<usize>,
    num_offsets: usize,
    variable_index: usize,
}

/// How many offsets a `ContainerDecoder` stores without allocating.
const INLINE_OFFSETS: usize = 8;

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
            inline_offsets: [0; INLINE_OFFSETS],
            spilled_offsets: Vec::new(),
            num_offsets: 0,
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
        let n = self.num_offsets;
        // First offset must point to the start of the variable part
        if n == 0 {
            if offset != self.fixed_part_len {
                return Err(DecodeError::InvalidFirstOffset {
                    expected: self.fixed_part_len,
                    got: offset,
                });
            }
        } else if offset < self.offset_at(n - 1) {
            return Err(DecodeError::OffsetsAreNotMonotonicallyIncreasing);
        }
        if offset > self.bytes.len() {
            return Err(DecodeError::OffsetOutOfBounds {
                offset,
                length: self.bytes.len(),
            });
        }
        if n < INLINE_OFFSETS {
            self.inline_offsets[n] = offset;
        } else {
            self.spilled_offsets.push(offset);
        }
        self.num_offsets = n + 1;
        self.cursor += BYTES_PER_LENGTH_OFFSET;
        Ok(())
    }

    /// The `i`-th of the offsets read so far (`i < self.num_offsets`).
    #[inline]
    fn offset_at(&self, i: usize) -> usize {
        if i < INLINE_OFFSETS {
            self.inline_offsets[i]
        } else {
            self.spilled_offsets[i - INLINE_OFFSETS]
        }
    }

    /// Decode the next variable-length field. Must be called after all
    /// fixed-part reads (decode_fixed / read_variable_offset) are done.
    pub fn decode_variable<T: SszDecode>(&mut self) -> Result<T, DecodeError> {
        let idx = self.variable_index;
        let n = self.num_offsets;
        if idx >= n {
            return Err(DecodeError::InvalidByteLength {
                expected: idx + 1,
                got: n,
            });
        }

        let start = self.offset_at(idx);
        let end = if idx + 1 < n {
            self.offset_at(idx + 1)
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
