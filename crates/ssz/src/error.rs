#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    /// Input bytes are shorter than expected.
    InvalidByteLength { expected: usize, got: usize },
    /// A fixed-size type received the wrong number of bytes.
    InvalidFixedLength { expected: usize, got: usize },
    /// An offset points outside the input buffer.
    OffsetOutOfBounds { offset: usize, length: usize },
    /// Offsets are not monotonically increasing.
    OffsetsAreNotMonotonicallyIncreasing,
    /// The first variable offset does not match the expected fixed-part length.
    InvalidFirstOffset { expected: usize, got: usize },
    /// A boolean byte is not 0 or 1.
    InvalidBooleanByte(u8),
    /// Extra bytes remain after decoding.
    ExtraBytesRemaining(usize),
    /// The input is empty when it shouldn't be.
    EmptyInput,
    /// A union selector byte is invalid.
    InvalidUnionSelector(u8),
    /// Bitfield has non-zero excess bits.
    ExcessBitsNotZero,
    /// Bitlist is missing the delimiter bit.
    MissingDelimiterBit,
    /// A container has zero variable-length fields but leftover bytes.
    AdditionalBytes { expected: usize, got: usize },
    /// `ssz_decode_fixed_vec` was called on a variable-size type.
    NotFixedSize,
}

#[cfg(feature = "std")]
impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DecodeError {}
