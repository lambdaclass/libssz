//! Checks shared by several properties. Each check has its own `assert!`
//! line, so ephyra tells the failures apart and never shrinks one into
//! another.

use core::fmt::Debug;

use libssz::{SszDecode, SszEncode};

/// SSZ serialization is a bijection between values and byte strings. So a
/// decoder that accepts `bytes` must return the value whose encoding is
/// exactly `bytes`: anything else means two clients can read the same
/// message differently.
///
/// Returns whether `bytes` decoded, for `classify`.
pub fn decode_is_canonical<T>(bytes: &[u8]) -> bool
where
    T: SszEncode + SszDecode + PartialEq + Debug,
{
    let Ok(value) = T::from_ssz_bytes(bytes) else {
        return false;
    };
    let reencoded = value.to_ssz();
    assert_eq!(
        reencoded, bytes,
        "accepted non-canonical bytes; decoded as {value:?}"
    );
    true
}

/// Encoding then decoding gives the value back, and `encoded_len` predicts
/// the encoding's length.
pub fn round_trips<T>(value: &T)
where
    T: SszEncode + SszDecode + PartialEq + Debug,
{
    let bytes = value.to_ssz();
    assert_eq!(
        value.encoded_len(),
        bytes.len(),
        "encoded_len disagrees with to_ssz"
    );
    assert_eq!(
        T::from_ssz_bytes(&bytes).as_ref(),
        Ok(value),
        "decode(encode(v)) != v"
    );
}
