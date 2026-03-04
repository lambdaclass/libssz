use ssz::{SszEncode, SszDecode, DecodeError, ContainerEncoder, ContainerDecoder};

// ── bool ──

#[test]
fn bool_true_round_trip() {
    let encoded = true.to_ssz();
    assert_eq!(encoded, vec![1]);
    assert!(bool::from_ssz_bytes(&encoded).unwrap());
}

#[test]
fn bool_false_round_trip() {
    let encoded = false.to_ssz();
    assert_eq!(encoded, vec![0]);
    assert!(!bool::from_ssz_bytes(&encoded).unwrap());
}

#[test]
fn bool_invalid_byte() {
    assert_eq!(
        bool::from_ssz_bytes(&[2]),
        Err(DecodeError::InvalidBooleanByte(2))
    );
}

#[test]
fn bool_wrong_length() {
    assert_eq!(
        bool::from_ssz_bytes(&[0, 1]),
        Err(DecodeError::InvalidFixedLength { expected: 1, got: 2 })
    );
}

// ── u8 ──

#[test]
fn u8_round_trip() {
    for val in [0u8, 1, 127, 255] {
        let encoded = val.to_ssz();
        assert_eq!(encoded, vec![val]);
        assert_eq!(u8::from_ssz_bytes(&encoded).unwrap(), val);
    }
}

// ── u16 ──

#[test]
fn u16_round_trip() {
    let val: u16 = 0x0102;
    let encoded = val.to_ssz();
    assert_eq!(encoded, vec![0x02, 0x01]); // little-endian
    assert_eq!(u16::from_ssz_bytes(&encoded).unwrap(), val);
}

// ── u32 ──

#[test]
fn u32_round_trip() {
    let val: u32 = 0x01020304;
    let encoded = val.to_ssz();
    assert_eq!(encoded, vec![0x04, 0x03, 0x02, 0x01]);
    assert_eq!(u32::from_ssz_bytes(&encoded).unwrap(), val);
}

// ── u64 ──

#[test]
fn u64_round_trip() {
    let val: u64 = 0x0102030405060708;
    let encoded = val.to_ssz();
    assert_eq!(encoded, vec![0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);
    assert_eq!(u64::from_ssz_bytes(&encoded).unwrap(), val);
}

// ── u128 ──

#[test]
fn u128_round_trip() {
    let val: u128 = 1;
    let encoded = val.to_ssz();
    assert_eq!(encoded.len(), 16);
    assert_eq!(u128::from_ssz_bytes(&encoded).unwrap(), val);
}

// ── u256 ([u8; 32]) ──

#[test]
fn u256_round_trip() {
    let mut val = [0u8; 32];
    val[0] = 1;
    val[31] = 0xFF;
    let encoded = val.to_ssz();
    assert_eq!(encoded.len(), 32);
    assert_eq!(<[u8; 32]>::from_ssz_bytes(&encoded).unwrap(), val);
}

// ── Vec<u16> (fixed-element list) ──

#[test]
fn vec_u16_round_trip() {
    let val: Vec<u16> = vec![1, 2, 3];
    let encoded = val.to_ssz();
    // 3 × 2 bytes = 6 bytes, LE
    assert_eq!(encoded, vec![0x01, 0x00, 0x02, 0x00, 0x03, 0x00]);
    assert_eq!(Vec::<u16>::from_ssz_bytes(&encoded).unwrap(), val);
}

#[test]
fn vec_empty() {
    let val: Vec<u16> = vec![];
    let encoded = val.to_ssz();
    assert_eq!(encoded, vec![]);
    assert_eq!(Vec::<u16>::from_ssz_bytes(&encoded).unwrap(), val);
}

// ── Vec<Vec<u8>> (variable-element list) ──

#[test]
fn vec_of_vecs_round_trip() {
    let val: Vec<Vec<u8>> = vec![vec![1, 2], vec![3], vec![4, 5, 6]];
    let encoded = val.to_ssz();

    // 3 offsets (4 bytes each) = 12 bytes fixed part
    // offset[0] = 12, offset[1] = 14, offset[2] = 15
    // data: [1,2], [3], [4,5,6]
    let expected = vec![
        12, 0, 0, 0, // offset to [1,2]
        14, 0, 0, 0, // offset to [3]
        15, 0, 0, 0, // offset to [4,5,6]
        1, 2,        // data[0]
        3,           // data[1]
        4, 5, 6,     // data[2]
    ];
    assert_eq!(encoded, expected);
    assert_eq!(Vec::<Vec<u8>>::from_ssz_bytes(&encoded).unwrap(), val);
}

#[test]
fn vec_of_vecs_empty() {
    let val: Vec<Vec<u8>> = vec![];
    let encoded = val.to_ssz();
    assert!(encoded.is_empty());
    assert_eq!(Vec::<Vec<u8>>::from_ssz_bytes(&encoded).unwrap(), val);
}

// ── ContainerEncoder / ContainerDecoder ──

/// Simulates a container: { a: u32, b: Vec<u8>, c: u16 }
/// Fixed part: 4 (u32) + 4 (offset) + 2 (u16) = 10 bytes
#[test]
fn container_mixed_round_trip() {
    let a: u32 = 42;
    let b: Vec<u8> = vec![0xAA, 0xBB, 0xCC];
    let c: u16 = 1000;

    // Encode
    let mut encoder = ContainerEncoder::new();
    encoder.append_fixed(&a);
    encoder.append_variable(&b);
    encoder.append_fixed(&c);
    let mut buf = Vec::new();
    encoder.finalize(&mut buf);

    // Expected:
    // [42, 0, 0, 0]         a = 42 (u32 LE)
    // [10, 0, 0, 0]         offset to b's data (fixed part = 4+4+2 = 10)
    // [0xE8, 0x03]          c = 1000 (u16 LE)
    // [0xAA, 0xBB, 0xCC]    b's data
    let expected = vec![
        42, 0, 0, 0,
        10, 0, 0, 0,
        0xE8, 0x03,
        0xAA, 0xBB, 0xCC,
    ];
    assert_eq!(buf, expected);

    // Decode
    let fixed_part_len = 4 + 4 + 2; // u32 + offset + u16
    let mut decoder = ContainerDecoder::new(&buf, fixed_part_len).unwrap();
    let dec_a: u32 = decoder.decode_fixed().unwrap();
    decoder.read_variable_offset().unwrap();
    let dec_c: u16 = decoder.decode_fixed().unwrap();
    let dec_b: Vec<u8> = decoder.decode_variable().unwrap();

    assert_eq!(dec_a, a);
    assert_eq!(dec_b, b);
    assert_eq!(dec_c, c);
}

/// All-fixed container: { x: u32, y: u64 }
#[test]
fn container_all_fixed_round_trip() {
    let x: u32 = 7;
    let y: u64 = 999;

    let mut encoder = ContainerEncoder::new();
    encoder.append_fixed(&x);
    encoder.append_fixed(&y);
    let mut buf = Vec::new();
    encoder.finalize(&mut buf);

    assert_eq!(buf.len(), 4 + 8);

    let mut decoder = ContainerDecoder::new(&buf, 12).unwrap();
    let dec_x: u32 = decoder.decode_fixed().unwrap();
    let dec_y: u64 = decoder.decode_fixed().unwrap();
    decoder.finish_fixed().unwrap();

    assert_eq!(dec_x, x);
    assert_eq!(dec_y, y);
}

/// Container with extra bytes should fail.
#[test]
fn container_extra_bytes() {
    let mut buf = vec![0u8; 16]; // 12-byte container + 4 extra bytes
    buf[0] = 7; // x = 7

    let mut decoder = ContainerDecoder::new(&buf, 12).unwrap();
    let _x: u32 = decoder.decode_fixed().unwrap();
    let _y: u64 = decoder.decode_fixed().unwrap();
    assert!(decoder.finish_fixed().is_err());
}

// ── encoded_len ──

#[test]
fn encoded_len_matches_actual() {
    let val: Vec<Vec<u8>> = vec![vec![1, 2, 3], vec![], vec![4]];
    assert_eq!(val.encoded_len(), val.to_ssz().len());

    let fixed: Vec<u32> = vec![1, 2, 3, 4, 5];
    assert_eq!(fixed.encoded_len(), fixed.to_ssz().len());

    assert_eq!(true.encoded_len(), 1);
    assert_eq!(42u64.encoded_len(), 8);
}

// ── Error cases ──

#[test]
fn u32_wrong_length() {
    assert_eq!(
        u32::from_ssz_bytes(&[1, 2, 3]),
        Err(DecodeError::InvalidFixedLength { expected: 4, got: 3 })
    );
}

#[test]
fn vec_u32_not_divisible() {
    // 5 bytes is not divisible by 4
    assert!(Vec::<u32>::from_ssz_bytes(&[1, 2, 3, 4, 5]).is_err());
}
