//! Demonstrates SSZ encoding and decoding of basic types.

use ssz::{SszDecode, SszEncode};

fn main() {
    // ── bool ──
    let val = true;
    let encoded = val.to_ssz();
    assert_eq!(encoded, [1]);
    let decoded = bool::from_ssz_bytes(&encoded).unwrap();
    println!("bool: {val} -> {encoded:02x?} -> {decoded}");

    // ── u8 ──
    let val: u8 = 255;
    let encoded = val.to_ssz();
    assert_eq!(encoded, [255]);
    let decoded = u8::from_ssz_bytes(&encoded).unwrap();
    println!("u8:   {val} -> {encoded:02x?} -> {decoded}");

    // ── u16 ──
    let val: u16 = 0x0102;
    let encoded = val.to_ssz();
    assert_eq!(encoded, [0x02, 0x01]); // little-endian
    let decoded = u16::from_ssz_bytes(&encoded).unwrap();
    println!("u16:  {val:#06x} -> {encoded:02x?} -> {decoded:#06x}");

    // ── u32 ──
    let val: u32 = 0x01020304;
    let encoded = val.to_ssz();
    assert_eq!(encoded, [0x04, 0x03, 0x02, 0x01]);
    let decoded = u32::from_ssz_bytes(&encoded).unwrap();
    println!("u32:  {val:#010x} -> {encoded:02x?} -> {decoded:#010x}");

    // ── u64 ──
    let val: u64 = 42;
    let encoded = val.to_ssz();
    assert_eq!(encoded, [42, 0, 0, 0, 0, 0, 0, 0]);
    let decoded = u64::from_ssz_bytes(&encoded).unwrap();
    println!("u64:  {val} -> {encoded:02x?} -> {decoded}");

    // ── u128 ──
    let val: u128 = 1;
    let encoded = val.to_ssz();
    assert_eq!(encoded.len(), 16);
    let decoded = u128::from_ssz_bytes(&encoded).unwrap();
    println!("u128: {val} -> ({} bytes) -> {decoded}", encoded.len());

    // ── [u8; 32] (Bytes32 / uint256) ──
    let mut val = [0u8; 32];
    val[0] = 0xAB;
    val[31] = 0xCD;
    let encoded = val.to_ssz();
    assert_eq!(encoded.len(), 32);
    let decoded = <[u8; 32]>::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, val);
    println!("[u8;32]: first={:#04x}, last={:#04x} -> (32 bytes) -> OK", val[0], val[31]);

    // ── Vec<u16> (list of fixed-size elements) ──
    let val: Vec<u16> = vec![10, 20, 30];
    let encoded = val.to_ssz();
    let decoded = Vec::<u16>::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, val);
    println!("Vec<u16>: {val:?} -> ({} bytes) -> {decoded:?}", encoded.len());

    // ── Vec<Vec<u8>> (list of variable-size elements) ──
    let val: Vec<Vec<u8>> = vec![vec![1, 2], vec![3], vec![4, 5, 6]];
    let encoded = val.to_ssz();
    let decoded = Vec::<Vec<u8>>::from_ssz_bytes(&encoded).unwrap();
    assert_eq!(decoded, val);
    println!("Vec<Vec<u8>>: {val:?} -> ({} bytes) -> {decoded:?}", encoded.len());

    // ── Error handling ──
    let err = bool::from_ssz_bytes(&[2]);
    println!("\nInvalid bool byte: {err:?}");

    let err = u32::from_ssz_bytes(&[1, 2, 3]);
    println!("Wrong u32 length:  {err:?}");

    println!("\nAll basic type examples passed.");
}
