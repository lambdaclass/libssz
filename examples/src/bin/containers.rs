//! Demonstrates manual container encoding/decoding using ContainerEncoder and ContainerDecoder.
//!
//! Once ssz-derive is ready, you can replace the manual encode/decode with:
//!   #[derive(SszEncode, SszDecode)]
//!   struct BeaconBlockHeader { ... }

use libssz::{ContainerDecoder, ContainerEncoder};

fn main() {
    // ── All-fixed container ──
    // Simulates: struct Point { x: u32, y: u32 }
    println!("=== All-fixed container: Point {{ x: u32, y: u32 }} ===");
    {
        let x: u32 = 100;
        let y: u32 = 200;

        // Encode
        let mut buf = Vec::new();
        let mut encoder = ContainerEncoder::new(&mut buf, 4 + 4);
        encoder.append_fixed(&x);
        encoder.append_fixed(&y);
        encoder.finalize();

        println!("  Encoded: {buf:02x?} ({} bytes)", buf.len());
        assert_eq!(buf.len(), 8); // 4 + 4

        // Decode
        let fixed_part_len = 4 + 4;
        let mut decoder = ContainerDecoder::new(&buf, fixed_part_len).unwrap();
        let dec_x: u32 = decoder.decode_fixed().unwrap();
        let dec_y: u32 = decoder.decode_fixed().unwrap();
        decoder.finish_fixed().unwrap(); // verify no trailing bytes

        assert_eq!((dec_x, dec_y), (x, y));
        println!("  Decoded: x={dec_x}, y={dec_y}");
    }

    // ── Mixed fixed/variable container ──
    // Simulates: struct Transfer { sender: [u8; 20], amount: u64, memo: Vec<u8> }
    println!(
        "\n=== Mixed container: Transfer {{ sender: [u8;20], amount: u64, memo: Vec<u8> }} ==="
    );
    {
        let sender = [0xABu8; 20];
        let amount: u64 = 1_000_000;
        let memo: Vec<u8> = b"hello".to_vec();

        // Encode
        let mut buf = Vec::new();
        let mut encoder = ContainerEncoder::new(&mut buf, 20 + 8 + 4);
        encoder.append_fixed(&sender); // 20 bytes
        encoder.append_fixed(&amount); // 8 bytes
        encoder.append_variable(&memo); // 4-byte offset + data
        encoder.finalize();

        // Fixed part: 20 (sender) + 8 (amount) + 4 (offset) = 32 bytes
        // Variable part: 5 bytes ("hello")
        // Total: 37 bytes
        println!("  Encoded: {} bytes", buf.len());
        println!("  Fixed part (32 bytes): {:02x?}", &buf[..32]);
        println!("  Variable part (5 bytes): {:02x?}", &buf[32..]);
        assert_eq!(buf.len(), 37);

        // Decode
        let fixed_part_len = 20 + 8 + 4;
        let mut decoder = ContainerDecoder::new(&buf, fixed_part_len).unwrap();
        let dec_sender: [u8; 20] = decoder.decode_fixed().unwrap();
        let dec_amount: u64 = decoder.decode_fixed().unwrap();
        decoder.read_variable_offset().unwrap();
        let dec_memo: Vec<u8> = decoder.decode_variable().unwrap();

        assert_eq!(dec_sender, sender);
        assert_eq!(dec_amount, amount);
        assert_eq!(dec_memo, memo);
        println!(
            "  Decoded: sender={:02x?}..., amount={dec_amount}, memo={:?}",
            &dec_sender[..4],
            String::from_utf8_lossy(&dec_memo)
        );
    }

    // ── Multiple variable fields ──
    // Simulates: struct Message { from: Vec<u8>, to: Vec<u8>, tag: u16 }
    println!(
        "\n=== Multiple variable fields: Message {{ from: Vec<u8>, to: Vec<u8>, tag: u16 }} ==="
    );
    {
        let from: Vec<u8> = vec![1, 2, 3];
        let to: Vec<u8> = vec![4, 5];
        let tag: u16 = 42;

        // Encode -- fields in declaration order
        let mut buf = Vec::new();
        let mut encoder = ContainerEncoder::new(&mut buf, 4 + 4 + 2);
        encoder.append_variable(&from); // 4-byte offset
        encoder.append_variable(&to); // 4-byte offset
        encoder.append_fixed(&tag); // 2 bytes
        encoder.finalize();

        // Fixed part: 4 (offset) + 4 (offset) + 2 (tag) = 10 bytes
        // Variable part: 3 (from) + 2 (to) = 5 bytes
        println!("  Encoded: {} bytes", buf.len());
        assert_eq!(buf.len(), 15);

        // Decode
        let fixed_part_len = 4 + 4 + 2;
        let mut decoder = ContainerDecoder::new(&buf, fixed_part_len).unwrap();
        decoder.read_variable_offset().unwrap();
        decoder.read_variable_offset().unwrap();
        let dec_tag: u16 = decoder.decode_fixed().unwrap();
        let dec_from: Vec<u8> = decoder.decode_variable().unwrap();
        let dec_to: Vec<u8> = decoder.decode_variable().unwrap();

        assert_eq!(dec_from, from);
        assert_eq!(dec_to, to);
        assert_eq!(dec_tag, tag);
        println!("  Decoded: from={dec_from:?}, to={dec_to:?}, tag={dec_tag}");
    }

    println!("\nAll container examples passed.");
}
