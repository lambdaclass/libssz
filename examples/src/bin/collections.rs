//! Placeholder: demonstrates bounded SSZ collection types.
//!
//! This example will compile once libssz-types is fully implemented.
//! Uncomment the libssz-types dependency in examples/Cargo.toml to use it.
//!
//! ```rust,ignore
//! use libssz::{SszEncode, SszDecode};
//! use libssz_types::SszVector;
//!
//! // Vector[uint64, 4] -- exactly 4 elements
//! let v: SszVector<u64, 4> = SszVector::try_from(vec![10, 20, 30, 40]).unwrap();
//! let encoded = v.to_ssz();
//! let decoded = SszVector::<u64, 4>::from_ssz_bytes(&encoded).unwrap();
//! assert_eq!(v, decoded);
//!
//! // List[uint16, 1024] -- up to 1024 elements
//! let list: SszList<u16, 1024> = SszList::try_from(vec![1, 2, 3]).unwrap();
//! let encoded = list.to_ssz();
//! let decoded = SszList::<u16, 1024>::from_ssz_bytes(&encoded).unwrap();
//! assert_eq!(list, decoded);
//!
//! // Bitvector[8] -- exactly 8 bits
//! let bv = Bitvector::<8>::from_bytes(&[0b10101010]).unwrap();
//! assert!(bv.get(1));
//! assert!(!bv.get(0));
//!
//! // Bitlist[256] -- up to 256 bits
//! let bl = Bitlist::<256>::from_raw_bytes(&[0b00000101, 0b00000001]).unwrap(); // 5 bits
//! ```

fn main() {
    println!("This is a placeholder example for libssz-types bounded collections.");
    println!("See the doc comments in this file for planned API usage.");
    println!("Enable by uncommenting libssz-types in examples/Cargo.toml.");
}
