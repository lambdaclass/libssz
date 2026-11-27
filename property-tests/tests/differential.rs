//! libssz against Lighthouse (`ethereum_ssz`, `ssz_types`, `tree_hash`) and
//! ssz_rs on the same edited encodings as `tests/encoding.rs`.
//!
//! For every input, libssz and Lighthouse must agree on whether the bytes
//! are valid. ssz_rs is a weaker witness: it panics on some malformed inputs
//! and accepts some invalid ones (see [`ssz_rs_decode`] and
//! `decoders_agree`), so when it alone disagrees the input is counted, not
//! failed. When all three accept, the re-encodings and hash tree roots must
//! agree. Unedited encodings are among the inputs, so this also compares the
//! encodings and roots of valid values.
//!
//! Progressive types are left out: neither library implements them.

use core::fmt::Debug;

use ephyra::{any, classify, gens, signature};
use libssz::{SszDecode, SszEncode};
use libssz_merkle::{HashTreeRoot, Sha2Hasher};
use libssz_types::{SszBitlist, SszBitvector};
use property_tests::edits::edited_encodings;
use property_tests::recipes::{
    bitlist, bitvector, ChoiceRecipe, FixedRecipe, InnerRecipe, OuterRecipe, ShapesRecipe,
    TaggedRecipe,
};
use property_tests::types::{Choice, Fixed, Inner, Outer, Shapes, Tagged};

/// The test types, declared with Lighthouse's derives.
mod lighthouse {
    // The derives name `ssz::...`, Lighthouse's own name for ethereum_ssz.
    use alloy_primitives::U128;
    use lighthouse_ssz as ssz;
    use lighthouse_ssz_derive::{Decode, Encode};
    use lighthouse_ssz_types::{BitList, BitVector, FixedVector, VariableList};
    use tree_hash::{Hash256, PackedEncoding, TreeHash, TreeHashType};
    use tree_hash_derive::TreeHash;
    use typenum::{U11, U16, U2, U20, U3, U4, U40, U5, U6, U7, U9};

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    pub struct Inner {
        pub a: u16,
        pub xs: VariableList<u8, U7>,
    }

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    pub struct Outer {
        pub x: u32,
        pub inners: VariableList<Inner, U5>,
        pub tail: VariableList<u64, U3>,
        pub flag: bool,
        pub bits: BitList<U20>,
        pub mask: BitVector<U11>,
    }

    /// Lighthouse's union derive needs exactly one field per variant, so the
    /// empty variant holds this zero-byte value. Its impls below follow the
    /// spec for the `None` variant (empty body, zero root); the comparison
    /// for selector 0 therefore exercises this code, not Lighthouse's.
    #[derive(Clone, Debug, PartialEq)]
    pub struct Empty;

    impl ssz::Encode for Empty {
        fn is_ssz_fixed_len() -> bool {
            true
        }
        fn ssz_fixed_len() -> usize {
            0
        }
        fn ssz_append(&self, _buf: &mut Vec<u8>) {}
        fn ssz_bytes_len(&self) -> usize {
            0
        }
    }

    impl ssz::Decode for Empty {
        fn is_ssz_fixed_len() -> bool {
            true
        }
        fn ssz_fixed_len() -> usize {
            0
        }
        fn from_ssz_bytes(bytes: &[u8]) -> Result<Self, ssz::DecodeError> {
            if bytes.is_empty() {
                Ok(Empty)
            } else {
                Err(ssz::DecodeError::BytesInvalid(format!(
                    "{} bytes after the None selector",
                    bytes.len()
                )))
            }
        }
    }

    impl TreeHash for Empty {
        fn tree_hash_type() -> TreeHashType {
            TreeHashType::Container
        }
        fn tree_hash_packed_encoding(&self) -> PackedEncoding {
            unreachable!("a container is never packed")
        }
        fn tree_hash_packing_factor() -> usize {
            unreachable!("a container is never packed")
        }
        fn tree_hash_root(&self) -> Hash256 {
            Hash256::ZERO
        }
    }

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    #[ssz(enum_behaviour = "union")]
    #[tree_hash(enum_behaviour = "union")]
    pub enum Choice {
        Nothing(Empty),
        Number(u64),
        Bytes(VariableList<u8, U40>),
        Nested(Inner),
    }

    pub type Bits = BitList<U20>;
    pub type Mask = BitVector<U11>;
    pub type AlignedMask = BitVector<U16>;

    // libssz's transparent `Slot` and `Wrapped` are spelled as their field:
    // that is what transparent means.

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    pub struct Fixed {
        pub a: u32,
        pub root: [u8; 32],
        pub b: U128,
        pub addr: [u8; 20],
        pub slot: u64,
        pub flag: bool,
    }

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    #[ssz(enum_behaviour = "union")]
    #[tree_hash(enum_behaviour = "union")]
    pub enum Tagged {
        Nothing(Empty),
        Word(u32),
        Record(Fixed),
        Records(FixedVector<Fixed, U2>),
    }

    #[derive(Clone, Debug, PartialEq, Encode, Decode, TreeHash)]
    pub struct Shapes {
        pub record: Fixed,
        pub records: VariableList<Fixed, U4>,
        pub pair: FixedVector<Fixed, U2>,
        pub words: FixedVector<u32, U5>,
        pub wide: VariableList<U128, U3>,
        pub roots: VariableList<[u8; 32], U3>,
        pub addrs: VariableList<[u8; 20], U3>,
        pub slot: u64,
        pub slots: VariableList<u64, U6>,
        pub wrapped: VariableList<u16, U9>,
        pub tagged: Tagged,
        pub inner: Inner,
    }
}

/// The test types, declared with ssz_rs's derive.
mod ssz_rs_types {
    use ssz_rs::prelude::*;

    #[derive(Clone, Debug, Default, PartialEq, SimpleSerialize)]
    pub struct Inner {
        pub a: u16,
        pub xs: List<u8, 7>,
    }

    #[derive(Clone, Debug, Default, PartialEq, SimpleSerialize)]
    pub struct Outer {
        pub x: u32,
        pub inners: List<Inner, 5>,
        pub tail: List<u64, 3>,
        pub flag: bool,
        pub bits: Bitlist<20>,
        pub mask: Bitvector<11>,
    }

    /// ssz_rs spells the empty variant `None`; it must come first.
    #[derive(Clone, Debug, Default, PartialEq, SimpleSerialize)]
    pub enum Choice {
        #[default]
        None,
        Number(u64),
        Bytes(List<u8, 40>),
        Nested(Inner),
    }

    pub type Bits = Bitlist<20>;
    pub type Mask = Bitvector<11>;
    pub type AlignedMask = Bitvector<16>;

    #[derive(Clone, Debug, Default, PartialEq, SimpleSerialize)]
    pub struct Fixed {
        pub a: u32,
        pub root: Vector<u8, 32>,
        pub b: u128,
        pub addr: Vector<u8, 20>,
        pub slot: u64,
        pub flag: bool,
    }

    #[derive(Clone, Debug, Default, PartialEq, SimpleSerialize)]
    pub enum Tagged {
        #[default]
        None,
        Word(u32),
        Record(Fixed),
        Records(Vector<Fixed, 2>),
    }

    #[derive(Clone, Debug, Default, PartialEq, SimpleSerialize)]
    pub struct Shapes {
        pub record: Fixed,
        pub records: List<Fixed, 4>,
        pub pair: Vector<Fixed, 2>,
        pub words: Vector<u32, 5>,
        pub wide: List<u128, 3>,
        pub roots: List<Vector<u8, 32>, 3>,
        pub addrs: List<Vector<u8, 20>, 3>,
        pub slot: u64,
        pub slots: List<u64, 6>,
        pub wrapped: List<u16, 9>,
        pub tagged: Tagged,
        pub inner: Inner,
    }
}

/// Decode `bytes` with all three libraries and compare.
fn decoders_agree<Ours, Lh, Rs>(bytes: &[u8])
where
    Ours: SszEncode + SszDecode + HashTreeRoot + Debug,
    Lh: lighthouse_ssz::Encode + lighthouse_ssz::Decode + tree_hash::TreeHash + Debug,
    Rs: ssz_rs::SimpleSerialize + Clone + Debug,
{
    let ours = Ours::from_ssz_bytes(bytes);
    let lh = Lh::from_ssz_bytes(bytes);
    let rs = ssz_rs_decode::<Rs>(bytes);
    classify(ours.is_ok(), "accepted by libssz");
    classify(rs.is_none(), "ssz_rs panicked");

    if ours.is_ok() != lh.is_ok() {
        signature(if ours.is_ok() {
            "only libssz accepts (vs Lighthouse)"
        } else {
            "Lighthouse accepts what libssz rejects"
        });
    }
    assert_eq!(
        ours.is_ok(),
        lh.is_ok(),
        "libssz and Lighthouse disagree on validity: libssz {ours:?}, Lighthouse {lh:?}"
    );

    // libssz and Lighthouse agree from here on. If ssz_rs disagrees with
    // both, it is outvoted: ssz_rs 0.9.0 is known to accept some invalid
    // inputs, e.g. a list of variable-size items whose body is `[0, 0, 0, 0]`
    // (first offset 0) decodes as an empty list. The label counts these.
    let rs_dissents = rs.as_ref().is_some_and(|rs| rs.is_ok() != ours.is_ok());
    classify(rs_dissents, "ssz_rs alone disagrees on validity");

    let (Ok(ours), Ok(lh)) = (ours, lh) else {
        return;
    };
    let ours_bytes = ours.to_ssz();
    let ours_root = ours.hash_tree_root(&Sha2Hasher);
    assert_eq!(
        lh.as_ssz_bytes(),
        ours_bytes,
        "Lighthouse re-encodes differently"
    );
    assert_eq!(lh.tree_hash_root().0, ours_root, "Lighthouse root differs");

    let Some(Ok(rs)) = rs else {
        return;
    };
    let rs_bytes = ssz_rs::serialize(&rs).expect("ssz_rs encodes what it decoded");
    assert_eq!(rs_bytes, ours_bytes, "ssz_rs re-encodes differently");
    let rs_node = rs
        .clone()
        .hash_tree_root()
        .expect("ssz_rs hashes what it decoded");
    let rs_root: [u8; 32] = rs_node.as_ref().try_into().expect("32-byte node");
    assert_eq!(rs_root, ours_root, "ssz_rs root differs");
}

/// Decode with ssz_rs, or `None` when ssz_rs panics.
///
/// ssz_rs 0.9.0 (the latest release) panics on some malformed inputs
/// instead of returning an error: its list decoder slices
/// `encoding[start..end]` after checking only `start <= end`
/// (`src/de.rs:127`), and its container derive subtracts offsets before
/// validating them. Those are ssz_rs bugs, not libssz ones, so such inputs
/// get no verdict from ssz_rs; Lighthouse still checks them. The
/// `ssz_rs panicked` label in the report counts them.
fn ssz_rs_decode<Rs: ssz_rs::SimpleSerialize>(
    bytes: &[u8],
) -> Option<Result<Rs, ssz_rs::DeserializeError>> {
    std::panic::catch_unwind(|| ssz_rs::deserialize::<Rs>(bytes)).ok()
}

#[ephyra::test(gen = edited_encodings(any::<InnerRecipe>(), |r| r.build().to_ssz()))]
fn inner_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<Inner, lighthouse::Inner, ssz_rs_types::Inner>(&bytes);
}

#[ephyra::test(gen = edited_encodings(any::<OuterRecipe>(), |r| r.build().to_ssz()), tests = 3_000)]
fn outer_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<Outer, lighthouse::Outer, ssz_rs_types::Outer>(&bytes);
}

#[ephyra::test(gen = edited_encodings(any::<ChoiceRecipe>(), |r| r.build().to_ssz()))]
fn choice_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<Choice, lighthouse::Choice, ssz_rs_types::Choice>(&bytes);
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::bool()).len(0..=20),
    |bits| bitlist::<20>(bits).to_ssz()
))]
fn bitlist_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<SszBitlist<20>, lighthouse::Bits, ssz_rs_types::Bits>(&bytes);
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::bool()).len(11..=11),
    |bits| bitvector::<11>(bits).to_ssz()
))]
fn bitvector_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<SszBitvector<11>, lighthouse::Mask, ssz_rs_types::Mask>(&bytes);
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::bool()).len(16..=16),
    |bits| bitvector::<16>(bits).to_ssz()
))]
fn byte_aligned_bitvector_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<SszBitvector<16>, lighthouse::AlignedMask, ssz_rs_types::AlignedMask>(&bytes);
}

#[ephyra::test(gen = edited_encodings(any::<FixedRecipe>(), |r| r.build().to_ssz()))]
fn fixed_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<Fixed, lighthouse::Fixed, ssz_rs_types::Fixed>(&bytes);
}

#[ephyra::test(gen = edited_encodings(any::<TaggedRecipe>(), |r| r.build().to_ssz()))]
fn tagged_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<Tagged, lighthouse::Tagged, ssz_rs_types::Tagged>(&bytes);
}

#[ephyra::test(gen = edited_encodings(any::<ShapesRecipe>(), |r| r.build().to_ssz()), tests = 3_000)]
fn shapes_decoders_agree(bytes: Vec<u8>) {
    decoders_agree::<Shapes, lighthouse::Shapes, ssz_rs_types::Shapes>(&bytes);
}
