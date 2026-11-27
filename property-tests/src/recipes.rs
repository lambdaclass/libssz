//! Generated, shrinkable descriptions of the values in [`crate::types`].
//!
//! Each recipe has `build`, which constructs the libssz value, and
//! `reference_root`, which computes its hash tree root from the recipe alone
//! through [`crate::reference`]. Collection lengths never exceed the type's
//! limit, so `build` cannot fail.

use ephyra::{any, gens};
use libssz_types::{
    ProgressiveBitlist, ProgressiveList, SszBitlist, SszBitvector, SszList, SszVector,
};

use crate::reference::{self as r, Chunk};
use crate::types::{Choice, Fixed, Inner, Outer, Shapes, Slot, Sparse, Tagged, Wrapped, Wrapper};

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub struct InnerRecipe {
    #[ephyra(gen = gens::int(0u16..=u16::MAX))]
    pub a: u16,
    #[ephyra(gen = gens::vec(gens::int(0u8..=255)).len(0..=7))]
    pub xs: Vec<u8>,
}

impl InnerRecipe {
    pub fn build(&self) -> Inner {
        Inner {
            a: self.a,
            xs: SszList::try_from(self.xs.clone()).expect("test bug: xs over limit"),
        }
    }

    pub fn reference_root(&self) -> Chunk {
        let fields = [
            r::basic_root(&self.a.to_le_bytes()),
            r::basic_list_root(&self.xs, self.xs.len(), 7, 1),
        ];
        r::merkleize(&fields, fields.len())
    }
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub struct OuterRecipe {
    #[ephyra(gen = gens::int(0u32..=u32::MAX))]
    pub x: u32,
    #[ephyra(gen = gens::vec(any::<InnerRecipe>()).len(0..=5))]
    pub inners: Vec<InnerRecipe>,
    #[ephyra(gen = gens::vec(gens::int(0u64..=u64::MAX)).len(0..=3))]
    pub tail: Vec<u64>,
    #[ephyra(gen = gens::bool())]
    pub flag: bool,
    #[ephyra(gen = gens::vec(gens::bool()).len(0..=20))]
    pub bits: Vec<bool>,
    #[ephyra(gen = gens::vec(gens::bool()).len(11..=11))]
    pub mask: Vec<bool>,
}

impl OuterRecipe {
    pub fn build(&self) -> Outer {
        let inners: Vec<Inner> = self.inners.iter().map(InnerRecipe::build).collect();
        let mut mask = SszBitvector::<11>::new();
        for (i, bit) in self.mask.iter().enumerate() {
            mask.set(i, *bit).expect("test bug: mask index");
        }
        Outer {
            x: self.x,
            inners: SszList::try_from(inners).expect("test bug: inners over limit"),
            tail: SszList::try_from(self.tail.clone()).expect("test bug: tail over limit"),
            flag: self.flag,
            bits: SszBitlist::try_from(self.bits.clone()).expect("test bug: bits over limit"),
            mask,
        }
    }

    pub fn reference_root(&self) -> Chunk {
        let inner_roots: Vec<Chunk> = self
            .inners
            .iter()
            .map(InnerRecipe::reference_root)
            .collect();
        let tail_bytes: Vec<u8> = self.tail.iter().flat_map(|v| v.to_le_bytes()).collect();
        let fields = [
            r::basic_root(&self.x.to_le_bytes()),
            r::mix_in_length(&r::merkleize(&inner_roots, 5), inner_roots.len()),
            r::basic_list_root(&tail_bytes, self.tail.len(), 3, 8),
            r::basic_root(&[self.flag as u8]),
            r::bitlist_root(&self.bits, 20),
            r::bitvector_root(&self.mask),
        ];
        r::merkleize(&fields, fields.len())
    }
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub enum ChoiceRecipe {
    Nothing,
    Number(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
    Bytes(#[ephyra(gen = gens::vec(gens::int(0u8..=255)).len(0..=40))] Vec<u8>),
    Nested(#[ephyra(gen = any::<InnerRecipe>())] InnerRecipe),
}

impl ChoiceRecipe {
    pub fn build(&self) -> Choice {
        match self {
            ChoiceRecipe::Nothing => Choice::Nothing,
            ChoiceRecipe::Number(n) => Choice::Number(*n),
            ChoiceRecipe::Bytes(b) => {
                Choice::Bytes(SszList::try_from(b.clone()).expect("test bug: bytes over limit"))
            }
            ChoiceRecipe::Nested(inner) => Choice::Nested(inner.build()),
        }
    }

    pub fn reference_root(&self) -> Chunk {
        match self {
            ChoiceRecipe::Nothing => r::mix_in_selector(&r::ZERO, 0),
            ChoiceRecipe::Number(n) => r::mix_in_selector(&r::basic_root(&n.to_le_bytes()), 1),
            ChoiceRecipe::Bytes(b) => r::mix_in_selector(&r::basic_list_root(b, b.len(), 40, 1), 2),
            ChoiceRecipe::Nested(inner) => r::mix_in_selector(&inner.reference_root(), 3),
        }
    }
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub struct SparseRecipe {
    #[ephyra(gen = gens::int(0u32..=u32::MAX))]
    pub a: u32,
    /// Up to 200 `u16`s span 13 chunks, past the 1- and 4-leaf subtrees.
    #[ephyra(gen = gens::vec(gens::int(0u16..=u16::MAX)).len(0..=200))]
    pub items: Vec<u16>,
    /// Up to 600 bits span 3 chunks.
    #[ephyra(gen = gens::vec(gens::bool()).len(0..=600))]
    pub bits: Vec<bool>,
}

impl SparseRecipe {
    pub fn build(&self) -> Sparse {
        let mut bits = ProgressiveBitlist::new();
        for bit in &self.bits {
            bits.push(*bit);
        }
        Sparse {
            a: self.a,
            items: ProgressiveList::from(self.items.clone()),
            bits,
        }
    }

    pub fn reference_root(&self) -> Chunk {
        let item_bytes: Vec<u8> = self.items.iter().flat_map(|v| v.to_le_bytes()).collect();
        // active_fields = [1, 0, 1, 1]: the inactive slot is a zero chunk.
        let chunks = [
            r::basic_root(&self.a.to_le_bytes()),
            r::ZERO,
            r::progressive_basic_list_root(&item_bytes, self.items.len()),
            r::progressive_bitlist_root(&self.bits),
        ];
        let root = r::merkleize_progressive(&chunks);
        r::mix_in_active_fields(&root, &[true, false, true, true])
    }
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub struct WrapperRecipe {
    #[ephyra(gen = gens::vec(any::<ChoiceRecipe>()).len(0..=4))]
    pub choices: Vec<ChoiceRecipe>,
    #[ephyra(gen = any::<SparseRecipe>())]
    pub sparse: SparseRecipe,
    #[ephyra(gen = gens::vec(any::<InnerRecipe>()).len(2..=2))]
    pub pair: Vec<InnerRecipe>,
}

impl WrapperRecipe {
    pub fn build(&self) -> Wrapper {
        let choices: Vec<Choice> = self.choices.iter().map(ChoiceRecipe::build).collect();
        let pair: Vec<Inner> = self.pair.iter().map(InnerRecipe::build).collect();
        Wrapper {
            choices: SszList::try_from(choices).expect("test bug: choices over limit"),
            sparse: self.sparse.build(),
            pair: SszVector::try_from(pair).expect("test bug: pair length"),
        }
    }

    pub fn reference_root(&self) -> Chunk {
        let choice_roots: Vec<Chunk> = self
            .choices
            .iter()
            .map(ChoiceRecipe::reference_root)
            .collect();
        let pair_roots: Vec<Chunk> = self.pair.iter().map(InnerRecipe::reference_root).collect();
        let fields = [
            r::mix_in_length(&r::merkleize(&choice_roots, 4), choice_roots.len()),
            self.sparse.reference_root(),
            r::merkleize(&pair_roots, 2),
        ];
        r::merkleize(&fields, fields.len())
    }
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub struct FixedRecipe {
    #[ephyra(gen = gens::int(0u32..=u32::MAX))]
    pub a: u32,
    #[ephyra(gen = gens::vec(gens::int(0u8..=255)).len(32..=32))]
    pub root: Vec<u8>,
    /// ephyra has no `u128` generator; see [`u128_from`].
    #[ephyra(gen = (gens::int(0u64..=u64::MAX), gens::int(0u64..=u64::MAX)))]
    pub b: (u64, u64),
    #[ephyra(gen = gens::vec(gens::int(0u8..=255)).len(20..=20))]
    pub addr: Vec<u8>,
    #[ephyra(gen = gens::int(0u64..=u64::MAX))]
    pub slot: u64,
    #[ephyra(gen = gens::bool())]
    pub flag: bool,
}

impl FixedRecipe {
    pub fn build(&self) -> Fixed {
        Fixed {
            a: self.a,
            root: self.root.clone().try_into().expect("test bug: root length"),
            b: u128_from(self.b),
            addr: self.addr.clone().try_into().expect("test bug: addr length"),
            slot: Slot(self.slot),
            flag: self.flag,
        }
    }

    pub fn reference_root(&self) -> Chunk {
        let fields = [
            r::basic_root(&self.a.to_le_bytes()),
            r::byte_vector_root(&self.root),
            r::basic_root(&u128_from(self.b).to_le_bytes()),
            r::byte_vector_root(&self.addr),
            r::basic_root(&self.slot.to_le_bytes()),
            r::basic_root(&[self.flag as u8]),
        ];
        r::merkleize(&fields, fields.len())
    }
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub enum TaggedRecipe {
    Nothing,
    Word(#[ephyra(gen = gens::int(0u32..=u32::MAX))] u32),
    Record(#[ephyra(gen = any::<FixedRecipe>())] FixedRecipe),
    Records(#[ephyra(gen = gens::vec(any::<FixedRecipe>()).len(2..=2))] Vec<FixedRecipe>),
}

impl TaggedRecipe {
    pub fn build(&self) -> Tagged {
        match self {
            TaggedRecipe::Nothing => Tagged::Nothing,
            TaggedRecipe::Word(w) => Tagged::Word(*w),
            TaggedRecipe::Record(f) => Tagged::Record(f.build()),
            TaggedRecipe::Records(fs) => Tagged::Records(
                SszVector::try_from(fs.iter().map(FixedRecipe::build).collect::<Vec<_>>())
                    .expect("test bug: records length"),
            ),
        }
    }

    pub fn reference_root(&self) -> Chunk {
        match self {
            TaggedRecipe::Nothing => r::mix_in_selector(&r::ZERO, 0),
            TaggedRecipe::Word(w) => r::mix_in_selector(&r::basic_root(&w.to_le_bytes()), 1),
            TaggedRecipe::Record(f) => r::mix_in_selector(&f.reference_root(), 2),
            TaggedRecipe::Records(fs) => {
                let roots: Vec<Chunk> = fs.iter().map(FixedRecipe::reference_root).collect();
                r::mix_in_selector(&r::composite_vector_root(&roots), 3)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
pub struct ShapesRecipe {
    #[ephyra(gen = any::<FixedRecipe>())]
    pub record: FixedRecipe,
    #[ephyra(gen = gens::vec(any::<FixedRecipe>()).len(0..=4))]
    pub records: Vec<FixedRecipe>,
    #[ephyra(gen = gens::vec(any::<FixedRecipe>()).len(2..=2))]
    pub pair: Vec<FixedRecipe>,
    #[ephyra(gen = gens::vec(gens::int(0u32..=u32::MAX)).len(5..=5))]
    pub words: Vec<u32>,
    #[ephyra(gen = gens::vec((gens::int(0u64..=u64::MAX), gens::int(0u64..=u64::MAX))).len(0..=3))]
    pub wide: Vec<(u64, u64)>,
    #[ephyra(gen = gens::vec(gens::vec(gens::int(0u8..=255)).len(32..=32)).len(0..=3))]
    pub roots: Vec<Vec<u8>>,
    #[ephyra(gen = gens::vec(gens::vec(gens::int(0u8..=255)).len(20..=20)).len(0..=3))]
    pub addrs: Vec<Vec<u8>>,
    #[ephyra(gen = gens::int(0u64..=u64::MAX))]
    pub slot: u64,
    #[ephyra(gen = gens::vec(gens::int(0u64..=u64::MAX)).len(0..=6))]
    pub slots: Vec<u64>,
    #[ephyra(gen = gens::vec(gens::int(0u16..=u16::MAX)).len(0..=9))]
    pub wrapped: Vec<u16>,
    #[ephyra(gen = any::<TaggedRecipe>())]
    pub tagged: TaggedRecipe,
    #[ephyra(gen = any::<InnerRecipe>())]
    pub inner: InnerRecipe,
}

impl ShapesRecipe {
    pub fn build(&self) -> Shapes {
        let records: Vec<Fixed> = self.records.iter().map(FixedRecipe::build).collect();
        let pair: Vec<Fixed> = self.pair.iter().map(FixedRecipe::build).collect();
        let roots: Vec<[u8; 32]> = self
            .roots
            .iter()
            .map(|b| b.clone().try_into().expect("test bug: root length"))
            .collect();
        let addrs: Vec<[u8; 20]> = self
            .addrs
            .iter()
            .map(|b| b.clone().try_into().expect("test bug: addr length"))
            .collect();
        Shapes {
            record: self.record.build(),
            records: SszList::try_from(records).expect("test bug: records over limit"),
            pair: SszVector::try_from(pair).expect("test bug: pair length"),
            words: SszVector::try_from(self.words.clone()).expect("test bug: words length"),
            wide: SszList::try_from(self.wide.iter().copied().map(u128_from).collect::<Vec<_>>())
                .expect("test bug: wide over limit"),
            roots: SszList::try_from(roots).expect("test bug: roots over limit"),
            addrs: SszList::try_from(addrs).expect("test bug: addrs over limit"),
            slot: Slot(self.slot),
            slots: SszList::try_from(self.slots.iter().copied().map(Slot).collect::<Vec<_>>())
                .expect("test bug: slots over limit"),
            wrapped: Wrapped(
                SszList::try_from(self.wrapped.clone()).expect("test bug: wrapped over limit"),
            ),
            tagged: self.tagged.build(),
            inner: self.inner.build(),
        }
    }

    pub fn reference_root(&self) -> Chunk {
        let record_roots: Vec<Chunk> = self
            .records
            .iter()
            .map(FixedRecipe::reference_root)
            .collect();
        let pair_roots: Vec<Chunk> = self.pair.iter().map(FixedRecipe::reference_root).collect();
        let words: Vec<u8> = self.words.iter().flat_map(|v| v.to_le_bytes()).collect();
        let wide: Vec<u8> = self
            .wide
            .iter()
            .flat_map(|v| u128_from(*v).to_le_bytes())
            .collect();
        let root_roots: Vec<Chunk> = self.roots.iter().map(|b| r::byte_vector_root(b)).collect();
        let addr_roots: Vec<Chunk> = self.addrs.iter().map(|b| r::byte_vector_root(b)).collect();
        let slots: Vec<u8> = self.slots.iter().flat_map(|v| v.to_le_bytes()).collect();
        let wrapped: Vec<u8> = self.wrapped.iter().flat_map(|v| v.to_le_bytes()).collect();
        let fields = [
            self.record.reference_root(),
            r::composite_list_root(&record_roots, 4),
            r::composite_vector_root(&pair_roots),
            r::basic_vector_root(&words, self.words.len(), 4),
            r::basic_list_root(&wide, self.wide.len(), 3, 16),
            // `[u8; N]` is `Vector[byte, N]`, a composite type: one root
            // per element, not packed.
            r::composite_list_root(&root_roots, 3),
            r::composite_list_root(&addr_roots, 3),
            r::basic_root(&self.slot.to_le_bytes()),
            // Transparent wrappers of `u64` pack like `u64`s.
            r::basic_list_root(&slots, self.slots.len(), 6, 8),
            r::basic_list_root(&wrapped, self.wrapped.len(), 9, 2),
            self.tagged.reference_root(),
            self.inner.reference_root(),
        ];
        r::merkleize(&fields, fields.len())
    }
}

/// A `u128` from its high and low halves.
pub fn u128_from((high, low): (u64, u64)) -> u128 {
    (u128::from(high) << 64) | u128::from(low)
}

/// The standalone bitfields of the properties, built from plain bits.
pub fn bitlist<const N: usize>(bits: &[bool]) -> SszBitlist<N> {
    SszBitlist::try_from(bits.to_vec()).expect("test bug: bits over limit")
}

pub fn bitvector<const N: usize>(bits: &[bool]) -> SszBitvector<N> {
    assert_eq!(bits.len(), N, "test bug: bitvector length");
    let mut value = SszBitvector::new();
    for (i, bit) in bits.iter().enumerate() {
        value.set(i, *bit).expect("test bug: bitvector index");
    }
    value
}

pub fn progressive_bitlist(bits: &[bool]) -> ProgressiveBitlist {
    let mut value = ProgressiveBitlist::new();
    for bit in bits {
        value.push(*bit);
    }
    value
}
