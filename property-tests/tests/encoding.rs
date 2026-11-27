//! Encoding properties: round trips, hash tree roots against the naive
//! reference model, and canonical decoding of edited encodings.
//!
//! One property per type and check, written out by hand (no macros), as in
//! `spec-tests`. Budgets are the defaults unless noted; `EPHYRA_TESTS`,
//! `EPHYRA_BUDGET_MS` and `EPHYRA_SEED` override them (see `make
//! property-tests-long`).

use ephyra::{any, classify, gens};
use libssz::SszEncode;
use libssz_merkle::{HashTreeRoot, Sha2Hasher};
use libssz_types::{ProgressiveBitlist, SszBitlist, SszBitvector, SszList};
use property_tests::edits::edited_encodings;
use property_tests::oracles::{decode_is_canonical, round_trips};
use property_tests::recipes::{
    bitlist, bitvector, progressive_bitlist, ChoiceRecipe, FixedRecipe, InnerRecipe, OuterRecipe,
    ShapesRecipe, SparseRecipe, TaggedRecipe, WrapperRecipe,
};
use property_tests::reference;
use property_tests::types::{
    Choice, Fixed, Inner, Outer, Shapes, Sparse, Tagged, Wrapped, Wrapper,
};

// ── Round trip and hash tree root ──

#[ephyra::test(gen = any::<InnerRecipe>())]
fn inner_round_trips_and_matches_reference_root(recipe: InnerRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

#[ephyra::test(gen = any::<OuterRecipe>())]
fn outer_round_trips_and_matches_reference_root(recipe: OuterRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

#[ephyra::test(gen = any::<ChoiceRecipe>())]
fn choice_round_trips_and_matches_reference_root(recipe: ChoiceRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

#[ephyra::test(gen = any::<SparseRecipe>(), tests = 2_000)]
fn sparse_round_trips_and_matches_reference_root(recipe: SparseRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

#[ephyra::test(gen = any::<WrapperRecipe>(), tests = 2_000)]
fn wrapper_round_trips_and_matches_reference_root(recipe: WrapperRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

#[ephyra::test(gen = any::<FixedRecipe>())]
fn fixed_round_trips_and_matches_reference_root(recipe: FixedRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

#[ephyra::test(gen = any::<TaggedRecipe>())]
fn tagged_round_trips_and_matches_reference_root(recipe: TaggedRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

#[ephyra::test(gen = any::<ShapesRecipe>(), tests = 2_000)]
fn shapes_round_trips_and_matches_reference_root(recipe: ShapesRecipe) {
    let value = recipe.build();
    round_trips(&value);
    assert_eq!(value.hash_tree_root(&Sha2Hasher), recipe.reference_root());
}

/// A list of all-fixed containers on its own: the derived bulk hooks
/// encode and decode it in one pass.
#[ephyra::test(gen = gens::vec(any::<FixedRecipe>()).len(0..=6))]
fn fixed_list_round_trips_and_matches_reference_root(recipes: Vec<FixedRecipe>) {
    let value: SszList<Fixed, 6> =
        SszList::try_from(recipes.iter().map(FixedRecipe::build).collect::<Vec<_>>())
            .expect("within limit");
    round_trips(&value);
    let roots: Vec<_> = recipes.iter().map(FixedRecipe::reference_root).collect();
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::composite_list_root(&roots, 6)
    );
}

/// A transparent struct is its field, at the top level as well as nested.
#[ephyra::test(gen = gens::vec(gens::int(0u16..=u16::MAX)).len(0..=9))]
fn transparent_is_its_field(items: Vec<u16>) {
    let list: SszList<u16, 9> = SszList::try_from(items).expect("within limit");
    let value = Wrapped(list.clone());
    round_trips(&value);
    assert_eq!(value.to_ssz(), list.to_ssz(), "encoding");
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        list.hash_tree_root(&Sha2Hasher),
        "root"
    );
}

#[ephyra::test(gen = gens::vec(gens::bool()).len(0..=20))]
fn bitlist_encoding_and_root_match_reference(bits: Vec<bool>) {
    let value = bitlist::<20>(&bits);
    round_trips(&value);
    assert_eq!(value.to_ssz(), reference::bitlist_encoding(&bits));
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::bitlist_root(&bits, 20)
    );
}

#[ephyra::test(gen = gens::vec(gens::bool()).len(11..=11))]
fn bitvector_encoding_and_root_match_reference(bits: Vec<bool>) {
    let value = bitvector::<11>(&bits);
    round_trips(&value);
    assert_eq!(value.to_ssz(), reference::bits_to_bytes(&bits));
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::bitvector_root(&bits)
    );
}

/// A byte-aligned bitvector has no padding bits, which takes the early
/// return in libssz's padding check.
#[ephyra::test(gen = gens::vec(gens::bool()).len(16..=16))]
fn byte_aligned_bitvector_encoding_and_root_match_reference(bits: Vec<bool>) {
    let value = bitvector::<16>(&bits);
    round_trips(&value);
    assert_eq!(value.to_ssz(), reference::bits_to_bytes(&bits));
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::bitvector_root(&bits)
    );
}

#[ephyra::test(gen = gens::vec(gens::bool()).len(0..=1500), tests = 2_000)]
fn progressive_bitlist_encoding_and_root_match_reference(bits: Vec<bool>) {
    let value = progressive_bitlist(&bits);
    round_trips(&value);
    assert_eq!(value.to_ssz(), reference::bitlist_encoding(&bits));
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::progressive_bitlist_root(&bits)
    );
}

// ── Canonical decoding of edited encodings ──

#[ephyra::test(gen = edited_encodings(any::<InnerRecipe>(), |r| r.build().to_ssz()))]
fn inner_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Inner>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(any::<OuterRecipe>(), |r| r.build().to_ssz()))]
fn outer_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Outer>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(any::<ChoiceRecipe>(), |r| r.build().to_ssz()))]
fn choice_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Choice>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(any::<SparseRecipe>(), |r| r.build().to_ssz()))]
fn sparse_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Sparse>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(any::<WrapperRecipe>(), |r| r.build().to_ssz()))]
fn wrapper_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Wrapper>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(any::<FixedRecipe>(), |r| r.build().to_ssz()))]
fn fixed_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Fixed>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(any::<FixedRecipe>()).len(0..=6),
    |rs| SszList::<Fixed, 6>::try_from(rs.iter().map(FixedRecipe::build).collect::<Vec<_>>())
        .expect("within limit")
        .to_ssz()
))]
fn fixed_list_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<SszList<Fixed, 6>>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(any::<TaggedRecipe>(), |r| r.build().to_ssz()))]
fn tagged_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Tagged>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(any::<ShapesRecipe>(), |r| r.build().to_ssz()))]
fn shapes_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Shapes>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::int(0u16..=u16::MAX)).len(0..=9),
    |items| Wrapped(SszList::try_from(items.clone()).expect("within limit")).to_ssz()
))]
fn transparent_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<Wrapped>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::bool()).len(0..=20),
    |bits| bitlist::<20>(bits).to_ssz()
))]
fn bitlist_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<SszBitlist<20>>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::bool()).len(0..=40),
    |bits| progressive_bitlist(bits).to_ssz()
))]
fn progressive_bitlist_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(
        decode_is_canonical::<ProgressiveBitlist>(&bytes),
        "accepted",
    );
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::bool()).len(11..=11),
    |bits| bitvector::<11>(bits).to_ssz()
))]
fn bitvector_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<SszBitvector<11>>(&bytes), "accepted");
}

#[ephyra::test(gen = edited_encodings(
    gens::vec(gens::bool()).len(16..=16),
    |bits| bitvector::<16>(bits).to_ssz()
))]
fn byte_aligned_bitvector_decodes_only_canonical_bytes(bytes: Vec<u8>) {
    classify(decode_is_canonical::<SszBitvector<16>>(&bytes), "accepted");
}
