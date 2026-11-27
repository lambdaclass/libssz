//! Checks on the generators and shrinkers themselves, as ephyra recommends
//! before trusting a property built on them.

use ephyra::{any, check_shrinker, gens, Config};
use libssz::SszEncode;
use property_tests::edits::{byte_size, edited_encodings, shrink_bytes};
use property_tests::recipes::{bitlist, WrapperRecipe};

/// Every byte shrink candidate is strictly smaller by `byte_size`, so
/// shrinking always terminates.
#[test]
fn byte_shrinker_only_makes_smaller_candidates() {
    let encodings = edited_encodings(any::<WrapperRecipe>(), |r| r.build().to_ssz());
    check_shrinker(
        &Config::default().tests(300),
        encodings,
        |_| true,
        byte_size,
    )
    .assert_passed();
}

#[test]
fn byte_shrinker_only_makes_smaller_candidates_for_short_inputs() {
    let encodings = edited_encodings(gens::vec(gens::bool()).len(0..=20), |bits| {
        bitlist::<20>(bits).to_ssz()
    });
    check_shrinker(
        &Config::default().tests(2_000),
        encodings,
        |_| true,
        byte_size,
    )
    .assert_passed();
}

/// The shrinker offers nothing for the empty string, which is minimal.
#[test]
fn byte_shrinker_stops_at_the_empty_string() {
    let mut candidates = 0;
    let _ = shrink_bytes(&Vec::new(), &mut |_| {
        candidates += 1;
        std::ops::ControlFlow::Continue(())
    });
    assert_eq!(candidates, 0);
}
