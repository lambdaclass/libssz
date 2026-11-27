//! Operation sequences on the collection types, checked against a `Vec`
//! model after every step: contents, bounds, the encoding, decoding the
//! encoding back, and the hash tree root against the reference model.
//!
//! Mutation goes through `push`, `set`, `IndexMut` and `DerefMut`, so the
//! slice access added for `SszList` and `ProgressiveList` is covered too.

use ephyra::{any, gens};
use libssz::{SszDecode, SszEncode};
use libssz_merkle::{HashTreeRoot, Sha2Hasher};
use libssz_types::{
    IndexError, ProgressiveBitlist, ProgressiveList, SszBitlist, SszList, TypeError,
};
use property_tests::reference;

/// `SszBitlist<33>`: one bit past four whole bytes. At length 32 the
/// delimiter takes a byte of its own; at the limit it shares the fifth byte
/// with the last bit.
const BITLIST_LIMIT: usize = 33;
/// `SszList<u16, 40>`: 80 bytes, three chunks, the last one partial.
const LIST_LIMIT: usize = 40;

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
enum BitOp {
    Push(#[ephyra(gen = gens::bool())] bool),
    /// Push the same bit many times, to cross byte, chunk and progressive
    /// subtree boundaries quickly.
    PushMany(
        #[ephyra(gen = gens::bool())] bool,
        #[ephyra(gen = gens::int(0usize..=300))] usize,
    ),
    /// May be out of range, which must be an error that changes nothing.
    Set(
        #[ephyra(gen = gens::int(0usize..=64))] usize,
        #[ephyra(gen = gens::bool())] bool,
    ),
}

#[derive(Clone, Debug, PartialEq, ephyra::Arbitrary)]
enum ListOp {
    Push(#[ephyra(gen = gens::int(0u16..=u16::MAX))] u16),
    PushMany(
        #[ephyra(gen = gens::int(0u16..=u16::MAX))] u16,
        #[ephyra(gen = gens::int(0usize..=150))] usize,
    ),
    /// `list[i % len] = v` through `IndexMut`.
    Assign(
        #[ephyra(gen = gens::int(0usize..=64))] usize,
        #[ephyra(gen = gens::int(0u16..=u16::MAX))] u16,
    ),
    /// `list.swap(i % len, j % len)` through `DerefMut`.
    Swap(
        #[ephyra(gen = gens::int(0usize..=64))] usize,
        #[ephyra(gen = gens::int(0usize..=64))] usize,
    ),
    /// `list.reverse()` through `DerefMut`.
    Reverse,
    /// `list.sort_unstable()` through `DerefMut`.
    Sort,
}

fn u16_bytes(values: &[u16]) -> Vec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}

// ── SszBitlist ──

fn check_bitlist(value: &SszBitlist<BITLIST_LIMIT>, model: &[bool], step: usize) {
    assert_eq!(value.len(), model.len(), "step {step}: len");
    for (i, bit) in model.iter().enumerate() {
        assert_eq!(value.get(i), Some(*bit), "step {step}: get({i})");
    }
    assert_eq!(
        value.get(model.len()),
        None,
        "step {step}: get past the end"
    );
    let ones = model.iter().filter(|b| **b).count();
    assert_eq!(value.count_ones(), ones, "step {step}: count_ones");
    assert_eq!(
        value.as_bytes(),
        reference::bits_to_bytes(model),
        "step {step}: as_bytes"
    );
    let bytes = value.to_ssz();
    assert_eq!(
        bytes,
        reference::bitlist_encoding(model),
        "step {step}: encoding"
    );
    assert_eq!(
        SszBitlist::<BITLIST_LIMIT>::from_ssz_bytes(&bytes).as_ref(),
        Ok(value),
        "step {step}: decode"
    );
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::bitlist_root(model, BITLIST_LIMIT),
        "step {step}: root"
    );
}

#[ephyra::test(gen = (
    gens::int(0usize..=BITLIST_LIMIT),
    gens::vec(any::<BitOp>()).len(0..=30),
))]
fn bitlist_operations_match_model(input: (usize, Vec<BitOp>)) {
    let (initial_len, ops) = input;
    let mut value = SszBitlist::<BITLIST_LIMIT>::with_length(initial_len).expect("within limit");
    let mut model = vec![false; initial_len];
    check_bitlist(&value, &model, 0);
    for (step, op) in ops.iter().enumerate() {
        match op {
            BitOp::Push(bit) => bitlist_push(&mut value, &mut model, *bit),
            BitOp::PushMany(bit, count) => {
                for _ in 0..*count {
                    bitlist_push(&mut value, &mut model, *bit);
                }
            }
            BitOp::Set(index, bit) => {
                let result = value.set(*index, *bit);
                if *index < model.len() {
                    assert_eq!(result, Ok(model[*index]), "set({index}) in range");
                    model[*index] = *bit;
                } else {
                    let expected = IndexError {
                        index: *index,
                        len: model.len(),
                    };
                    assert_eq!(result, Err(expected), "set({index}) out of range");
                }
            }
        }
        check_bitlist(&value, &model, step + 1);
    }
}

fn bitlist_push(value: &mut SszBitlist<BITLIST_LIMIT>, model: &mut Vec<bool>, bit: bool) {
    let result = value.push(bit);
    if model.len() < BITLIST_LIMIT {
        assert_eq!(result, Ok(()), "push below the limit");
        model.push(bit);
    } else {
        let expected = TypeError::OverCapacity {
            max: BITLIST_LIMIT,
            got: model.len() + 1,
        };
        assert_eq!(result, Err(expected), "push at the limit");
    }
}

// ── ProgressiveBitlist ──

fn check_progressive_bitlist(value: &ProgressiveBitlist, model: &[bool], step: usize) {
    assert_eq!(value.len(), model.len(), "step {step}: len");
    for (i, bit) in model.iter().enumerate() {
        assert_eq!(value.get(i), Some(*bit), "step {step}: get({i})");
    }
    assert_eq!(
        value.get(model.len()),
        None,
        "step {step}: get past the end"
    );
    let ones = model.iter().filter(|b| **b).count();
    assert_eq!(value.count_ones(), ones, "step {step}: count_ones");
    assert_eq!(
        value.as_bytes(),
        reference::bits_to_bytes(model),
        "step {step}: as_bytes"
    );
    let bytes = value.to_ssz();
    assert_eq!(
        bytes,
        reference::bitlist_encoding(model),
        "step {step}: encoding"
    );
    assert_eq!(
        ProgressiveBitlist::from_ssz_bytes(&bytes).as_ref(),
        Ok(value),
        "step {step}: decode"
    );
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::progressive_bitlist_root(model),
        "step {step}: root"
    );
}

#[ephyra::test(
    gen = (gens::int(0usize..=64), gens::vec(any::<BitOp>()).len(0..=20)),
    tests = 2_000
)]
fn progressive_bitlist_operations_match_model(input: (usize, Vec<BitOp>)) {
    let (initial_len, ops) = input;
    let mut value = ProgressiveBitlist::with_length(initial_len);
    let mut model = vec![false; initial_len];
    check_progressive_bitlist(&value, &model, 0);
    for (step, op) in ops.iter().enumerate() {
        match op {
            BitOp::Push(bit) => {
                value.push(*bit);
                model.push(*bit);
            }
            BitOp::PushMany(bit, count) => {
                for _ in 0..*count {
                    value.push(*bit);
                    model.push(*bit);
                }
            }
            BitOp::Set(index, bit) => {
                let result = value.set(*index, *bit);
                if *index < model.len() {
                    assert_eq!(result, Ok(model[*index]), "set({index}) in range");
                    model[*index] = *bit;
                } else {
                    let expected = IndexError {
                        index: *index,
                        len: model.len(),
                    };
                    assert_eq!(result, Err(expected), "set({index}) out of range");
                }
            }
        }
        check_progressive_bitlist(&value, &model, step + 1);
    }
}

// ── SszList ──

fn check_list(value: &SszList<u16, LIST_LIMIT>, model: &[u16], step: usize) {
    assert_eq!(&**value, model, "step {step}: contents");
    assert_eq!(
        value.max_capacity(),
        LIST_LIMIT,
        "step {step}: max_capacity"
    );
    let bytes = value.to_ssz();
    assert_eq!(bytes, u16_bytes(model), "step {step}: encoding");
    assert_eq!(
        SszList::<u16, LIST_LIMIT>::from_ssz_bytes(&bytes).as_ref(),
        Ok(value),
        "step {step}: decode"
    );
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::basic_list_root(&u16_bytes(model), model.len(), LIST_LIMIT, 2),
        "step {step}: root"
    );
}

#[ephyra::test(gen = gens::vec(any::<ListOp>()).len(0..=30), tests = 2_000)]
fn list_operations_match_model(ops: Vec<ListOp>) {
    let mut value = SszList::<u16, LIST_LIMIT>::new();
    let mut model: Vec<u16> = Vec::new();
    check_list(&value, &model, 0);
    for (step, op) in ops.iter().enumerate() {
        match op {
            ListOp::Push(v) => list_push(&mut value, &mut model, *v),
            ListOp::PushMany(v, count) => {
                for _ in 0..*count {
                    list_push(&mut value, &mut model, *v);
                }
            }
            ListOp::Assign(i, v) => {
                if !model.is_empty() {
                    let i = i % model.len();
                    value[i] = *v;
                    model[i] = *v;
                }
            }
            ListOp::Swap(i, j) => {
                if !model.is_empty() {
                    let (i, j) = (i % model.len(), j % model.len());
                    value.swap(i, j);
                    model.swap(i, j);
                }
            }
            ListOp::Reverse => {
                value.reverse();
                model.reverse();
            }
            ListOp::Sort => {
                value.sort_unstable();
                model.sort_unstable();
            }
        }
        check_list(&value, &model, step + 1);
    }
}

fn list_push(value: &mut SszList<u16, LIST_LIMIT>, model: &mut Vec<u16>, v: u16) {
    let result = value.push(v);
    if model.len() < LIST_LIMIT {
        assert_eq!(result, Ok(()), "push below the limit");
        model.push(v);
    } else {
        let expected = TypeError::OverCapacity {
            max: LIST_LIMIT,
            got: model.len() + 1,
        };
        assert_eq!(result, Err(expected), "push at the limit");
    }
}

// ── ProgressiveList ──

fn check_progressive_list(value: &ProgressiveList<u16>, model: &[u16], step: usize) {
    assert_eq!(&**value, model, "step {step}: contents");
    let bytes = value.to_ssz();
    assert_eq!(bytes, u16_bytes(model), "step {step}: encoding");
    assert_eq!(
        ProgressiveList::<u16>::from_ssz_bytes(&bytes).as_ref(),
        Ok(value),
        "step {step}: decode"
    );
    assert_eq!(
        value.hash_tree_root(&Sha2Hasher),
        reference::progressive_basic_list_root(&u16_bytes(model), model.len()),
        "step {step}: root"
    );
}

#[ephyra::test(gen = gens::vec(any::<ListOp>()).len(0..=20), tests = 2_000)]
fn progressive_list_operations_match_model(ops: Vec<ListOp>) {
    let mut value = ProgressiveList::<u16>::new();
    let mut model: Vec<u16> = Vec::new();
    check_progressive_list(&value, &model, 0);
    for (step, op) in ops.iter().enumerate() {
        match op {
            ListOp::Push(v) => {
                value.push(*v);
                model.push(*v);
            }
            ListOp::PushMany(v, count) => {
                for _ in 0..*count {
                    value.push(*v);
                    model.push(*v);
                }
            }
            ListOp::Assign(i, v) => {
                if !model.is_empty() {
                    let i = i % model.len();
                    value[i] = *v;
                    model[i] = *v;
                }
            }
            ListOp::Swap(i, j) => {
                if !model.is_empty() {
                    let (i, j) = (i % model.len(), j % model.len());
                    value.swap(i, j);
                    model.swap(i, j);
                }
            }
            ListOp::Reverse => {
                value.reverse();
                model.reverse();
            }
            ListOp::Sort => {
                value.sort_unstable();
                model.sort_unstable();
            }
        }
        check_progressive_list(&value, &model, step + 1);
    }
}
