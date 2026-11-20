# Verification of the verif codec: libssz ≡ EthLib

> **Not meant to be merged.** This branch shows the proofs for the *verif* version of the
> `ssz` crate (#42: no iterators, closures or `unsafe`). The proofs meant for upstream are those
> for the optimized version, in the PR stacked on #43.

Lean 4 proofs that the SSZ codec of the `ssz` crate computes what the
[EthLib](https://github.com/ethereum/EthLib) specification says. The Rust code is translated to
Lean by [Charon + Aeneas](https://github.com/AeneasVerif/aeneas); the proofs are about that
translation, and EthLib's own definitions are the specification. Without iterators, closures
and `unsafe`, Aeneas translates the whole crate, with no axioms.

## What is proven

Every theorem has the form `f x ⦃ r => P r ⦄`: the Rust function `f`, as translated by Aeneas,
terminates without panicking and its result `r` satisfies `P`. `P` compares `r` with EthLib's
`serialize` or `deserialize`.

| What | Main theorems | Where |
|---|---|---|
| `bool`, `u8`…`u128`: encode and decode | `U64.ssz_append.spec`, `U64.from_ssz_bytes.spec`, … | `Libssz/Proofs/Bool.lean`, `Uint.lean` |
| lists of fixed-size items (integers, `bool`, `[u8; N]`) | `U64.decode_list.spec`, `U64.encode_list.spec`, … | `Libssz/Proofs/Lists.lean` |
| lists of variable-size items, generic in the item | `decode_var_list.spec`, `encode_var_list.agrees` | `Libssz/Proofs/VarLists.lean`, `VarEncode.lean` |
| containers, on the code `#[derive]` generates | `Example.from_ssz_bytes.spec`, `Example.encode.agrees` | `Libssz/Proofs/Container.lean` |
| fixed-size consensus containers (`Checkpoint`, `Fork`, `Validator`, …) | `Validator.from_ssz_bytes.spec`, … | `Libssz/Proofs/FixedContainers.lean` |

`Axioms.lean` lists the main theorems and prints their axioms: only Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`), no `sorry`. `make proofs` runs it.

* `bytes` (`Libssz/Proofs/Bytes.lean`) maps an Aeneas `Vec<u8>` or slice to EthLib's `Bytes`.
* `Agrees toV r spec` (`Libssz/Proofs/Bridge.lean`) holds when Rust and EthLib both accept
  with the same value, or both reject with corresponding errors (`ErrMatch`). Any other
  combination is `False`.
* Decode statements hold for every input under 4 GiB. Encode statements say that EthLib
  accepts the value and libssz writes exactly its bytes.

## Divergences from the specification, proven

* **Decode of inputs of 4 GiB or more.** EthLib rejects every SSZ input of 2³² bytes or more
  (`offsetOverflow`), even a list of fixed-size items; libssz accepts it.
  `U64.decode_list_diverges`.
* **Encode of values of 4 GiB or more.** Offsets are written with `as u32` and silently
  truncated, so `decode(encode(x)) ≠ x`; EthLib rejects the value. `encode_var_list.diverges`
  and `Example.encode.diverges`.

## Running it

In `lean/`, the first time: `lake update && lake exe cache get`. Then, from `verification/`:

```bash
make proofs     # lake build + the axioms check
make difftest   # libssz before the rewrite vs libssz vs the Lean model vs EthLib
make extract CHARON=/path/to/charon AENEAS=/path/to/aeneas   # regenerate lean/Libssz/Code/
```

## What has to be trusted

* Lean's kernel, the three standard axioms and Mathlib's cached `.olean` files.
* The rustc frontend Charon uses, Charon and Aeneas (versions below). The crate is extracted
  with the `verif-example` feature and no `--opaque`.
* The definitions of Aeneas' Lean library for the `core`/`alloc` functions the model uses, and
  the modeling assumption that allocation never fails. The only hand-written piece of the model
  is `Vec::reserve`, as the identity (Aeneas' model has no capacity).
* EthLib (commit below), `bytes`, `Agrees`/`ErrMatch` and the theorem statements.

## Versions

* EthLib `cdd16763847e2a6cf52f01128cc1ce618a8c516c`.
* Aeneas `5a392f4b80a4d0d05abc240eb2a7fa70622a9a35`, with the Charon commit in its `charon-pin`.
* Lean `v4.35.0`, Mathlib `56a0058`.
