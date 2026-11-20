# Verification: libssz ≡ EthLib

Lean 4 proofs that libssz's SSZ codec and Merkleization compute what the
[EthLib](https://github.com/ethereum/EthLib) specification says. The Rust code is translated to
Lean by [Charon + Aeneas](https://github.com/AeneasVerif/aeneas); the proofs are about that
translation, and EthLib's own definitions are the specification.

## What is proven

Every theorem has the form `f x ⦃ r => P r ⦄`: the Rust function `f`, as translated by Aeneas,
terminates without panicking and its result `r` satisfies `P`. `P` compares `r` with EthLib's
`serialize`, `deserialize`, `hashTreeRoot` or `combine` (SHA-256 of two nodes).

| What | Main theorems | Where |
|---|---|---|
| `bool`, `u8`…`u128`: encode and decode | `U64.ssz_append.spec`, `U64.from_ssz_bytes.spec`, … | `Libssz/Proofs/Bool.lean`, `Uint.lean` |
| lists of fixed-size items (integers, `bool`, `[u8; N]`) | `U64.decode_list.spec`, `U64.encode_list.spec`, … | `Libssz/Proofs/Lists.lean` |
| lists of variable-size items, generic in the item | `decode_var_list.spec`, `encode_var_list.agrees` | `Libssz/Proofs/VarLists.lean`, `VarEncode.lean` |
| containers, on the code `#[derive]` generates | `Example.from_ssz_bytes.spec`, `Example.encode.agrees` | `Libssz/Proofs/Container.lean` |
| fixed-size consensus containers (`Checkpoint`, `Fork`, `Validator`, …) | `Validator.from_ssz_bytes.spec`, … | `Libssz/Proofs/FixedContainers.lean` |
| the SHA-NI kernel (x86-64) computes `combine` | `hash_pair.spec`, `hash_pairs_x2.spec`, `hash_pairs_x4.spec`, `hash_layer.spec` | `Libssz/Merkle/Proofs/Kernel.lean` |
| the same kernel for AArch64 | the same names | `Libssz/MerkleNeon/Proofs/Kernel.lean` |
| the tree: `merkleize`, `pack`, `mix_in_length`, progressive | `merkleize.spec`, `pack.spec`, `mix_in_length.spec`, … | `Libssz/Merkle/Proofs/Tree.lean`, `Pack.lean`, `Zero.lean` |
| `hash_tree_root` of basic types, `[u8; N]`, `Vec<T>`, containers | `Validator.hash_tree_root.spec`, `VecU64.hash_tree_root.spec`, … | `Libssz/Merkle/Proofs/Types.lean`, `Vecs.lean`, `Composite.lean` |
| `SszList`, `SszVector`, bitfields, `BeaconBlock`, `BeaconState` (phase0) | `SszListU64.hash_tree_root.spec`, `BeaconState.hash_tree_root.spec`, … | `Libssz/SszTypes/Proofs/` |

`Axioms.lean` lists the main theorems (339) and prints their axioms: only Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`), no `sorry`. `make proofs` runs it and fails if
any theorem is missing or uses another axiom (`scripts/check_axioms.py`).

How to read the statements:

* `bytes` (`Libssz/Proofs/Bytes.lean`) maps an Aeneas `Vec<u8>` or slice to EthLib's `Bytes`.
* `Agrees toV r spec` (`Libssz/Proofs/Bridge.lean`) holds when Rust and EthLib both accept
  with the same value, or both reject with corresponding errors (`ErrMatch`, for example
  `InvalidFixedLength { expected, got }` ↔ `.scope expected got`). Any other combination is
  `False`, so "both fail" is not enough: they must fail for the same reason, with the same data.
* Decode statements hold for every input under 4 GiB. Encode statements say that EthLib
  accepts the value and libssz writes exactly its bytes.

The containers in `crates/*/src/verif_example.rs` (behind the `verif-example` feature, not part
of the API) exist for these proofs: Charon translates exactly the code that `#[derive]`
generates for them.

## Divergences from the specification, proven

* **Decode of inputs of 4 GiB or more.** EthLib rejects every SSZ input of 2³² bytes or more
  (`offsetOverflow`), even a list of fixed-size items, which has no offsets. libssz accepts
  it. `U64.decode_list_diverges`.
* **Encode of values of 4 GiB or more.** Offsets are written with `as u32` and silently
  truncated, so `decode(encode(x)) ≠ x`; EthLib rejects the value. Proven for both places in
  the code: lists (`encode_var_list.diverges`) and containers (`Example.encode.diverges`).
* **`[u8; N]` as a basic type.** For SSZ a `ByteVector[N]` is composite, but libssz treats
  `[u8; N]` with `N ≤ 32` as basic. In a list or vector of `[u8; N]` with `N < 32` it packs
  the items together, where the specification gives each item its own node, so the root
  differs. `VecU8x4.diverges` proves it for a list of two `[u8; 4]`. Consensus types are not
  affected (their byte lists are 32, 48 or 96 bytes).

## Layout

```
lean/
  Libssz/Code/                 Aeneas model of crates/ssz (the codec)
  Libssz/Merkle/Code/          Aeneas model of crates/ssz-merkle (x86-64: SHA-NI kernel, tree)
  Libssz/MerkleNeon/Code/      Aeneas model of the AArch64 kernel (crates/ssz-merkle/src/neon.rs)
  Libssz/SszTypes/Code/        Aeneas model of crates/ssz-types
  Libssz/**/Proofs/            the proofs
  Libssz/StdModel.lean         hand-written models of six core/alloc functions
  Libssz/Merkle/Intrinsics.lean, Libssz/MerkleNeon/Intrinsics.lean
                               hand-written models of the SHA/SIMD instructions
  Libssz/SszTypes/SmallVecModel.lean
                               hand-written model of SmallVec
  Axioms.lean                  the main theorems and their axioms
  DiffTest*.lean               executables that run the model and EthLib, for difftest/
scripts/                       post-processing of the Aeneas output, and proof generators
difftest/                      libssz vs libssz before the rewrite vs Lean model vs EthLib
difftest-merkle/               SHA kernels: CPU vs instruction models vs Aeneas model vs EthLib vs sha2
```

Pipeline:

```
crates/ssz         ──charon──▶ libssz.llbc              ──aeneas──▶ lean/Libssz/Code/
crates/ssz-merkle  ──charon──▶ libssz-merkle-shani.llbc ──aeneas──▶ lean/Libssz/Merkle/Code/
  (for aarch64)    ──charon──▶ libssz-merkle-neon.llbc  ──aeneas──▶ lean/Libssz/MerkleNeon/Code/
crates/ssz-types   ──charon──▶ libssz-types.llbc        ──aeneas──▶ lean/Libssz/SszTypes/Code/
                   (each FunsExternal.lean is completed by scripts/complete_externals_*.py)
```

## Running it

Lean comes through [elan](https://github.com/leanprover/elan); `lean/lean-toolchain` pins the
version. The first time, in `lean/`:

```bash
lake update && lake exe cache get   # Aeneas, EthLib and Mathlib (with Mathlib's build cache)
```

Then, from `verification/`:

```bash
make proofs     # lake build + the axioms check (fails on `sorry` or any other axiom)
make difftest   # builds the Lean executables, then cargo test --release in both difftest crates
```

`make proofs` does not need Charon or Aeneas: the generated model is committed. To regenerate it
after changing the Rust code, install Charon and Aeneas at the versions below (Aeneas'
`make setup-charon` builds the matching Charon) and run:

```bash
make extract CHARON=/path/to/charon AENEAS=/path/to/aeneas
```

`git diff lean/` then shows how the model changed, and `make proofs` whether the proofs still
hold.

## What has to be trusted

* **Lean:** the kernel of the version in `lean/lean-toolchain`, the three standard axioms, and
  Mathlib's `.olean` files from its build cache.
* **Rust to Lean:**
  * the rustc frontend Charon uses, Charon and Aeneas at the versions below;
  * the codec is extracted with the `verif-example` feature and no `--opaque`; Aeneas runs with
    `-filter-trait-methods` so unused `Iterator` methods are left out;
  * Merkleization is extracted starting from the kernel (`shani::hash_pair`, `hash_pairs_x2`,
    `hash_pairs_x4`, `hash_layer`), the tree functions and the containers of
    `verif_example.rs`; `shani::available` (CPU feature detection) is opaque. The AArch64 kernel
    is extracted from the same crate compiled for `aarch64-unknown-linux-gnu`. The tree and the
    types are extracted for x86-64 only; they are the same source on AArch64;
  * **linking between extractions.** What `ssz-merkle` uses from `ssz`, and what `ssz-types`
    uses from both, is replaced in Lean by the declaration with the same Rust path in the other
    crate's extraction (`scripts/link.py`). Lean checks that the types match; the assumption is
    that the same path names the same declaration in both extractions;
  * Charon and Aeneas ignore `#[target_feature]`: the model does not say on which CPU the
    kernel may run;
  * for containers, what is verified is the code the macro generates for the structs in
    `verif_example.rs`, not the macro itself.
* **The definitions of Aeneas' Lean library** for the `core` and `alloc` functions the model
  uses (slices, `Vec`, `to_vec`, `split_at_mut`, the slice iterator and `collect`,
  `U32::from_be_bytes`, …), and the modeling assumption that allocation never fails.
* **Hand-written models** (definitions, not axioms, so `#print axioms` does not show them):
  * `Libssz/StdModel.lean`: `as_chunks`, `as_flattened`, `Vec::into_flattened`,
    `Vec::into_boxed_slice`, `Iterator::map` and `Map::next`, from their documentation;
  * `Vec::reserve` as the identity (Aeneas' model has no capacity);
  * `Libssz/SszTypes/SmallVecModel.lean`: `SmallVec` as a `Vec` of its items;
  * `Libssz/Merkle/Intrinsics.lean`: `__m128i` as four 32-bit lanes and eight x86 instructions
    (`_mm_set_epi32`, `_mm_extract_epi32`, `_mm_add_epi32`, `_mm_shuffle_epi32`,
    `_mm_alignr_epi8`, `_mm_sha256msg1_epu32`, `_mm_sha256msg2_epu32`,
    `_mm_sha256rnds2_epu32`), from Intel's manual and `stdarch`; six come from
    [gattaca-com/silver](https://github.com/gattaca-com/silver). `black_box` is the identity;
  * `Libssz/MerkleNeon/Intrinsics.lean`: `uint32x4_t` and eight Arm intrinsics (`vaddq_u32`,
    `vdupq_n_u32`, `vsetq_lane_u32`, `vgetq_lane_u32`, `vsha256su0q_u32`, `vsha256su1q_u32`,
    `vsha256hq_u32`, `vsha256h2q_u32`), from Arm's pseudocode, ACLE and `stdarch`.

  `difftest-merkle` runs each instruction model against the real instruction (10,970 cases on
  x86-64, and it caught 17 of 17 bugs planted in the models). The Arm models are checked
  against vectors stored in `difftest-merkle/vectors/` by `tests/neon.rs`, which runs on an
  AArch64 machine (3,891 cases, no mismatches, on an Apple M4 Max).
* **The unverified dispatch to the kernels:** the `unsafe` calls in `Sha2Hasher` are correct if
  `shani::available()` / `neon::available()` tell the truth about the CPU; the fallback path
  with the `sha2` crate; and `shaniHasher` / `neonHasher`, the Lean copies of what
  `Sha2Hasher` does when the CPU has the SHA instructions. The tree theorems hold for any
  hasher that computes `combine`.
* **The specification, the bridge and the statements:** EthLib at the commit below (including
  its SHA-256), `bytes`, `Agrees`/`ErrMatch`, and the theorem statements. If those were wrong,
  the theorems would say something else.

Checked by Lean, so they need no trust: the proofs; the `K` and `PAD_WK` tables of the kernels
(compared with the specification); that interleaving two or four hashes does not mix them;
that hashing a level in place does not overwrite a node before reading it; the
`ZERO_HASHES` table that `build.rs` generates (the Lean kernel recomputes its 64 hashes); and
that `scripts/complete_externals_*.py` replace a fixed list of declarations and fail if any
other `axiom` is left.

## Out of scope

* Encode and decode of `SszList`, `SszVector` and of containers with lists (`BeaconBlock`,
  `BeaconState`): only their roots are proven.
* Unions and progressive containers, `mix_in_active_fields`, `ethereum_types.rs`.
* The two overlapping cases of `copy_within` (`ContainerEncoder::append_fixed` only uses the
  non-overlapping one, which is proven).
* `Vec<[u8; 0]>`: the theorems assume `N > 0`.
* Other architectures: outside x86-64 and little-endian AArch64, or without the SHA
  instructions, the kernels are not used and the `sha2` path runs.

## Differential tests

* `difftest/`: on the same deterministic inputs (valid encodings, mutations, random bytes,
  long lists), (A) libssz before the verification rewrite (upstream `f6c22eb`) against libssz
  now: same values, errors, re-encodings and panics; (B) the Lean model and EthLib against the
  Rust code. (B) checks the Aeneas translation, including functions without a theorem.
* `difftest-merkle/`: the CPU's SHA and SIMD instructions against their Lean models, and the
  SHA-NI kernel against its Aeneas model, EthLib and the `sha2` crate.

## Versions

* EthLib `cdd16763847e2a6cf52f01128cc1ce618a8c516c`.
* Aeneas `5a392f4b80a4d0d05abc240eb2a7fa70622a9a35` (Lean library and binary), with the Charon
  commit pinned in Aeneas' `charon-pin`.
* Lean `v4.35.0`, Mathlib `56a0058` (resolved through Aeneas and EthLib; see
  `lean/lake-manifest.json`).
