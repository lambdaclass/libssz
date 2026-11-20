module
public import Libssz.MerkleNeon.Proofs.Kernel
public import Libssz.Merkle.Proofs.Hasher
public import Libssz.Merkle.Proofs.Tree
public import Libssz.SszTypes.Proofs.Blocks
@[expose] public section

/-!
# The AArch64 kernel satisfies the hasher specification

The `ssz-merkle` tree and the `hash_tree_root` of the types are proved for any hasher that
satisfies `Lawful` (`Merkle/Proofs/Hasher.lean`): its three methods compute EthLib's
`combine`. `neonHasher` has the methods that `Sha2Hasher` uses on AArch64 when the processor
has the SHA-256 instructions, and `neon_lawful` states that it satisfies `Lawful`. With that,
all the tree and type theorems hold on ARM; two examples at the end.

As with the x86 kernel, `Sha2Hasher` itself is not extracted: its `hash` calls the `sha2`
crate, and it chooses between the kernel and `sha2` with `neon::available()`, the processor
detection. `neonHasher` copies by hand what `Sha2Hasher` does when that detection returns
true; see the TCB in the README.

**What is additionally assumed.** The tree and the types were extracted by compiling for
x86-64. On AArch64 it is the same Rust code (there is no architecture `cfg` in it, only in the
methods of `Sha2Hasher`), and both architectures are 64-bit, so `usize` is the same.
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz
open Libssz.Merkle (Lawful LayerPost emptyNodes sourceOf Node chunksOf)

namespace Libssz.MerkleNeon

/-- The methods of `Sha2Hasher` on AArch64 when `neon::available()` returns true (`lib.rs`):
`hash_pair` and `hash_layer` are the kernel's, and `hash_layer_in_place` is `hash_layer` with
`in_place = true`. `hash` is the one from the `sha2` crate, which the tree does not use: it
stays a parameter. -/
def neonHasher (hash : Unit → Slice Std.U8 → Result Node) : Sha256Hasher Unit where
  hash := hash
  hash_pair := fun _ a b => neon.hash_pair a b
  hash_layer := fun _ nodes out zero => neon.hash_layer nodes out false zero
  hash_layer_in_place := fun _ nodes zero => neon.hash_layer emptyNodes nodes true zero

/-- **The AArch64 kernel satisfies the specification.** -/
theorem neon_lawful (hash : Unit → Slice Std.U8 → Result Node) :
    Lawful (neonHasher hash) () where
  hash_pair a b := hash_pair.spec a b
  hash_layer nodes out zero h := by
    apply WP.spec_mono (hash_layer.spec nodes out false zero (by simpa [sourceOf] using h))
    intro r ⟨ hl, hpar, hrest ⟩
    exact ⟨ hl, fun j hj => hpar j (by simpa [sourceOf] using hj),
      fun j hj => hrest j (by simpa [sourceOf] using hj) ⟩
  hash_layer_in_place nodes zero := by
    apply WP.spec_mono (hash_layer.spec emptyNodes nodes true zero (by simp [sourceOf]; omega))
    intro r ⟨ hl, hpar, hrest ⟩
    exact ⟨ hl, fun j hj => hpar j (by simpa [sourceOf] using hj),
      fun j hj => hrest j (by simpa [sourceOf] using hj) ⟩

/-! ## Two examples -/

/-- **`merkleize` with the AArch64 kernel is EthLib's `merkleizeBoundedUnchecked`.** -/
theorem merkleize_neon (hash : Unit → Slice Std.U8 → Result Node) (chunks : Slice Node)
    (limit : Option Std.Usize) (hlimit : ∀ l, limit = some l → chunks.length ≤ l.val) :
    merkleize (neonHasher hash) () chunks limit ⦃ r =>
      merkleizeBoundedUnchecked (chunksOf chunks.val) (limit.map (·.val)) =
        .ok (bytes r.val) ⦄ :=
  Libssz.Merkle.merkleize.spec (neonHasher hash) () (neon_lawful hash) chunks limit hlimit

/-- **The root of `BeaconState` with the AArch64 kernel is the EthLib one**, under the same
invariants required by `BeaconState.hash_tree_root.spec`. -/
theorem beacon_state_neon (hash : Unit → Slice Std.U8 → Result Node) {VRL : Std.Usize}
    (x : libssz_types.verif_example.BeaconState VRL)
    (hvrl : 8 * VRL.val ≤ Usize.max)
    (hbr : x.block_roots.length = 8192) (hsr : x.state_roots.length = 8192)
    (hhr : x.historical_roots.length ≤ 16777216) (hev : x.eth1_data_votes.length ≤ 2048)
    (hval : x.validators.length ≤ VRL.val) (hbal : x.balances.length ≤ VRL.val)
    (hrm : x.randao_mixes.length = 65536) (hsl : x.slashings.length = 8192)
    (hpa : x.previous_epoch_attestations.length ≤ 4096)
    (hpa' : ∀ a ∈ x.previous_epoch_attestations.val,
      Libssz.SszTypes.BlInv a.aggregation_bits)
    (hca : x.current_epoch_attestations.length ≤ 4096)
    (hca' : ∀ a ∈ x.current_epoch_attestations.val,
      Libssz.SszTypes.BlInv a.aggregation_bits)
    (hjb : Libssz.SszTypes.Canon (bytes x.justification_bits.bytes.val) 4) :
    libssz_types.verif_example.BeaconState.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      (neonHasher hash) x () ⦃ r =>
        hashTreeRoot (.container Libssz.SszTypes.stateNames
          (Libssz.SszTypes.stateFields VRL)) (Libssz.SszTypes.stateV x)
          = .ok (bytes r.val) ⦄ :=
  Libssz.SszTypes.BeaconState.hash_tree_root.spec (neonHasher hash) () (neon_lawful hash)
    x hvrl hbr hsr hhr hev hval hbal hrm hsl hpa hpa' hca hca' hjb

end Libssz.MerkleNeon
