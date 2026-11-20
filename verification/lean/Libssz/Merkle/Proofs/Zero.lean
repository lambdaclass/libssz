module
public import Libssz.Merkle.Code.Funs
public import Libssz.Proofs.Bytes
public import EthLib.Serialization.Proofs.Ssz.Merkle.Tree
@[expose] public section

/-!
# The `ZERO_HASHES` table

`crates/ssz-merkle/build.rs` computes the table with the `sha2` crate at build time, and the
Rust code includes it as 65 literal 32-byte arrays. Here we prove that those bytes are the
roots of the specification's zero trees: row `k` is `zeroRoot combine zeroChunk k`.

Neither `build.rs` nor `sha2` is trusted: the Lean kernel computes the 64 `combine` with
EthLib's SHA-256 and compares them with the rows.
-/

open Aeneas Aeneas.Std Result
open libssz_merkle
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz

namespace Libssz.Merkle

/-- A row of the table, as EthLib `Bytes`. -/
def zeroRow (k : Nat) : Bytes := bytes (ZERO_HASHES.val[k]!).val

/-- Row 0 is the zero node. -/
theorem zeroRow_zero : zeroRow 0 = zeroChunk := by decide +kernel

/-- Each row is the `combine` of the previous one with itself: 64 SHA-256 computed by the Lean
kernel, eight per theorem. With all 64 in a single computation, the kernel reaches 15 GB of
memory. -/
theorem zeroRow_succ_0 : ∀ r < 8, zeroRow (0 + r + 1) =
    combine (zeroRow (0 + r)) (zeroRow (0 + r)) := by
  decide +kernel

theorem zeroRow_succ_1 : ∀ r < 8, zeroRow (8 + r + 1) =
    combine (zeroRow (8 + r)) (zeroRow (8 + r)) := by
  decide +kernel

theorem zeroRow_succ_2 : ∀ r < 8, zeroRow (16 + r + 1) =
    combine (zeroRow (16 + r)) (zeroRow (16 + r)) := by
  decide +kernel

theorem zeroRow_succ_3 : ∀ r < 8, zeroRow (24 + r + 1) =
    combine (zeroRow (24 + r)) (zeroRow (24 + r)) := by
  decide +kernel

theorem zeroRow_succ_4 : ∀ r < 8, zeroRow (32 + r + 1) =
    combine (zeroRow (32 + r)) (zeroRow (32 + r)) := by
  decide +kernel

theorem zeroRow_succ_5 : ∀ r < 8, zeroRow (40 + r + 1) =
    combine (zeroRow (40 + r)) (zeroRow (40 + r)) := by
  decide +kernel

theorem zeroRow_succ_6 : ∀ r < 8, zeroRow (48 + r + 1) =
    combine (zeroRow (48 + r)) (zeroRow (48 + r)) := by
  decide +kernel

theorem zeroRow_succ_7 : ∀ r < 8, zeroRow (56 + r + 1) =
    combine (zeroRow (56 + r)) (zeroRow (56 + r)) := by
  decide +kernel

theorem zeroRow_succ (k : Nat) (h : k < 64) :
    zeroRow (k + 1) = combine (zeroRow k) (zeroRow k) := by
  have hk : k = 8 * (k / 8) + k % 8 := (Nat.div_add_mod k 8).symm
  have hr : k % 8 < 8 := Nat.mod_lt _ (by decide)
  have hg : k / 8 < 8 := by omega
  rw [hk]
  generalize k / 8 = g at hg
  generalize k % 8 = r at hr
  match g, hg with
  | 0, _ => exact zeroRow_succ_0 r hr
  | 1, _ => exact zeroRow_succ_1 r hr
  | 2, _ => exact zeroRow_succ_2 r hr
  | 3, _ => exact zeroRow_succ_3 r hr
  | 4, _ => exact zeroRow_succ_4 r hr
  | 5, _ => exact zeroRow_succ_5 r hr
  | 6, _ => exact zeroRow_succ_6 r hr
  | 7, _ => exact zeroRow_succ_7 r hr

/-- **Row `k` is the root of the zero tree of height `k`.** -/
theorem zeroRow_eq (k : Nat) (h : k ≤ 64) : zeroRow k = zeroRoot combine zeroChunk k := by
  induction k with
  | zero => exact zeroRow_zero
  | succ k ih => rw [zeroRow_succ k (by omega), ih (by omega)]; rfl

end Libssz.Merkle
