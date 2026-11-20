module
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Libssz.Merkle.Intrinsics
public import EthLib.Cryptography.Hash.Sha256
@[expose] public section

namespace Libssz.Merkle

open EthLib.Cryptography.Hash.Sha256

/-- The ABEF lanes of a state. -/
def abef (s : State) : M128 := #v[s.f, s.e, s.b, s.a]

/-- The CDGH lanes of a state. -/
def cdgh (s : State) : M128 := #v[s.h, s.g, s.d, s.c]

/-- A round as written by the `SHA256RNDS2` model: it receives the schedule word already added
to the constant. -/
def laneRound (s : State) (wk : UInt32) : State :=
  let t1 := ch s.e s.f s.g + bigSigma1 s.e + wk + s.h
  ⟨t1 + maj s.a s.b s.c + bigSigma0 s.a, s.a, s.b, s.c, t1 + s.d, s.e, s.f, s.g⟩

theorem laneRound_eq_round (s : State) (k x : UInt32) :
    laneRound s (x + k) = round s k x := by
  simp only [laneRound, round, State.mk.injEq, and_true]
  constructor <;> ac_rfl

theorem rnds2_laneRound (s : State) (wk : M128) :
    _mm_sha256rnds2_epu32 (cdgh s) (abef s) wk
      = abef (laneRound (laneRound s wk[0]) wk[1]) := rfl

theorem cdgh_laneRound2 (s : State) (x y : UInt32) :
    cdgh (laneRound (laneRound s x) y) = abef s := rfl

theorem shuffle_0e (a : M128) : _mm_shuffle_epi32 0x0e a = #v[a[2], a[3], a[0], a[0]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

theorem add_lanes (a b : M128) : _mm_add_epi32 a b = #v[a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-! ## `PALIGNR` with shift 4

`join_bytes` and `alignr_four` come from gattaca-com/silver (CC0),
`LeanBlsSimd/Proofs/Sha256.lean`. -/

theorem join_bytes (x : UInt32) :
    UInt32.ofNat ((UInt8.ofNat x.toNat).toNat + 256 * (UInt8.ofNat (x.toNat / 256)).toNat +
      65536 * (UInt8.ofNat (x.toNat / 65536)).toNat +
      16777216 * (UInt8.ofNat (x.toNat / 16777216)).toNat) = x := by
  apply UInt32.toNat_inj.mp
  have hx := x.toBitVec.isLt
  change x.toNat < 4294967296 at hx
  simp only [UInt32.toNat_ofNat', UInt8.toNat_ofNat']
  norm_num only [Nat.reducePow]
  omega

theorem alignr_four (a b : M128) : _mm_alignr_epi8 4 a b = #v[b[1], b[2], b[3], a[0]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    norm_num only [_mm_alignr_epi8, Intrinsics.fromBytes, Intrinsics.byte, Vector.getElem_ofFn,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      Nat.div_one]
  all_goals exact join_bytes _

/-! ## The schedule, four words at a time -/

def quad0 (w : Window) : M128 := #v[w.w0, w.w1, w.w2, w.w3]
def quad1 (w : Window) : M128 := #v[w.w4, w.w5, w.w6, w.w7]
def quad2 (w : Window) : M128 := #v[w.w8, w.w9, w.w10, w.w11]
def quad3 (w : Window) : M128 := #v[w.w12, w.w13, w.w14, w.w15]

/-- The schedule four words further ahead. -/
def next4 (w : Window) : Window := w.next.next.next.next

theorem quad0_next4 (w : Window) : quad0 (next4 w) = quad1 w := rfl
theorem quad1_next4 (w : Window) : quad1 (next4 w) = quad2 w := rfl
theorem quad2_next4 (w : Window) : quad2 (next4 w) = quad3 w := rfl

/-- `SHA256MSG1`, `PALIGNR`, `PADDD` and `SHA256MSG2`, combined as in the kernel, compute the
next four schedule words. -/
theorem quad3_next4 (w : Window) :
    _mm_sha256msg2_epu32
      (_mm_add_epi32 (_mm_sha256msg1_epu32 (quad0 w) (quad1 w))
        (_mm_alignr_epi8 4 (quad3 w) (quad2 w)))
      (quad3 w) = quad3 (next4 w) := by
  rw [alignr_four, add_lanes]
  rfl

/-! ## Four rounds -/

/-- Four rounds, with the four words already added to their constants. -/
def quadStep (s : State) (wk : M128) : State :=
  laneRound (laneRound (laneRound (laneRound s wk[0]) wk[1]) wk[2]) wk[3]

/-- What `four_rounds` of `shani.rs` computes: two `SHA256RNDS2`, the second with the two high
lanes of `wk` moved down by `PSHUFD`. -/
theorem four_rounds_lanes (s : State) (wk : M128) :
    _mm_sha256rnds2_epu32 (abef s) (_mm_sha256rnds2_epu32 (cdgh s) (abef s) wk)
        (_mm_shuffle_epi32 0x0e wk) = abef (quadStep s wk) ∧
    _mm_sha256rnds2_epu32 (cdgh s) (abef s) wk = cdgh (quadStep s wk) := by
  rw [shuffle_0e, rnds2_laneRound, ← cdgh_laneRound2 s wk[0] wk[1], rnds2_laneRound]
  exact ⟨rfl, rfl⟩

/-- Four rounds of the specification are one `quadStep`. -/
theorem rounds_quad (k0 k1 k2 k3 : UInt32) (rest : List UInt32) (w : Window) (s : State) :
    rounds (k0 :: k1 :: k2 :: k3 :: rest) w s
      = rounds rest (next4 w) (quadStep s (_mm_add_epi32 (quad0 w) #v[k0, k1, k2, k3])) := by
  rw [add_lanes]
  simp only [rounds, quadStep, quad0, next4, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, laneRound_eq_round]
  rfl

/-! ## The constants -/

/-- The constants from round `n` onward. -/
def Kfrom (n : Nat) : List UInt32 := K.toList.drop n

/-- The four constants of quartet `q`, as lanes. -/
def Krow (q : Nat) : M128 := #v[K[4 * q]!, K[4 * q + 1]!, K[4 * q + 2]!, K[4 * q + 3]!]

theorem Kfrom_zero : Kfrom 0 = K.toList := rfl

theorem Kfrom_end : Kfrom 64 = [] := rfl

theorem Kfrom_quad (q : Nat) (h : q < 16) :
    Kfrom (4 * q) = (Krow q)[0] :: (Krow q)[1] :: (Krow q)[2] :: (Krow q)[3] :: Kfrom (4 * q + 4) := by
  interval_cases q <;> rfl

/-- Four rounds of the specification, starting at quartet `q`. -/
theorem rounds_Kfrom (q : Nat) (h : q < 16) (w : Window) (s : State) :
    rounds (Kfrom (4 * q)) w s
      = rounds (Kfrom (4 * q + 4)) (next4 w) (quadStep s (_mm_add_epi32 (quad0 w) (Krow q))) := by
  rw [Kfrom_quad q h, rounds_quad]
  rfl

/-- The last 16 rounds of a block: no more schedule needs to be computed. -/
theorem rounds_last (w : Window) (s : State) :
    rounds (Kfrom 48) w s =
      quadStep (quadStep (quadStep (quadStep s (_mm_add_epi32 (quad0 w) (Krow 12)))
        (_mm_add_epi32 (quad1 w) (Krow 13))) (_mm_add_epi32 (quad2 w) (Krow 14)))
        (_mm_add_epi32 (quad3 w) (Krow 15)) := by
  have h12 := rounds_Kfrom 12 (by decide) w s
  have h13 := rounds_Kfrom 13 (by decide) (next4 w) (quadStep s (_mm_add_epi32 (quad0 w) (Krow 12)))
  have h14 := rounds_Kfrom 14 (by decide) (next4 (next4 w))
    (quadStep (quadStep s (_mm_add_epi32 (quad0 w) (Krow 12)))
      (_mm_add_epi32 (quad0 (next4 w)) (Krow 13)))
  have h15 := rounds_Kfrom 15 (by decide) (next4 (next4 (next4 w)))
    (quadStep (quadStep (quadStep s (_mm_add_epi32 (quad0 w) (Krow 12)))
      (_mm_add_epi32 (quad0 (next4 w)) (Krow 13)))
      (_mm_add_epi32 (quad0 (next4 (next4 w))) (Krow 14)))
  simp only [Nat.reduceMul, Nat.reduceAdd] at h12 h13 h14 h15
  rw [h12, h13, h14, h15, Kfrom_end]
  rfl

/-- Sixteen consecutive rounds: four steps of four. -/
theorem rounds_turn (q : Nat) (h : q + 3 < 16) (w : Window) (s : State) :
    rounds (Kfrom (4 * q)) w s =
      rounds (Kfrom (4 * (q + 4))) (next4 (next4 (next4 (next4 w))))
        (quadStep (quadStep (quadStep (quadStep s
          (_mm_add_epi32 (quad0 w) (Krow q)))
          (_mm_add_epi32 (quad0 (next4 w)) (Krow (q + 1))))
          (_mm_add_epi32 (quad0 (next4 (next4 w))) (Krow (q + 2))))
          (_mm_add_epi32 (quad0 (next4 (next4 (next4 w)))) (Krow (q + 3)))) := by
  rw [rounds_Kfrom q (by omega), show 4 * q + 4 = 4 * (q + 1) by omega,
    rounds_Kfrom (q + 1) (by omega), show 4 * (q + 1) + 4 = 4 * (q + 2) by omega,
    rounds_Kfrom (q + 2) (by omega), show 4 * (q + 2) + 4 = 4 * (q + 3) by omega,
    rounds_Kfrom (q + 3) (by omega), show 4 * (q + 3) + 4 = 4 * (q + 4) by omega]

/-! ## The final addition of a block -/

/-- The hash value after a block: the previous one plus the working variables. -/
def feed (s r : State) : State :=
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

theorem compress_eq (s : State) (bytes : ByteArray) (start : Nat) (whole : start + 64 ≤ bytes.size) :
    compress s bytes start whole = feed s (rounds (Kfrom 0) (Window.ofBlock bytes start whole) s) :=
  rfl

theorem add_abef (r s : State) : _mm_add_epi32 (abef r) (abef s) = abef (feed s r) := by
  rw [add_lanes]
  simp only [abef, feed, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, UInt32.add_comm]

theorem add_cdgh (r s : State) : _mm_add_epi32 (cdgh r) (cdgh s) = cdgh (feed s r) := by
  rw [add_lanes]
  simp only [cdgh, feed, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, UInt32.add_comm]

end Libssz.Merkle
