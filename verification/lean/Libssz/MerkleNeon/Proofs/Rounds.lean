module
public import Mathlib.Tactic.IntervalCases
public import Libssz.MerkleNeon.Intrinsics
public import Libssz.Merkle.Proofs.Rounds
@[expose] public section

/-!
# The Arm instructions and EthLib's SHA-256

What the models in `MerkleNeon/Intrinsics.lean` compute, in terms of EthLib's round and
schedule (`EthLib.Cryptography.Hash.Sha256`). It is the same thing `Merkle/Proofs/Rounds.lean`
does with the x86 instructions; the architecture-independent definitions (`quadStep`, `next4`,
`Kfrom`, `Krow`, `feed`…) are those of that file.
-/

namespace Libssz.MerkleNeon

open EthLib.Cryptography.Hash.Sha256
open Libssz.Merkle (laneRound quadStep quad0 quad1 quad2 quad3 next4 Kfrom Krow
  rounds_Kfrom rounds_last rounds_turn feed _mm_add_epi32)

/-- The ABCD lanes of a state: A in lane 0. -/
def abcd (s : State) : U32x4 := #v[s.a, s.b, s.c, s.d]

/-- The EFGH lanes of a state: E in lane 0. -/
def efgh (s : State) : U32x4 := #v[s.e, s.f, s.g, s.h]

/-! ## The rounds -/

/-- **One iteration of `SHA256hash` is one EthLib round**, with the schedule word already
added to the constant. The manual adds in a different order than FIPS 180-4; it is the same
modulo 2³². -/
theorem hashRound_laneRound (s : State) (w : UInt32) :
    hashRound (abcd s) (efgh s) w = (abcd (laneRound s w), efgh (laneRound s w)) := by
  have ht : s.h + bigSigma1 s.e + ch s.e s.f s.g + w = ch s.e s.f s.g + bigSigma1 s.e + w + s.h := by
    ac_rfl
  have ha : ∀ t : UInt32, t + bigSigma0 s.a + maj s.a s.b s.c = t + maj s.a s.b s.c + bigSigma0 s.a :=
    fun t => by ac_rfl
  show (#v[(s.h + bigSigma1 s.e + ch s.e s.f s.g + w) + bigSigma0 s.a + maj s.a s.b s.c, s.a, s.b,
      s.c], #v[(s.h + bigSigma1 s.e + ch s.e s.f s.g + w) + s.d, s.e, s.f, s.g]) = _
  rw [ht, ha]
  rfl

/-- `SHA256hash`: four rounds. -/
theorem sha256hash_quadStep (s : State) (wk : U32x4) :
    sha256hash (abcd s) (efgh s) wk = (abcd (quadStep s wk), efgh (quadStep s wk)) := by
  simp only [sha256hash, hashRound_laneRound, quadStep]

/-- `SHA256H` gives ABCD after four rounds. -/
theorem sha256h_quadStep (s : State) (wk : U32x4) :
    vsha256hq_u32 (abcd s) (efgh s) wk = abcd (quadStep s wk) := by
  simp only [vsha256hq_u32, sha256hash_quadStep]

/-- `SHA256H2`, starting from the same ABCD and EFGH, gives EFGH after the same rounds. -/
theorem sha256h2_quadStep (s : State) (wk : U32x4) :
    vsha256h2q_u32 (efgh s) (abcd s) wk = efgh (quadStep s wk) := by
  simp only [vsha256h2q_u32, sha256hash_quadStep]

/-! ## Lane-wise addition -/

theorem vaddq_lanes (a b : U32x4) :
    vaddq_u32 a b = #v[a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-- `vaddq_u32` and `_mm_add_epi32` are the same lane-wise addition: that is how the round
lemmas of `Merkle/Proofs/Rounds.lean`, which use the x86 name, apply here. -/
theorem vaddq_eq_add : vaddq_u32 = _mm_add_epi32 := rfl

theorem rounds_Kfrom' (q : Nat) (h : q < 16) (w : Window) (s : State) :
    rounds (Kfrom (4 * q)) w s
      = rounds (Kfrom (4 * q + 4)) (next4 w) (quadStep s (vaddq_u32 (quad0 w) (Krow q))) := by
  rw [vaddq_eq_add]
  exact rounds_Kfrom q h w s

theorem rounds_last' (w : Window) (s : State) :
    rounds (Kfrom 48) w s =
      quadStep (quadStep (quadStep (quadStep s (vaddq_u32 (quad0 w) (Krow 12)))
        (vaddq_u32 (quad1 w) (Krow 13))) (vaddq_u32 (quad2 w) (Krow 14)))
        (vaddq_u32 (quad3 w) (Krow 15)) := by
  rw [vaddq_eq_add]
  exact rounds_last w s

theorem rounds_turn' (q : Nat) (h : q + 3 < 16) (w : Window) (s : State) :
    rounds (Kfrom (4 * q)) w s =
      rounds (Kfrom (4 * (q + 4))) (next4 (next4 (next4 (next4 w))))
        (quadStep (quadStep (quadStep (quadStep s
          (vaddq_u32 (quad0 w) (Krow q)))
          (vaddq_u32 (quad0 (next4 w)) (Krow (q + 1))))
          (vaddq_u32 (quad0 (next4 (next4 w))) (Krow (q + 2))))
          (vaddq_u32 (quad0 (next4 (next4 (next4 w)))) (Krow (q + 3)))) := by
  rw [vaddq_eq_add]
  exact rounds_turn q h w s

/-! ## The schedule -/

/-- **`SHA256SU0` and `SHA256SU1`, combined as in the kernel, compute the next four schedule
words.** -/
theorem su_next4 (w : Window) :
    vsha256su1q_u32 (vsha256su0q_u32 (quad0 w) (quad1 w)) (quad2 w) (quad3 w)
      = quad3 (next4 w) := by
  have h16 : smallSigma1 w.w14 + (smallSigma0 w.w1 + w.w0) + w.w9
      = w.w0 + smallSigma0 w.w1 + w.w9 + smallSigma1 w.w14 := by ac_rfl
  have h17 : smallSigma1 w.w15 + (smallSigma0 w.w2 + w.w1) + w.w10
      = w.w1 + smallSigma0 w.w2 + w.w10 + smallSigma1 w.w15 := by ac_rfl
  have h18 : ∀ x : UInt32, smallSigma1 x + (smallSigma0 w.w3 + w.w2) + w.w11
      = w.w2 + smallSigma0 w.w3 + w.w11 + smallSigma1 x := fun x => by ac_rfl
  have h19 : ∀ x : UInt32, smallSigma1 x + (smallSigma0 w.w4 + w.w3) + w.w12
      = w.w3 + smallSigma0 w.w4 + w.w12 + smallSigma1 x := fun x => by ac_rfl
  show #v[smallSigma1 w.w14 + (smallSigma0 w.w1 + w.w0) + w.w9,
      smallSigma1 w.w15 + (smallSigma0 w.w2 + w.w1) + w.w10,
      smallSigma1 (smallSigma1 w.w14 + (smallSigma0 w.w1 + w.w0) + w.w9) +
        (smallSigma0 w.w3 + w.w2) + w.w11,
      smallSigma1 (smallSigma1 w.w15 + (smallSigma0 w.w2 + w.w1) + w.w10) +
        (smallSigma0 w.w4 + w.w3) + w.w12] = _
  rw [h18, h19, h16, h17]
  rfl

/-! ## The final addition of a block -/

theorem add_abcd (r s : State) : vaddq_u32 (abcd r) (abcd s) = abcd (feed s r) := by
  rw [vaddq_lanes]
  simp only [abcd, feed, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, UInt32.add_comm]

theorem add_efgh (r s : State) : vaddq_u32 (efgh r) (efgh s) = efgh (feed s r) := by
  rw [vaddq_lanes]
  simp only [efgh, feed, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, UInt32.add_comm]

end Libssz.MerkleNeon
