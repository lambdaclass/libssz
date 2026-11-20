module
public import Libssz.MerkleNeon.Code.Funs
public import Libssz.MerkleNeon.Proofs.Rounds
public import Libssz.Merkle.Proofs.Kernel
@[expose] public section

/-!
# The AArch64 SHA-256 kernel computes the specification's `combine`

The proofs for `crates/ssz-merkle/src/neon.rs`: `hash_pair`, `hash_pairs_x2` and
`hash_pairs_x4` compute EthLib's `combine` of their pairs, and `hash_layer` leaves a tree
layer. They are those of `Merkle/Proofs/Kernel.lean` (the x86 kernel) with the Arm
instructions: the Rust code of the two kernels has the same shape, and the
architecture-independent definitions are reused from that file (the big-endian words of a
node, the block of a pair, the parents of a layer).
-/

open Aeneas Aeneas.Std Result
open EthLib.Cryptography.Hash.Sha256
open libssz_merkle
open Libssz.Proofs (byte bytes)
open Libssz.Merkle (u32 rowOf quadAt wordAt pairWindow pairWindow_quads combine_eq
  wordBytes to_be_bytes_bytes list4 from_be_bytes_eq getD_map_byte Node sourceOf sourceOf_length
  sourceOf_getElem? parentOf parentOf_eq set2_other set2_first set2_second set4_getElem?
  getElem?_of_eq src_node black_box_eq quadStep quad0 quad1 quad2 quad3 next4 Kfrom Kfrom_end
  Krow feed padW pairState)

namespace Libssz.MerkleNeon

/-! ## The intrinsics, as equations -/

@[simp] theorem vaddq_eq (a b : U32x4) :
    core.core_arch.arm_shared.neon.generated.vaddq_u32 a b = ok (vaddq_u32 a b) := rfl
@[simp] theorem vdupq_eq (x : Std.U32) :
    core.core_arch.arm_shared.neon.generated.vdupq_n_u32 x = ok (vdupq_n_u32 (u32 x)) := rfl
@[simp] theorem vsetq_eq (lane : Std.I32) (x : Std.U32) (v : U32x4) :
    core.core_arch.arm_shared.neon.generated.vsetq_lane_u32 lane x v
      = ok (vsetq_lane_u32 lane.bv.toNat (u32 x) v) := rfl
@[simp] theorem vgetq_eq (lane : Std.I32) (v : U32x4) :
    core.core_arch.arm_shared.neon.generated.vgetq_lane_u32 lane v
      = ok ⟨(vgetq_lane_u32 lane.bv.toNat v).toBitVec⟩ := rfl
@[simp] theorem sha256h_eq (a e k : U32x4) :
    core.core_arch.arm_shared.neon.generated.vsha256hq_u32 a e k = ok (vsha256hq_u32 a e k) :=
  rfl
@[simp] theorem sha256h2_eq (e a k : U32x4) :
    core.core_arch.arm_shared.neon.generated.vsha256h2q_u32 e a k = ok (vsha256h2q_u32 e a k) :=
  rfl
@[simp] theorem su0_eq (a b : U32x4) :
    core.core_arch.arm_shared.neon.generated.vsha256su0q_u32 a b = ok (vsha256su0q_u32 a b) := rfl
@[simp] theorem su1_eq (a b c : U32x4) :
    core.core_arch.arm_shared.neon.generated.vsha256su1q_u32 a b c
      = ok (vsha256su1q_u32 a b c) := rfl

/-! ## Words -/

/-- `vdupq_n_u32` and three `vsetq_lane_u32` build the vector with the four values. -/
theorem set_dup (x0 x1 x2 x3 : UInt32) :
    vsetq_lane_u32 3 x3 (vsetq_lane_u32 2 x2 (vsetq_lane_u32 1 x1 (vdupq_n_u32 x0)))
      = #v[x0, x1, x2, x3] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

theorem words_eq (w0 w1 w2 w3 : Std.U32) :
    neon.words w0 w1 w2 w3 = ok #v[u32 w0, u32 w1, u32 w2, u32 w3] := by
  simp only [neon.words, vdupq_eq, vsetq_eq, bind_ok]
  rw [show (1#i32).bv.toNat = 1 from rfl, show (2#i32).bv.toNat = 2 from rfl,
    show (3#i32).bv.toNat = 3 from rfl, set_dup]

@[step]
theorem row.spec (r : Array Std.U32 4#usize) : neon.row r ⦃ m => m = rowOf r.val ⦄ := by
  unfold neon.row
  step as ⟨ i, hi ⟩
  step as ⟨ i1, hi1 ⟩
  step as ⟨ i2, hi2 ⟩
  step as ⟨ i3, hi3 ⟩
  simp only [words_eq, WP.spec_ok, rowOf, hi, hi1, hi2, hi3]
  simp

/-! ## The two tables -/

/-- The `K` table of `neon.rs` is EthLib's constants, four at a time. -/
theorem K_row (q : Nat) (h : q < 16) : rowOf (neon.K.val[q]!).val = Krow q := by
  unfold neon.K
  interval_cases q <;> decide +kernel

/-- The `PAD_WK` table of `neon.rs` is the schedule of the padding block, with the constants
already added. -/
theorem PAD_WK_row (q : Nat) (h : q < 16) :
    rowOf (neon.PAD_WK.val[q]!).val = vaddq_u32 (quad0 (padW q)) (Krow q) := by
  unfold neon.PAD_WK
  interval_cases q <;> decide +kernel

/-! ## Reading the block -/

@[step]
theorem be_word.spec (d : Array Std.U8 32#usize) (pos : Std.Usize) (h : pos.val + 4 ≤ 32) :
    neon.be_word d pos ⦃ r => u32 r = wordAt (d.val.map byte) pos.val ⦄ := by
  have hl : d.val.length = 32 := by scalar_tac
  unfold neon.be_word
  step as ⟨ i, hi ⟩
  step as ⟨ i1, hi1 ⟩
  step as ⟨ i2, hi2 ⟩
  step as ⟨ i3, hi3 ⟩
  step as ⟨ i4, hi4 ⟩
  step as ⟨ i5, hi5 ⟩
  step as ⟨ i6, hi6 ⟩
  simp only [from_be_bytes_eq, wordAt]
  rw [getD_map_byte _ _ (by omega), getD_map_byte _ _ (by omega), getD_map_byte _ _ (by omega),
    getD_map_byte _ _ (by omega)]
  simp only [hi, hi2, hi4, hi6, hi1, hi3, hi5]

@[step]
theorem be_words.spec (d : Array Std.U8 32#usize) (pos : Std.Usize) (h : pos.val + 16 ≤ 32) :
    neon.be_words d pos ⦃ r => r = quadAt (d.val.map byte) pos.val ⦄ := by
  unfold neon.be_words
  step as ⟨ i, hi ⟩
  step as ⟨ i1, hi1 ⟩
  step as ⟨ i2, hi2 ⟩
  step as ⟨ i3, hi3 ⟩
  step as ⟨ i4, hi4 ⟩
  step as ⟨ i5, hi5 ⟩
  step as ⟨ i6, hi6 ⟩
  simp only [words_eq, WP.spec_ok, quadAt, hi1, hi3, hi5, hi6, hi, hi2, hi4]

/-! ## The state of a hash in progress -/

/-- What a `Stream` of `neon.rs` holds: the working variables and the 16 current schedule
words. -/
def streamOf (s : State) (w : Window) : neon.Stream :=
  { abcd := abcd s, efgh := efgh s, w0 := quad0 w, w1 := quad1 w, w2 := quad2 w, w3 := quad3 w }

theorem iv_abcd :
    (#v[u32 1779033703#u32, u32 3144134277#u32, u32 1013904242#u32, u32 2773480762#u32] : U32x4)
      = abcd initial := by decide +kernel

theorem iv_efgh :
    (#v[u32 1359893119#u32, u32 2600822924#u32, u32 528734635#u32, u32 1541459225#u32] : U32x4)
      = efgh initial := by decide +kernel

@[step]
theorem start.spec (a b : Array Std.U8 32#usize) :
    neon.start a b ⦃ s => s = streamOf initial (pairWindow a b) ⦄ := by
  unfold neon.start
  simp only [words_eq, bind_ok, iv_abcd, iv_efgh]
  step as ⟨ m2, h2 ⟩
  step as ⟨ m3, h3 ⟩
  step as ⟨ m4, h4 ⟩
  step as ⟨ m5, h5 ⟩
  obtain ⟨ q0, q1, q2, q3 ⟩ := pairWindow_quads a b
  simp only [streamOf, q0, q1, q2, q3, h2, h3, h4, h5]

/-! ## Rounds -/

theorem four_rounds_eq (s : State) (wk : U32x4) :
    neon.four_rounds (abcd s) (efgh s) wk = ok (abcd (quadStep s wk), efgh (quadStep s wk)) := by
  simp only [neon.four_rounds, sha256h_eq, sha256h2_eq, bind_ok, sha256h_quadStep,
    sha256h2_quadStep]

/-- Four rounds and the next four schedule words. -/
@[step]
theorem scheduled_quad.spec (s : State) (w : Window) (quad : Std.Usize) (h : quad.val < 16) :
    neon.scheduled_quad (streamOf s w) quad ⦃ r =>
      r = streamOf (quadStep s (vaddq_u32 (quad0 w) (Krow quad.val))) (next4 w) ⦄ := by
  have hK := K_row quad.val h
  rw [getElem!_pos neon.K.val quad.val (by scalar_tac)] at hK
  unfold neon.scheduled_quad
  step as ⟨ a, ha ⟩
  step as ⟨ mi, hmi ⟩
  simp only [streamOf, vaddq_eq, su0_eq, su1_eq, bind_ok, four_rounds_eq, uncurry_apply_pair,
    WP.spec_ok]
  rw [su_next4, hmi, ha, hK]
  rfl

/-- The last 16 rounds of the block and the addition of the initial value. -/
@[step]
theorem finish_block.spec (s : State) (w : Window) :
    neon.finish_block (streamOf s w) ⦃ r =>
      r = (abcd (feed initial (rounds (Kfrom 48) w s)),
        efgh (feed initial (rounds (Kfrom 48) w s))) ⦄ := by
  have h12 := K_row 12 (by decide)
  have h13 := K_row 13 (by decide)
  have h14 := K_row 14 (by decide)
  have h15 := K_row 15 (by decide)
  rw [getElem!_pos neon.K.val 12 (by scalar_tac)] at h12
  rw [getElem!_pos neon.K.val 13 (by scalar_tac)] at h13
  rw [getElem!_pos neon.K.val 14 (by scalar_tac)] at h14
  rw [getElem!_pos neon.K.val 15 (by scalar_tac)] at h15
  unfold neon.finish_block
  step as ⟨ a, ha ⟩
  step as ⟨ mi, hmi ⟩
  simp only [streamOf, vaddq_eq, bind_ok, four_rounds_eq, uncurry_apply_pair, words_eq, iv_abcd,
    iv_efgh, add_abcd, add_efgh]
  step as ⟨ a1, ha1 ⟩
  step as ⟨ mi2, hmi2 ⟩
  step as ⟨ a2, ha2 ⟩
  step as ⟨ mi4, hmi4 ⟩
  step as ⟨ a3, ha3 ⟩
  step as ⟨ mi6, hmi6 ⟩
  rw [rounds_last', hmi, ha, hmi2, ha1, hmi4, ha2, hmi6, ha3, h12, h13, h14, h15]
  exact ⟨rfl, rfl⟩

/-! ## The two loops of the single-pair hash -/

/-- The first 48 rounds of the first block: the ones that still compute the schedule. -/
theorem hash_pair_loop0.spec (s : State) (w : Window) (quad : Std.Usize) (hq : quad.val ≤ 12) :
    neon.hash_pair_loop0 (streamOf s w) quad ⦃ r =>
      ∃ s' w', r = streamOf s' w' ∧
        rounds (Kfrom (4 * quad.val)) w s = rounds (Kfrom 48) w' s' ⦄ := by
  unfold neon.hash_pair_loop0
  spec_split
  · step as ⟨ s1, hs1 ⟩
    step as ⟨ quad1, hquad1 ⟩
    rw [hs1]
    apply WP.spec_mono (hash_pair_loop0.spec _ _ quad1 (by scalar_tac))
    intro r ⟨ s', w', hr, h ⟩
    refine ⟨ s', w', hr, ?_ ⟩
    rw [rounds_Kfrom' quad.val (by scalar_tac), ← h, hquad1]
    rfl
  · simp only [WP.spec_ok]
    have h12 : quad.val = 12 := by scalar_tac
    exact ⟨ s, w, rfl, by rw [h12] ⟩
termination_by 12 - quad.val
decreasing_by scalar_decr_tac

/-- Four rounds of the padding block: the `PAD_WK` row already has the schedule words and the
constants added. -/
theorem pad_quad (q : Nat) (h : q < 16) (t : State) :
    rounds (Kfrom (4 * q)) (padW q) t =
      rounds (Kfrom (4 * (q + 1))) (padW (q + 1))
        (quadStep t (rowOf (neon.PAD_WK.val[q]!).val)) := by
  rw [rounds_Kfrom' q h, PAD_WK_row q h]
  rfl

/-- The 64 rounds of the padding block. -/
theorem hash_pair_loop1.spec (t : State) (quad : Std.Usize) (hq : quad.val ≤ 16) :
    neon.hash_pair_loop1 (abcd t) (efgh t) quad ⦃ r =>
      r = (abcd (rounds (Kfrom (4 * quad.val)) (padW quad.val) t),
        efgh (rounds (Kfrom (4 * quad.val)) (padW quad.val) t)) ⦄ := by
  unfold neon.hash_pair_loop1
  spec_split
  · step as ⟨ a, ha ⟩
    step as ⟨ mi, hmi ⟩
    simp only [four_rounds_eq, bind_ok, uncurry_apply_pair]
    step as ⟨ quad1, hquad1 ⟩
    apply WP.spec_mono (hash_pair_loop1.spec _ quad1 (by scalar_tac))
    intro r hr
    rw [hr, pad_quad quad.val (by scalar_tac), hquad1, hmi, ha,
      getElem!_pos neon.PAD_WK.val quad.val (by scalar_tac)]
  · simp only [WP.spec_ok]
    have h16 : quad.val = 16 := by scalar_tac
    rw [h16]
    rfl
termination_by 16 - quad.val
decreasing_by scalar_decr_tac

/-! ## The digest -/

/-- The four bytes that `digest` takes from a lane. -/
def laneBytes (v : U32x4) (imm : Std.I32) : Array Std.U8 4#usize :=
  core.num.U32.to_be_bytes ⟨(vgetq_lane_u32 imm.bv.toNat v).toBitVec⟩

theorem laneBytes_def (v : U32x4) (imm : Std.I32) :
    laneBytes v imm = core.num.U32.to_be_bytes ⟨(vgetq_lane_u32 imm.bv.toNat v).toBitVec⟩ :=
  rfl

theorem laneBytes_map (v : U32x4) (imm : Std.I32) :
    (laneBytes v imm).val.map byte = wordBytes v[imm.bv.toNat % 4] := by
  rw [laneBytes, to_be_bytes_bytes]
  rfl

theorem digest.spec (h t : State) :
    neon.digest (abcd h) (efgh h) (abcd t) (efgh t) ⦃ r =>
      bytes r.val = (digest (feed h t)).data ⦄ := by
  unfold neon.digest
  simp only [vaddq_eq, add_abcd, add_efgh, vgetq_eq, lift, bind_ok, ← laneBytes_def]
  generalize hA : laneBytes (abcd (feed h t)) 0#i32 = A
  generalize hB : laneBytes (abcd (feed h t)) 1#i32 = B
  generalize hC : laneBytes (abcd (feed h t)) 2#i32 = C
  generalize hD : laneBytes (abcd (feed h t)) 3#i32 = D
  generalize hE : laneBytes (efgh (feed h t)) 0#i32 = E
  generalize hF : laneBytes (efgh (feed h t)) 1#i32 = F
  generalize hG : laneBytes (efgh (feed h t)) 2#i32 = G
  generalize hH : laneBytes (efgh (feed h t)) 3#i32 = H
  step as ⟨ i16, h16 ⟩
  step as ⟨ i17, h17 ⟩
  step as ⟨ i18, h18 ⟩
  step as ⟨ i19, h19 ⟩
  step as ⟨ i20, h20 ⟩
  step as ⟨ i21, h21 ⟩
  step as ⟨ i22, h22 ⟩
  step as ⟨ i23, h23 ⟩
  step as ⟨ i24, h24 ⟩
  step as ⟨ i25, h25 ⟩
  step as ⟨ i26, h26 ⟩
  step as ⟨ i27, h27 ⟩
  step as ⟨ i28, h28 ⟩
  step as ⟨ i29, h29 ⟩
  step as ⟨ i30, h30 ⟩
  step as ⟨ i31, h31 ⟩
  step as ⟨ i32, h32 ⟩
  step as ⟨ i33, h33 ⟩
  step as ⟨ i34, h34 ⟩
  step as ⟨ i35, h35 ⟩
  step as ⟨ i36, h36 ⟩
  step as ⟨ i37, h37 ⟩
  step as ⟨ i38, h38 ⟩
  step as ⟨ i39, h39 ⟩
  step as ⟨ i40, h40 ⟩
  step as ⟨ i41, h41 ⟩
  step as ⟨ i42, h42 ⟩
  step as ⟨ i43, h43 ⟩
  step as ⟨ i44, h44 ⟩
  step as ⟨ i45, h45 ⟩
  step as ⟨ i46, h46 ⟩
  step as ⟨ i47, h47 ⟩
  have eA := list4 A.val (by scalar_tac)
  have eB := list4 B.val (by scalar_tac)
  have eC := list4 C.val (by scalar_tac)
  have eD := list4 D.val (by scalar_tac)
  have eE := list4 E.val (by scalar_tac)
  have eF := list4 F.val (by scalar_tac)
  have eG := list4 G.val (by scalar_tac)
  have eH := list4 H.val (by scalar_tac)
  rw [← h16, ← h17, ← h18, ← h19] at eA
  rw [← h20, ← h21, ← h22, ← h23] at eB
  rw [← h24, ← h25, ← h26, ← h27] at eC
  rw [← h28, ← h29, ← h30, ← h31] at eD
  rw [← h32, ← h33, ← h34, ← h35] at eE
  rw [← h36, ← h37, ← h38, ← h39] at eF
  rw [← h40, ← h41, ← h42, ← h43] at eG
  rw [← h44, ← h45, ← h46, ← h47] at eH
  have hl : [i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31, i32,
      i33, i34, i35, i36, i37, i38, i39, i40, i41, i42, i43, i44, i45, i46, i47]
      = A.val ++ B.val ++ C.val ++ D.val ++ E.val ++ F.val ++ G.val ++ H.val := by
    rw [eA, eB, eC, eD, eE, eF, eG, eH]
    rfl
  subst hA hB hC hD hE hF hG hH
  simp only [Array.make_val, hl, bytes, List.map_append, laneBytes_map]
  rfl

/-! ## A pair of nodes -/

/-- **`hash_pair` is the specification's `combine`.** -/
@[step]
theorem hash_pair.spec (a b : Array Std.U8 32#usize) :
    neon.hash_pair a b ⦃ r =>
      bytes r.val = EthLib.Serialization.Ssz.combine (bytes a.val) (bytes b.val) ⦄ := by
  unfold neon.hash_pair
  step as ⟨ s, hs ⟩
  rw [hs]
  step with hash_pair_loop0.spec as ⟨ s1, s', w', hs1, hr ⟩
  rw [hs1]
  step as ⟨ abcd0, efgh0, h0, h1 ⟩
  rw [h0, h1]
  step with hash_pair_loop1.spec as ⟨ ab, cd, hab, hcd ⟩
  rw [hab, hcd]
  apply WP.spec_mono (digest.spec _ _)
  intro r hr'
  rw [hr', combine_eq, pairState, ← hr]

/-! ## Two pairs at once -/

/-- The first 48 rounds of the first block of the two hashes, interleaved 16 at a time. -/
theorem hash_pairs_x2_loop0.spec (scheduled : Std.Usize) (s0 s1 : State) (w0 w1 : Window)
    (turn : Std.Usize) (hs : scheduled.val ≤ 3) (ht : turn.val ≤ scheduled.val) :
    neon.hash_pairs_x2_loop0 scheduled (streamOf s0 w0) (streamOf s1 w1) turn ⦃ r =>
      ∃ s0' w0' s1' w1', r = (streamOf s0' w0', streamOf s1' w1') ∧
        rounds (Kfrom (4 * (4 * turn.val))) w0 s0
          = rounds (Kfrom (4 * (4 * scheduled.val))) w0' s0' ∧
        rounds (Kfrom (4 * (4 * turn.val))) w1 s1
          = rounds (Kfrom (4 * (4 * scheduled.val))) w1' s1' ⦄ := by
  unfold neon.hash_pairs_x2_loop0
  spec_split
  · step as ⟨ i, hi ⟩
    step as ⟨ s01, h01 ⟩
    subst h01
    step as ⟨ s11, h11 ⟩
    subst h11
    step as ⟨ i1, hi1 ⟩
    step as ⟨ s02, h02 ⟩
    subst h02
    step as ⟨ i2, hi2 ⟩
    step as ⟨ s12, h12 ⟩
    subst h12
    step as ⟨ i3, hi3 ⟩
    step as ⟨ s03, h03 ⟩
    subst h03
    step as ⟨ i4, hi4 ⟩
    step as ⟨ s13, h13 ⟩
    subst h13
    step as ⟨ i5, hi5 ⟩
    step as ⟨ s04, h04 ⟩
    subst h04
    step as ⟨ i6, hi6 ⟩
    step as ⟨ s14, h14 ⟩
    subst h14
    step as ⟨ turn1, hturn1 ⟩
    apply WP.spec_mono (hash_pairs_x2_loop0.spec scheduled _ _ _ _ turn1 hs (by scalar_tac))
    intro r ⟨ s0', w0', s1', w1', hr, e0, e1 ⟩
    have e4 : 4 * turn1.val = 4 * turn.val + 4 := by scalar_tac
    rw [e4, hi1, hi3, hi5, hi] at e0
    rw [e4, hi2, hi4, hi6, hi] at e1
    refine ⟨ s0', w0', s1', w1', hr, ?_, ?_ ⟩
    · rw [rounds_turn' (4 * turn.val) (by scalar_tac)]
      exact e0
    · rw [rounds_turn' (4 * turn.val) (by scalar_tac)]
      exact e1
  · simp only [WP.spec_ok]
    have hts : turn.val = scheduled.val := by scalar_tac
    exact ⟨ s0, w0, s1, w1, rfl, by rw [hts], by rw [hts] ⟩
termination_by scheduled.val - turn.val
decreasing_by scalar_decr_tac

/-- Sixteen rounds of the padding block. -/
theorem pad_turn (q : Nat) (h : q + 3 < 16) (t : State) :
    rounds (Kfrom (4 * q)) (padW q) t =
      rounds (Kfrom (4 * (q + 4))) (padW (q + 4))
        (quadStep (quadStep (quadStep (quadStep t
          (rowOf (neon.PAD_WK.val[q]!).val))
          (rowOf (neon.PAD_WK.val[q + 1]!).val))
          (rowOf (neon.PAD_WK.val[q + 2]!).val))
          (rowOf (neon.PAD_WK.val[q + 3]!).val)) := by
  rw [pad_quad q (by omega), pad_quad (q + 1) (by omega), pad_quad (q + 2) (by omega),
    pad_quad (q + 3) (by omega)]

/-- The 64 rounds of the padding block of the two hashes, interleaved 16 at a time. -/
theorem hash_pairs_x2_loop1.spec (padded : Std.Usize) (t0 t1 : State) (turn : Std.Usize)
    (hp : padded.val ≤ 4) (ht : turn.val ≤ padded.val) :
    neon.hash_pairs_x2_loop1 padded (abcd t0) (efgh t0) (abcd t1) (efgh t1) turn ⦃ r =>
      ∃ t0' t1', r = (abcd t0', efgh t0', abcd t1', efgh t1') ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t0
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t0' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t1
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t1' ⦄ := by
  unfold neon.hash_pairs_x2_loop1
  spec_split
  · simp only [four_rounds_eq, bind_ok, uncurry_apply_pair]
    step as ⟨ i, hi ⟩
    step as ⟨ a, ha ⟩
    step as ⟨ wk, hwk ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ a1, ha1 ⟩
    step as ⟨ wk1, hwk1 ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ a2, ha2 ⟩
    step as ⟨ wk2, hwk2 ⟩
    step as ⟨ i3, hi3 ⟩
    step as ⟨ a3, ha3 ⟩
    step as ⟨ wk3, hwk3 ⟩
    step as ⟨ turn1, hturn1 ⟩
    have ek : wk = rowOf (neon.PAD_WK.val[4 * turn.val]!).val := by
      rw [hwk, ha, ← getElem!_pos neon.PAD_WK.val i.val (by scalar_tac), hi]
    have ek1 : wk1 = rowOf (neon.PAD_WK.val[4 * turn.val + 1]!).val := by
      rw [hwk1, ha1, ← getElem!_pos neon.PAD_WK.val i1.val (by scalar_tac), hi1, hi]
    have ek2 : wk2 = rowOf (neon.PAD_WK.val[4 * turn.val + 2]!).val := by
      rw [hwk2, ha2, ← getElem!_pos neon.PAD_WK.val i2.val (by scalar_tac), hi2, hi]
    have ek3 : wk3 = rowOf (neon.PAD_WK.val[4 * turn.val + 3]!).val := by
      rw [hwk3, ha3, ← getElem!_pos neon.PAD_WK.val i3.val (by scalar_tac), hi3, hi]
    apply WP.spec_mono (hash_pairs_x2_loop1.spec padded _ _ turn1 hp (by scalar_tac))
    intro r ⟨ t0', t1', hr, e0, e1 ⟩
    have e4 : 4 * turn1.val = 4 * turn.val + 4 := by scalar_tac
    rw [e4, ek, ek1, ek2, ek3] at e0 e1
    refine ⟨ t0', t1', hr, ?_, ?_ ⟩
    · rw [pad_turn (4 * turn.val) (by scalar_tac)]
      exact e0
    · rw [pad_turn (4 * turn.val) (by scalar_tac)]
      exact e1
  · simp only [WP.spec_ok]
    have htp : turn.val = padded.val := by scalar_tac
    exact ⟨ t0, t1, rfl, by rw [htp], by rw [htp] ⟩
termination_by padded.val - turn.val
decreasing_by scalar_decr_tac

/-- **`hash_pairs_x2` is two of the specification's `combine`.** -/
@[step]
theorem hash_pairs_x2.spec (a0 b0 a1 b1 : Array Std.U8 32#usize) :
    neon.hash_pairs_x2 a0 b0 a1 b1 ⦃ x y =>
      bytes x.val = EthLib.Serialization.Ssz.combine (bytes a0.val) (bytes b0.val) ∧
      bytes y.val = EthLib.Serialization.Ssz.combine (bytes a1.val) (bytes b1.val) ⦄ := by
  unfold neon.hash_pairs_x2
  simp only [black_box_eq, bind_ok]
  step as ⟨ s0, hs0 ⟩
  step as ⟨ s1, hs1 ⟩
  rw [hs0, hs1]
  step with hash_pairs_x2_loop0.spec as ⟨ r0, r1, s0', w0', s1', w1', hr0, hr1, e0, e1 ⟩
  rw [hr0, hr1]
  step as ⟨ abcd00, efgh00, h00, h01 ⟩
  step as ⟨ abcd10, efgh10, h10, h11 ⟩
  rw [h00, h01, h10, h11]
  step with hash_pairs_x2_loop1.spec as
    ⟨ ab0, cd0, ab1, cd1, t0', t1', hab0, hcd0, hab1, hcd1, f0, f1 ⟩
  simp only [Nat.reduceMul, Kfrom_end, rounds] at e0 e1 f0 f1
  subst f0 f1
  rw [hab0, hcd0, hab1, hcd1]
  step with digest.spec as ⟨ x, hx ⟩
  step with digest.spec as ⟨ y, hy ⟩
  rw [hx, hy, combine_eq, combine_eq, pairState, pairState, e0, e1]
  exact ⟨rfl, rfl⟩

/-! ## Four pairs at once -/

/-- The first 48 rounds of the first block of the four hashes, interleaved 16 at a time. -/
theorem hash_pairs_x4_loop0.spec (scheduled : Std.Usize) (s0 s1 s2 s3 : State)
    (w0 w1 w2 w3 : Window) (turn : Std.Usize) (hs : scheduled.val ≤ 3)
    (ht : turn.val ≤ scheduled.val) :
    neon.hash_pairs_x4_loop0 scheduled (streamOf s0 w0) (streamOf s1 w1) (streamOf s2 w2)
      (streamOf s3 w3) turn ⦃ r =>
      ∃ s0' w0' s1' w1' s2' w2' s3' w3',
        r = (streamOf s0' w0', streamOf s1' w1', streamOf s2' w2', streamOf s3' w3') ∧
        rounds (Kfrom (4 * (4 * turn.val))) w0 s0
          = rounds (Kfrom (4 * (4 * scheduled.val))) w0' s0' ∧
        rounds (Kfrom (4 * (4 * turn.val))) w1 s1
          = rounds (Kfrom (4 * (4 * scheduled.val))) w1' s1' ∧
        rounds (Kfrom (4 * (4 * turn.val))) w2 s2
          = rounds (Kfrom (4 * (4 * scheduled.val))) w2' s2' ∧
        rounds (Kfrom (4 * (4 * turn.val))) w3 s3
          = rounds (Kfrom (4 * (4 * scheduled.val))) w3' s3' ⦄ := by
  unfold neon.hash_pairs_x4_loop0
  spec_split
  · step as ⟨ i, hi ⟩
    step as ⟨ s01, h01 ⟩
    subst h01
    step as ⟨ s11, h11 ⟩
    subst h11
    step as ⟨ s21, h21 ⟩
    subst h21
    step as ⟨ s31, h31 ⟩
    subst h31
    step as ⟨ i1, hi1 ⟩
    step as ⟨ s02, h02 ⟩
    subst h02
    step as ⟨ i2, hi2 ⟩
    step as ⟨ s12, h12 ⟩
    subst h12
    step as ⟨ i3, hi3 ⟩
    step as ⟨ s22, h22 ⟩
    subst h22
    step as ⟨ i4, hi4 ⟩
    step as ⟨ s32, h32 ⟩
    subst h32
    step as ⟨ i5, hi5 ⟩
    step as ⟨ s03, h03 ⟩
    subst h03
    step as ⟨ i6, hi6 ⟩
    step as ⟨ s13, h13 ⟩
    subst h13
    step as ⟨ i7, hi7 ⟩
    step as ⟨ s23, h23 ⟩
    subst h23
    step as ⟨ i8, hi8 ⟩
    step as ⟨ s33, h33 ⟩
    subst h33
    step as ⟨ i9, hi9 ⟩
    step as ⟨ s04, h04 ⟩
    subst h04
    step as ⟨ i10, hi10 ⟩
    step as ⟨ s14, h14 ⟩
    subst h14
    step as ⟨ i11, hi11 ⟩
    step as ⟨ s24, h24 ⟩
    subst h24
    step as ⟨ i12, hi12 ⟩
    step as ⟨ s34, h34 ⟩
    subst h34
    step as ⟨ turn1, hturn1 ⟩
    apply WP.spec_mono (hash_pairs_x4_loop0.spec scheduled _ _ _ _ _ _ _ _ turn1 hs
      (by scalar_tac))
    intro r ⟨ s0', w0', s1', w1', s2', w2', s3', w3', hr, e0, e1, e2, e3 ⟩
    have e4 : 4 * turn1.val = 4 * turn.val + 4 := by scalar_tac
    rw [e4, hi1, hi5, hi9, hi] at e0
    rw [e4, hi2, hi6, hi10, hi] at e1
    rw [e4, hi3, hi7, hi11, hi] at e2
    rw [e4, hi4, hi8, hi12, hi] at e3
    refine ⟨ s0', w0', s1', w1', s2', w2', s3', w3', hr, ?_, ?_, ?_, ?_ ⟩
    · rw [rounds_turn' (4 * turn.val) (by scalar_tac)]
      exact e0
    · rw [rounds_turn' (4 * turn.val) (by scalar_tac)]
      exact e1
    · rw [rounds_turn' (4 * turn.val) (by scalar_tac)]
      exact e2
    · rw [rounds_turn' (4 * turn.val) (by scalar_tac)]
      exact e3
  · simp only [WP.spec_ok]
    have hts : turn.val = scheduled.val := by scalar_tac
    exact ⟨ s0, w0, s1, w1, s2, w2, s3, w3, rfl, by rw [hts], by rw [hts], by rw [hts],
      by rw [hts] ⟩
termination_by scheduled.val - turn.val
decreasing_by scalar_decr_tac

/-- The 64 rounds of the padding block of the four hashes, interleaved 16 at a time. -/
theorem hash_pairs_x4_loop1.spec (padded : Std.Usize) (t0 t1 t2 t3 : State) (turn : Std.Usize)
    (hp : padded.val ≤ 4) (ht : turn.val ≤ padded.val) :
    neon.hash_pairs_x4_loop1 padded (abcd t0) (efgh t0) (abcd t1) (efgh t1) (abcd t2)
      (efgh t2) (abcd t3) (efgh t3) turn ⦃ r =>
      ∃ t0' t1' t2' t3', r = (abcd t0', efgh t0', abcd t1', efgh t1', abcd t2', efgh t2',
          abcd t3', efgh t3') ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t0
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t0' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t1
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t1' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t2
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t2' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t3
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t3' ⦄ := by
  unfold neon.hash_pairs_x4_loop1
  spec_split
  · simp only [four_rounds_eq, bind_ok, uncurry_apply_pair]
    step as ⟨ i, hi ⟩
    step as ⟨ a, ha ⟩
    step as ⟨ wk, hwk ⟩
    step as ⟨ i1, hi1 ⟩
    step as ⟨ a1, ha1 ⟩
    step as ⟨ wk1, hwk1 ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ a2, ha2 ⟩
    step as ⟨ wk2, hwk2 ⟩
    step as ⟨ i3, hi3 ⟩
    step as ⟨ a3, ha3 ⟩
    step as ⟨ wk3, hwk3 ⟩
    step as ⟨ turn1, hturn1 ⟩
    have ek : wk = rowOf (neon.PAD_WK.val[4 * turn.val]!).val := by
      rw [hwk, ha, ← getElem!_pos neon.PAD_WK.val i.val (by scalar_tac), hi]
    have ek1 : wk1 = rowOf (neon.PAD_WK.val[4 * turn.val + 1]!).val := by
      rw [hwk1, ha1, ← getElem!_pos neon.PAD_WK.val i1.val (by scalar_tac), hi1, hi]
    have ek2 : wk2 = rowOf (neon.PAD_WK.val[4 * turn.val + 2]!).val := by
      rw [hwk2, ha2, ← getElem!_pos neon.PAD_WK.val i2.val (by scalar_tac), hi2, hi]
    have ek3 : wk3 = rowOf (neon.PAD_WK.val[4 * turn.val + 3]!).val := by
      rw [hwk3, ha3, ← getElem!_pos neon.PAD_WK.val i3.val (by scalar_tac), hi3, hi]
    apply WP.spec_mono (hash_pairs_x4_loop1.spec padded _ _ _ _ turn1 hp (by scalar_tac))
    intro r ⟨ t0', t1', t2', t3', hr, e0, e1, e2, e3 ⟩
    have e4 : 4 * turn1.val = 4 * turn.val + 4 := by scalar_tac
    rw [e4, ek, ek1, ek2, ek3] at e0 e1 e2 e3
    refine ⟨ t0', t1', t2', t3', hr, ?_, ?_, ?_, ?_ ⟩
    · rw [pad_turn (4 * turn.val) (by scalar_tac)]
      exact e0
    · rw [pad_turn (4 * turn.val) (by scalar_tac)]
      exact e1
    · rw [pad_turn (4 * turn.val) (by scalar_tac)]
      exact e2
    · rw [pad_turn (4 * turn.val) (by scalar_tac)]
      exact e3
  · simp only [WP.spec_ok]
    have htp : turn.val = padded.val := by scalar_tac
    exact ⟨ t0, t1, t2, t3, rfl, by rw [htp], by rw [htp], by rw [htp], by rw [htp] ⟩
termination_by padded.val - turn.val
decreasing_by scalar_decr_tac

/-- **`hash_pairs_x4` is four of the specification's `combine`.** -/
@[step]
theorem hash_pairs_x4.spec (a0 b0 a1 b1 a2 b2 a3 b3 : Array Std.U8 32#usize) :
    neon.hash_pairs_x4 a0 b0 a1 b1 a2 b2 a3 b3 ⦃ x y z w =>
      bytes x.val = EthLib.Serialization.Ssz.combine (bytes a0.val) (bytes b0.val) ∧
      bytes y.val = EthLib.Serialization.Ssz.combine (bytes a1.val) (bytes b1.val) ∧
      bytes z.val = EthLib.Serialization.Ssz.combine (bytes a2.val) (bytes b2.val) ∧
      bytes w.val = EthLib.Serialization.Ssz.combine (bytes a3.val) (bytes b3.val) ⦄ := by
  unfold neon.hash_pairs_x4
  simp only [black_box_eq, bind_ok]
  step as ⟨ s0, hs0 ⟩
  step as ⟨ s1, hs1 ⟩
  step as ⟨ s2, hs2 ⟩
  step as ⟨ s3, hs3 ⟩
  rw [hs0, hs1, hs2, hs3]
  step with hash_pairs_x4_loop0.spec as ⟨ r0, r1, r2, r3, s0', w0', s1', w1', s2', w2', s3', w3',
    hr0, hr1, hr2, hr3, e0, e1, e2, e3 ⟩
  rw [hr0, hr1, hr2, hr3]
  step as ⟨ abcd00, efgh00, h00, h01 ⟩
  step as ⟨ abcd10, efgh10, h10, h11 ⟩
  step as ⟨ abcd20, efgh20, h20, h21 ⟩
  step as ⟨ abcd30, efgh30, h30, h31 ⟩
  rw [h00, h01, h10, h11, h20, h21, h30, h31]
  step with hash_pairs_x4_loop1.spec as
    ⟨ ab0, cd0, ab1, cd1, ab2, cd2, ab3, cd3, t0', t1', t2', t3', hab0, hcd0, hab1, hcd1,
      hab2, hcd2, hab3, hcd3, f0, f1, f2, f3 ⟩
  simp only [Nat.reduceMul, Kfrom_end, rounds] at e0 e1 e2 e3 f0 f1 f2 f3
  subst f0 f1 f2 f3
  rw [hab0, hcd0, hab1, hcd1, hab2, hcd2, hab3, hcd3]
  step with digest.spec as ⟨ x, hx ⟩
  step with digest.spec as ⟨ y, hy ⟩
  step with digest.spec as ⟨ z, hz ⟩
  step with digest.spec as ⟨ w, hw ⟩
  rw [hx, hy, hz, hw, combine_eq, combine_eq, combine_eq, combine_eq, pairState, pairState,
    pairState, pairState, e0, e1, e2, e3]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## A tree layer -/

theorem source_eq (in_place : Bool) (below level : Slice Node) :
    neon.source in_place below level = ok (sourceOf in_place below level) := by
  cases in_place <;> rfl

@[step]
theorem sibling.spec (nodes : Slice Node) (k : Std.Usize) (zero : Node)
    (h : 2 * k.val + 1 ≤ Usize.max) :
    neon.sibling nodes k zero ⦃ r => r = nodes.val[2 * k.val + 1]?.getD zero ⦄ := by
  unfold neon.sibling
  step as ⟨ i, hi ⟩
  step as ⟨ i1, hi1 ⟩
  spec_split
  · step as ⟨ i3, hi3 ⟩
    step as ⟨ r, hr ⟩
    rw [getElem?_of_eq nodes.val i3.val (2 * k.val + 1) (by scalar_tac) r hr (by scalar_tac)]
    rfl
  · simp only [WP.spec_ok]
    rw [List.getElem?_eq_none (by scalar_tac)]
    rfl

/-- The loop of `hash_layer`: four parents per iteration. It reads from `src` (the layer below
as it was at the start) and writes the parents into `level`. When hashing in place, what has
not been read yet (from `k` on) is still intact. -/
theorem hash_layer_loop.spec (below level : Slice Node) (in_place : Bool) (zero : Node)
    (total k : Std.Usize) (src : List Node)
    (hlen : (sourceOf in_place below level).length = src.length)
    (hsrc : ∀ j, k.val ≤ j → (sourceOf in_place below level).val[j]? = src[j]?)
    (htotal : 2 * total.val ≤ src.length + 1)
    (hk : k.val ≤ total.val) (hlevel : total.val ≤ level.length) :
    neon.hash_layer_loop below level in_place zero total k ⦃ r =>
      ∃ level' k', r = (level', k') ∧ level'.length = level.length ∧
        k.val ≤ k'.val ∧ k'.val ≤ total.val ∧ total.val < k'.val + 4 ∧
        (∀ j, k.val ≤ j → j < k'.val →
          (level'.val[j]?.map fun n => bytes n.val) = some (parentOf src zero j)) ∧
        (∀ j, j < k.val ∨ k'.val ≤ j → level'.val[j]? = level.val[j]?) ⦄ := by
  unfold neon.hash_layer_loop
  step as ⟨ i, hi ⟩
  spec_split
  · simp only [source_eq, bind_ok]
    have hsl0 : (sourceOf in_place below level).val.length = src.length := hlen
    step as ⟨ i1, hi1 ⟩
    step as ⟨ a, ha ⟩
    step as ⟨ i2, hi2 ⟩
    step as ⟨ a1, ha1 ⟩
    step as ⟨ i3, hi3 ⟩
    step as ⟨ a2, ha2 ⟩
    step as ⟨ i4, hi4 ⟩
    step as ⟨ a3, ha3 ⟩
    step as ⟨ i5, hi5 ⟩
    step as ⟨ a4, ha4 ⟩
    step as ⟨ i6, hi6 ⟩
    step as ⟨ a5, ha5 ⟩
    step as ⟨ i7, hi7 ⟩
    step as ⟨ a6, ha6 ⟩
    step as ⟨ i8, hi8 ⟩
    step as ⟨ a7, ha7 ⟩
    step as ⟨ x, y, z, w, hx, hy, hz, hw ⟩
    step as ⟨ level1, hlevel1 ⟩
    step as ⟨ i9, hi9 ⟩
    step as ⟨ level2, hlevel2 ⟩
    step as ⟨ i10, hi10 ⟩
    step as ⟨ level3, hlevel3 ⟩
    have hl3 : level3.length = level.length := by
      rw [hlevel3, hlevel2, hlevel1]
      simp only [Slice.length, Slice.set_val_eq, List.length_set]
    step as ⟨ s, hs ⟩
    step as ⟨ k1, hk1 ⟩
    have hkt : k.val + 4 ≤ total.val := by scalar_tac
    have hs4 : ∀ j, s.val[j]? =
        if j = k.val then some x else if j = k.val + 1 then some y
        else if j = k.val + 2 then some z else if j = k.val + 3 then some w
        else level.val[j]? := by
      intro j
      rw [hs, hlevel3, hlevel2, hlevel1]
      exact set4_getElem? level k i9 i10 i8 x y z w (by scalar_tac) (by scalar_tac)
        (by scalar_tac) (by scalar_tac) j
    have hsl : s.length = level.length := by
      rw [hs, hlevel3, hlevel2, hlevel1]
      simp only [Slice.length, Slice.set_val_eq, List.length_set]
    have hget : ∀ j, (j < k.val ∨ k.val + 4 ≤ j) → s.val[j]? = level.val[j]? := by
      intro j hj
      rw [hs4 j]
      split_ifs <;> first | rfl | (exfalso; omega)
    apply WP.spec_mono (hash_layer_loop.spec below s in_place zero total k1 src
      (by rw [sourceOf_length in_place below level s hsl]; exact hlen)
      (by
        intro j hj
        rw [sourceOf_getElem? in_place below level s j (hget j (by omega))]
        exact hsrc j (by omega))
      htotal (by scalar_tac) (by scalar_tac))
    intro r ⟨ level', k', hr, hl', hkk, hkt', htk, hpar, hrest ⟩
    have hsrcAt := src_node below level in_place src k hsrc
    refine ⟨ level', k', hr, by omega, by omega, hkt', htk, ?_, ?_ ⟩
    · intro j hj1 hj2
      by_cases hjk : j < k.val + 4
      · rw [hrest j (Or.inl (by scalar_tac)), hs4 j]
        by_cases e0 : j = k.val
        · subst e0
          simp only [ite_true, Option.map_some, hx]
          rw [parentOf_eq src zero k.val a a1
            (hsrcAt i1 _ (by scalar_tac) a ha (by scalar_tac) (by scalar_tac))
            (by rw [hsrcAt i2 _ (by scalar_tac) a1 ha1 (by scalar_tac) (by scalar_tac)]; rfl)]
        · by_cases e1 : j = k.val + 1
          · subst e1
            simp only [e0, ite_false, ite_true, Option.map_some, hy]
            rw [parentOf_eq src zero (k.val + 1) a2 a3
              (hsrcAt i3 _ (by scalar_tac) a2 ha2 (by scalar_tac) (by scalar_tac))
              (by rw [hsrcAt i4 _ (by scalar_tac) a3 ha3 (by scalar_tac) (by scalar_tac)]; rfl)]
          · by_cases e2 : j = k.val + 2
            · subst e2
              simp only [e0, e1, ite_false, ite_true, Option.map_some, hz]
              rw [parentOf_eq src zero (k.val + 2) a4 a5
                (hsrcAt i5 _ (by scalar_tac) a4 ha4 (by scalar_tac) (by scalar_tac))
                (by rw [hsrcAt i6 _ (by scalar_tac) a5 ha5 (by scalar_tac) (by scalar_tac)]; rfl)]
            · have e3 : j = k.val + 3 := by omega
              subst e3
              simp only [e0, e1, e2, ite_false, ite_true, Option.map_some, hw]
              rw [parentOf_eq src zero (k.val + 3) a6 a7
                (hsrcAt i7 _ (by scalar_tac) a6 ha6 (by scalar_tac) (by scalar_tac))
                (by rw [← hsrc (2 * (k.val + 3) + 1) (by omega), ha7, hi8])]
      · exact hpar j (by scalar_tac) hj2
    · intro j hj
      rw [hrest j (by scalar_tac)]
      exact hget j (by scalar_tac)
  · simp only [WP.spec_ok]
    exact ⟨ level, k, rfl, rfl, Nat.le_refl _, hk, by scalar_tac, by intro j h1 h2; omega,
      by intro j _; rfl ⟩
termination_by total.val - k.val
decreasing_by scalar_decr_tac

/-- **A tree layer.** `hash_layer` reads the nodes of `level` (when hashing in place) or of
`below`, and leaves in the first `⌈n / 2⌉` slots of `level` the parents according to EthLib's
specification (`combine`, with `zero` as the sibling of the last node when `n` is odd). The
rest of `level` is unchanged. It does not fail. -/
theorem hash_layer.spec (below level : Slice Node) (in_place : Bool) (zero : Node)
    (h : (sourceOf in_place below level).length / 2 +
      (sourceOf in_place below level).length % 2 ≤ level.length) :
    neon.hash_layer below level in_place zero ⦃ r =>
      r.length = level.length ∧
      (∀ j, j < (sourceOf in_place below level).length / 2 +
            (sourceOf in_place below level).length % 2 →
          (r.val[j]?.map fun n => bytes n.val) =
            some (parentOf (sourceOf in_place below level).val zero j)) ∧
      (∀ j, (sourceOf in_place below level).length / 2 +
            (sourceOf in_place below level).length % 2 ≤ j →
          r.val[j]? = level.val[j]?) ⦄ := by
  unfold neon.hash_layer
  simp only [source_eq, bind_ok]
  step as ⟨ i, hi ⟩
  step as ⟨ i1, hi1 ⟩
  step as ⟨ total, htotal ⟩
  step with hash_layer_loop.spec below level in_place zero total 0#usize
    (sourceOf in_place below level).val as
    ⟨ r1, rk, level1, k, hr1, hrk, hl1, hkt, htk, hk0, hpar, hrest ⟩
  subst hr1 hrk
  have hsame : ∀ j, rk.val ≤ j →
      (sourceOf in_place below r1).val[j]? = (sourceOf in_place below level).val[j]? :=
    fun j hj => sourceOf_getElem? in_place below level r1 j (hrest j (Or.inr hj))
  have hsl1 : (sourceOf in_place below r1).length = (sourceOf in_place below level).length :=
    sourceOf_length in_place below level r1 hl1
  step as ⟨ i2, hi2 ⟩
  -- After the groups of four: one pair of parents, if two or three remain.
  apply WP.spec_bind (Pₘ := fun p : Slice Node × Std.Usize =>
    p.1.length = level.length ∧ rk.val ≤ p.2.val ∧ p.2.val ≤ total.val ∧
    total.val < p.2.val + 2 ∧
    (∀ j, j < p.2.val → (p.1.val[j]?.map fun n => bytes n.val) =
      some (parentOf (sourceOf in_place below level).val zero j)) ∧
    (∀ j, p.2.val ≤ j → p.1.val[j]? = level.val[j]?))
  · split
    · step as ⟨ i3, hi3 ⟩
      step as ⟨ a, ha ⟩
      step as ⟨ i4, hi4 ⟩
      step as ⟨ a1, ha1 ⟩
      step as ⟨ i5, hi5 ⟩
      step as ⟨ a2, ha2 ⟩
      step as ⟨ i6, hi6 ⟩
      step as ⟨ a3, ha3 ⟩
      step as ⟨ x, y, hx, hy ⟩
      step as ⟨ level3, hlevel3 ⟩
      step as ⟨ s1, hs1 ⟩
      step as ⟨ k2, hk2 ⟩
      have hkt2 : rk.val + 2 ≤ total.val := by scalar_tac
      have hsrcAt := src_node below r1 in_place (sourceOf in_place below level).val rk hsame
      refine ⟨ ?_, by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_ ⟩
      · rw [hs1, hlevel3]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl1
      · intro j hj
        by_cases hjk : j = rk.val
        · subst hjk
          rw [hs1, hlevel3, set2_first r1 rk i6 x y (by scalar_tac) (by scalar_tac)]
          simp only [Option.map_some, hx]
          rw [parentOf_eq _ zero rk.val a a1
            (hsrcAt i3 _ (by scalar_tac) a ha (by scalar_tac) (by scalar_tac))
            (by rw [hsrcAt i4 _ (by scalar_tac) a1 ha1 (by scalar_tac) (by scalar_tac)]; rfl)]
        · by_cases hjk1 : j = rk.val + 1
          · subst hjk1
            rw [hs1, hlevel3, ← hi6, set2_second r1 rk i6 x y (by scalar_tac)]
            simp only [Option.map_some, hy]
            rw [hi6, parentOf_eq _ zero (rk.val + 1) a2 a3
              (hsrcAt i5 _ (by scalar_tac) a2 ha2 (by scalar_tac) (by scalar_tac))
              (by rw [← hsame (2 * (rk.val + 1) + 1) (by omega), ha3, hi6])]
          · rw [hs1, hlevel3, set2_other r1 rk i6 x y j hjk (by scalar_tac)]
            exact hpar j (Nat.zero_le _) (by scalar_tac)
      · intro j hj
        rw [hs1, hlevel3, set2_other r1 rk i6 x y j (by scalar_tac) (by scalar_tac)]
        exact hrest j (Or.inr (by scalar_tac))
    · simp only [WP.spec_ok]
      exact ⟨ hl1, Nat.le_refl _, htk, by scalar_tac,
        fun j hj => hpar j (Nat.zero_le _) hj, fun j hj => hrest j (Or.inr hj) ⟩
  · -- And one last parent, if one remains.
    intro ⟨ r2, k1 ⟩ ⟨ hl2, hk1a, hk1b, hk1c, hpar2, hrest2 ⟩
    dsimp only at hl2 hk1a hk1b hk1c hpar2 hrest2
    have hsame2 : ∀ j, k1.val ≤ j →
        (sourceOf in_place below r2).val[j]? = (sourceOf in_place below level).val[j]? :=
      fun j hj => sourceOf_getElem? in_place below level r2 j (hrest2 j hj)
    have hsl2 : (sourceOf in_place below r2).length = (sourceOf in_place below level).length :=
      sourceOf_length in_place below level r2 hl2
    step as ⟨ i3, hi3 ⟩
    spec_split
    · rename_i _ hone
      have hone' : i3.val = 1 := by rw [hone]; rfl
      step as ⟨ i4, hi4 ⟩
      step as ⟨ a, ha ⟩
      step as ⟨ a1, ha1 ⟩
      step as ⟨ x, hx ⟩
      step as ⟨ r, hr ⟩
      have hkk : k1.val + 1 = total.val := by omega
      refine ⟨ ?_, ?_, ?_ ⟩
      · rw [hr]; simp only [Slice.length, Slice.set_val_eq, List.length_set]; exact hl2
      · intro j hj
        by_cases hjk : j = k1.val
        · subst hjk
          rw [hr, Slice.set_val_eq, List.getElem?_set_self (by scalar_tac)]
          simp only [Option.map_some, hx]
          rw [parentOf_eq _ zero k1.val a a1]
          · rw [← hsame2 (2 * k1.val) (by omega)]
            exact getElem?_of_eq _ i4.val _ (by scalar_tac) a ha (by scalar_tac)
          · rw [← hsame2 (2 * k1.val + 1) (by omega), ha1]
        · rw [hr, Slice.set_val_eq, List.getElem?_set_ne (Ne.symm hjk)]
          exact hpar2 j (by scalar_tac)
      · intro j hj
        rw [hr, Slice.set_val_eq, List.getElem?_set_ne (by scalar_tac)]
        exact hrest2 j (by scalar_tac)
    · simp only [WP.spec_ok]
      have hkk : k1.val = total.val := by scalar_tac
      refine ⟨ hl2, ?_, ?_ ⟩
      · intro j hj
        exact hpar2 j (by scalar_tac)
      · intro j hj
        exact hrest2 j (by scalar_tac)

end Libssz.MerkleNeon
