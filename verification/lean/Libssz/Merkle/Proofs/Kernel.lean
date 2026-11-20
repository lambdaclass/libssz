module
public import Libssz.Merkle.Code.Funs
public import Libssz.Merkle.Proofs.Pair
public import Libssz.Proofs.Bytes
public import EthLib.Serialization.Ssz.Merkle.Tree
@[expose] public section

open Aeneas Aeneas.Std Result
open EthLib.Cryptography.Hash.Sha256
open libssz_merkle
open Libssz.Proofs (byte bytes)

namespace Libssz.Merkle

/-! ## The intrinsics, as equations -/

@[simp] theorem msg1_eq (a b : M128) :
    core.core_arch.x86.sha._mm_sha256msg1_epu32 a b = ok (_mm_sha256msg1_epu32 a b) := rfl
@[simp] theorem msg2_eq (a b : M128) :
    core.core_arch.x86.sha._mm_sha256msg2_epu32 a b = ok (_mm_sha256msg2_epu32 a b) := rfl
@[simp] theorem rnds2_eq (a b k : M128) :
    core.core_arch.x86.sha._mm_sha256rnds2_epu32 a b k = ok (_mm_sha256rnds2_epu32 a b k) := rfl
@[simp] theorem add_eq (a b : M128) :
    core.core_arch.x86.sse2._mm_add_epi32 a b = ok (_mm_add_epi32 a b) := rfl
@[simp] theorem shuffle_eq (imm : Std.I32) (a : M128) :
    core.core_arch.x86.sse2._mm_shuffle_epi32 imm a = ok (_mm_shuffle_epi32 imm.bv.toNat a) := rfl
@[simp] theorem alignr_eq (imm : Std.I32) (a b : M128) :
    core.core_arch.x86.ssse3._mm_alignr_epi8 imm a b = ok (_mm_alignr_epi8 imm.bv.toNat a b) := rfl
@[simp] theorem black_box_eq {T : Type} (x : T) : core.hint.black_box x = ok x := rfl

/-! ## Words -/

/-- A Rust `u32` as a `UInt32`: the same 32 bits. -/
def u32 (x : Std.U32) : UInt32 := UInt32.ofBitVec x.bv

/-- The `as i32` that `_mm_set_epi32` requires does not change the bits. -/
theorem cast_i32 (w : Std.U32) :
    (Int32.ofBitVec (UScalar.hcast IScalarTy.I32 w).bv).toUInt32 = u32 w := by
  apply UInt32.toBitVec_inj.mp
  simp only [u32, UScalar.hcast_bv_eq]
  exact BitVec.setWidth_eq w.bv

theorem words_eq (w3 w2 w1 w0 : Std.U32) :
    shani.words w3 w2 w1 w0 = ok #v[u32 w0, u32 w1, u32 w2, u32 w3] := by
  simp only [shani.words, lift, bind_ok, core.core_arch.x86.sse2._mm_set_epi32, _mm_set_epi32,
    cast_i32]

/-- A row of four `u32` as lanes: the first one in lane 0. -/
def rowOf (r : List Std.U32) : M128 := #v[u32 r[0]!, u32 r[1]!, u32 r[2]!, u32 r[3]!]

@[step]
theorem row.spec (r : Array Std.U32 4#usize) : shani.row r ⦃ m => m = rowOf r.val ⦄ := by
  unfold shani.row
  step as ⟨ i, hi ⟩
  step as ⟨ i1, hi1 ⟩
  step as ⟨ i2, hi2 ⟩
  step as ⟨ i3, hi3 ⟩
  simp only [words_eq, WP.spec_ok, rowOf, hi, hi1, hi2, hi3]
  simp

/-! ## The two tables -/

/-- The `K` table of `shani.rs` is EthLib's constants, four at a time. -/
theorem K_row (q : Nat) (h : q < 16) : rowOf (shani.K.val[q]!).val = Krow q := by
  unfold shani.K
  interval_cases q <;> decide +kernel

/-- The `PAD_WK` table of `shani.rs` is the schedule of the padding block, with the constants
already added. -/
theorem PAD_WK_row (q : Nat) (h : q < 16) :
    rowOf (shani.PAD_WK.val[q]!).val = _mm_add_epi32 (quad0 (padW q)) (Krow q) := by
  unfold shani.PAD_WK
  interval_cases q <;> decide +kernel

/-! ## Reading the block -/

/-- Four big-endian bytes, as bit vectors. -/
theorem fromBE4 (x0 x1 x2 x3 : BitVec 8) :
    BitVec.fromLEBytes [x3, x2, x1, x0]
      = x0.setWidth 32 <<< 24 ||| x1.setWidth 32 <<< 16 ||| x2.setWidth 32 <<< 8 |||
        x3.setWidth 32 := by
  dsimp only [BitVec.fromLEBytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  ext i hi
  interval_cases i <;> simp

/-- `u32::from_be_bytes` is EthLib's `big32`. -/
theorem from_be_bytes_eq (b0 b1 b2 b3 : Std.U8) :
    u32 (core.num.U32.from_be_bytes (Array.make 4#usize [b0, b1, b2, b3]))
      = big32 (byte b0) (byte b1) (byte b2) (byte b3) := by
  apply UInt32.toBitVec_inj.mp
  show BitVec.fromLEBytes [b3.bv, b2.bv, b1.bv, b0.bv] = _
  rw [fromBE4]
  simp [big32, byte]

theorem getD_map_byte (l : List Std.U8) (j : Nat) (h : j < l.length) :
    (l.map byte)[j]?.getD 0 = byte l[j] := by
  simp [h]

@[step]
theorem be_word.spec (d : Array Std.U8 32#usize) (pos : Std.Usize) (h : pos.val + 4 ≤ 32) :
    shani.be_word d pos ⦃ r => u32 r = wordAt (d.val.map byte) pos.val ⦄ := by
  have hl : d.val.length = 32 := by scalar_tac
  unfold shani.be_word
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

/-- Four consecutive words, the first one in lane 0. -/
def quadAt (l : List UInt8) (j : Nat) : M128 :=
  #v[wordAt l j, wordAt l (j + 4), wordAt l (j + 8), wordAt l (j + 12)]

@[step]
theorem be_words.spec (d : Array Std.U8 32#usize) (pos : Std.Usize) (h : pos.val + 16 ≤ 32) :
    shani.be_words d pos ⦃ r => r = quadAt (d.val.map byte) pos.val ⦄ := by
  unfold shani.be_words
  step as ⟨ i, hi ⟩
  step as ⟨ i1, hi1 ⟩
  step as ⟨ i2, hi2 ⟩
  step as ⟨ i3, hi3 ⟩
  step as ⟨ i4, hi4 ⟩
  step as ⟨ i5, hi5 ⟩
  step as ⟨ i6, hi6 ⟩
  simp only [words_eq, WP.spec_ok, quadAt, hi1, hi3, hi5, hi6, hi, hi2, hi4]

/-! ## The state of a hash in progress -/

/-- What a `Stream` of `shani.rs` holds: the working variables and the 16 current schedule
words. -/
def streamOf (s : State) (w : Window) : shani.Stream :=
  { abef := abef s, cdgh := cdgh s, w0 := quad0 w, w1 := quad1 w, w2 := quad2 w, w3 := quad3 w }

/-- The 16 words of the block formed by two consecutive nodes. -/
def pairWindow (a b : Array Std.U8 32#usize) : Window :=
  windowAt (a.val.map byte ++ b.val.map byte) 0

theorem pairWindow_quads (a b : Array Std.U8 32#usize) :
    quad0 (pairWindow a b) = quadAt (a.val.map byte) 0 ∧
    quad1 (pairWindow a b) = quadAt (a.val.map byte) 16 ∧
    quad2 (pairWindow a b) = quadAt (b.val.map byte) 0 ∧
    quad3 (pairWindow a b) = quadAt (b.val.map byte) 16 := by
  have hA : (a.val.map byte).length = 32 := by simp
  have hl : ∀ j, j + 4 ≤ 32 →
      wordAt (a.val.map byte ++ b.val.map byte) j = wordAt (a.val.map byte) j :=
    fun j hj => wordAt_append_left _ _ j (by omega)
  have hr : ∀ j, wordAt (a.val.map byte ++ b.val.map byte) (32 + j) = wordAt (b.val.map byte) j := by
    intro j
    have h := wordAt_append_right (a.val.map byte) (b.val.map byte) j
    rw [hA] at h
    exact h
  have h32 := hr 0
  have h36 := hr 4
  have h40 := hr 8
  have h44 := hr 12
  have h48 := hr 16
  have h52 := hr 20
  have h56 := hr 24
  have h60 := hr 28
  simp only [Nat.reduceAdd] at h32 h36 h40 h44 h48 h52 h56 h60
  simp (disch := omega) only [pairWindow, windowAt, quad0, quad1, quad2, quad3, quadAt,
    Nat.zero_add, Nat.reduceAdd, hl, h32, h36, h40, h44, h48, h52, h56, h60, and_self]

theorem iv_abef :
    (#v[u32 2600822924#u32, u32 1359893119#u32, u32 3144134277#u32, u32 1779033703#u32] : M128)
      = abef initial := by decide +kernel

theorem iv_cdgh :
    (#v[u32 1541459225#u32, u32 528734635#u32, u32 2773480762#u32, u32 1013904242#u32] : M128)
      = cdgh initial := by decide +kernel

@[step]
theorem start.spec (a b : Array Std.U8 32#usize) :
    shani.start a b ⦃ s => s = streamOf initial (pairWindow a b) ⦄ := by
  unfold shani.start
  simp only [words_eq, bind_ok, iv_abef, iv_cdgh]
  step as ⟨ m2, h2 ⟩
  step as ⟨ m3, h3 ⟩
  step as ⟨ m4, h4 ⟩
  step as ⟨ m5, h5 ⟩
  obtain ⟨ q0, q1, q2, q3 ⟩ := pairWindow_quads a b
  simp only [streamOf, q0, q1, q2, q3, h2, h3, h4, h5]

/-! ## Rounds -/

theorem four_rounds_eq (s : State) (wk : M128) :
    shani.four_rounds (abef s) (cdgh s) wk = ok (abef (quadStep s wk), cdgh (quadStep s wk)) := by
  have h := four_rounds_lanes s wk
  simp only [shani.four_rounds, rnds2_eq, shuffle_eq, bind_ok]
  rw [show (14#i32).bv.toNat = 0x0e from rfl, h.1, h.2]

/-- Four rounds and the next four schedule words. -/
@[step]
theorem scheduled_quad.spec (s : State) (w : Window) (quad : Std.Usize) (h : quad.val < 16) :
    shani.scheduled_quad (streamOf s w) quad ⦃ r =>
      r = streamOf (quadStep s (_mm_add_epi32 (quad0 w) (Krow quad.val))) (next4 w) ⦄ := by
  have hK := K_row quad.val h
  rw [getElem!_pos shani.K.val quad.val (by scalar_tac)] at hK
  unfold shani.scheduled_quad
  step as ⟨ a, ha ⟩
  step as ⟨ mi, hmi ⟩
  simp only [streamOf, add_eq, msg1_eq, msg2_eq, alignr_eq, bind_ok, four_rounds_eq,
    uncurry_apply_pair, WP.spec_ok]
  rw [show (4#i32).bv.toNat = 4 from rfl, quad3_next4, hmi, ha, hK]
  rfl

/-- The last 16 rounds of the block and the addition of the initial value. -/
@[step]
theorem finish_block.spec (s : State) (w : Window) :
    shani.finish_block (streamOf s w) ⦃ r =>
      r = (abef (feed initial (rounds (Kfrom 48) w s)),
        cdgh (feed initial (rounds (Kfrom 48) w s))) ⦄ := by
  have h12 := K_row 12 (by decide)
  have h13 := K_row 13 (by decide)
  have h14 := K_row 14 (by decide)
  have h15 := K_row 15 (by decide)
  rw [getElem!_pos shani.K.val 12 (by scalar_tac)] at h12
  rw [getElem!_pos shani.K.val 13 (by scalar_tac)] at h13
  rw [getElem!_pos shani.K.val 14 (by scalar_tac)] at h14
  rw [getElem!_pos shani.K.val 15 (by scalar_tac)] at h15
  unfold shani.finish_block
  step as ⟨ a, ha ⟩
  step as ⟨ mi, hmi ⟩
  simp only [streamOf, add_eq, bind_ok, four_rounds_eq, uncurry_apply_pair, words_eq, iv_abef,
    iv_cdgh, add_abef, add_cdgh]
  step as ⟨ a1, ha1 ⟩
  step as ⟨ mi2, hmi2 ⟩
  step as ⟨ a2, ha2 ⟩
  step as ⟨ mi4, hmi4 ⟩
  step as ⟨ a3, ha3 ⟩
  step as ⟨ mi6, hmi6 ⟩
  rw [rounds_last, hmi, ha, hmi2, ha1, hmi4, ha2, hmi6, ha3, h12, h13, h14, h15]
  exact ⟨rfl, rfl⟩

/-! ## The two loops of the single-pair hash -/

/-- The first 48 rounds of the first block: the ones that still compute the schedule. -/
theorem hash_pair_loop0.spec (s : State) (w : Window) (quad : Std.Usize) (hq : quad.val ≤ 12) :
    shani.hash_pair_loop0 (streamOf s w) quad ⦃ r =>
      ∃ s' w', r = streamOf s' w' ∧
        rounds (Kfrom (4 * quad.val)) w s = rounds (Kfrom 48) w' s' ⦄ := by
  unfold shani.hash_pair_loop0
  spec_split
  · step as ⟨ s1, hs1 ⟩
    step as ⟨ quad1, hquad1 ⟩
    rw [hs1]
    apply WP.spec_mono (hash_pair_loop0.spec _ _ quad1 (by scalar_tac))
    intro r ⟨ s', w', hr, h ⟩
    refine ⟨ s', w', hr, ?_ ⟩
    rw [rounds_Kfrom quad.val (by scalar_tac), ← h, hquad1]
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
        (quadStep t (rowOf (shani.PAD_WK.val[q]!).val)) := by
  rw [rounds_Kfrom q h, PAD_WK_row q h]
  rfl

/-- The 64 rounds of the padding block. -/
theorem hash_pair_loop1.spec (t : State) (quad : Std.Usize) (hq : quad.val ≤ 16) :
    shani.hash_pair_loop1 (abef t) (cdgh t) quad ⦃ r =>
      r = (abef (rounds (Kfrom (4 * quad.val)) (padW quad.val) t),
        cdgh (rounds (Kfrom (4 * quad.val)) (padW quad.val) t)) ⦄ := by
  unfold shani.hash_pair_loop1
  spec_split
  · step as ⟨ a, ha ⟩
    step as ⟨ mi, hmi ⟩
    simp only [four_rounds_eq, bind_ok, uncurry_apply_pair]
    step as ⟨ quad1, hquad1 ⟩
    apply WP.spec_mono (hash_pair_loop1.spec _ quad1 (by scalar_tac))
    intro r hr
    rw [hr, pad_quad quad.val (by scalar_tac), hquad1, hmi, ha,
      getElem!_pos shani.PAD_WK.val quad.val (by scalar_tac)]
  · simp only [WP.spec_ok]
    have h16 : quad.val = 16 := by scalar_tac
    rw [h16]
    rfl
termination_by 16 - quad.val
decreasing_by scalar_decr_tac

/-! ## The digest -/

@[simp] theorem extract_eq (imm : Std.I32) (a : M128) :
    core.core_arch.x86.sse41._mm_extract_epi32 imm a
      = ok ⟨(_mm_extract_epi32 imm.bv.toNat a).toBitVec⟩ := rfl

/-- Reading a lane with `_mm_extract_epi32` and converting it to `u32` does not change the bits. -/
theorem extract_u32 (imm : Std.I32) (v : M128) :
    u32 (IScalar.hcast UScalarTy.U32 (⟨(_mm_extract_epi32 imm.bv.toNat v).toBitVec⟩ : Std.I32))
      = v[imm.bv.toNat % 4] := by
  apply UInt32.toBitVec_inj.mp
  simp only [u32, IScalar.hcast_bv_eq, _mm_extract_epi32]
  simp

theorem toBE4 (x : BitVec 32) :
    x.toBEBytes
      = [(x >>> 24).setWidth 8, (x >>> 16).setWidth 8, (x >>> 8).setWidth 8, x.setWidth 8] := by
  unfold BitVec.toBEBytes
  rw [BitVec.toLEBytes]
  simp only [show (32 : Nat) > 0 by omega, ↓reduceIte, Nat.reduceSub]
  rw [BitVec.toLEBytes]
  simp only [show (24 : Nat) > 0 by omega, ↓reduceIte, Nat.reduceSub]
  rw [BitVec.toLEBytes]
  simp only [show (16 : Nat) > 0 by omega, ↓reduceIte, Nat.reduceSub]
  rw [BitVec.toLEBytes]
  simp only [show (8 : Nat) > 0 by omega, ↓reduceIte, Nat.reduceSub]
  rw [BitVec.toLEBytes]
  simp only [show ¬ (0 : Nat) > 0 by omega, ↓reduceIte, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> (ext i hi; interval_cases i <;> simp)

/-- The four bytes of a word, most significant first. -/
def wordBytes (x : UInt32) : List UInt8 := [byteAt x 24, byteAt x 16, byteAt x 8, byteAt x 0]

theorem to_be_bytes_bytes (x : Std.U32) :
    (core.num.U32.to_be_bytes x).val.map byte = wordBytes (u32 x) := by
  simp only [core.num.U32.to_be_bytes, Array.from_val, toBE4, List.map_cons, List.map_nil,
    wordBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (apply UInt8.toBitVec_inj.mp; simp [byte, byteAt, u32])

/-- The four bytes that `digest` takes from a lane. -/
def laneBytes (v : M128) (imm : Std.I32) : Array Std.U8 4#usize :=
  core.num.U32.to_be_bytes
    (IScalar.hcast UScalarTy.U32 (⟨(_mm_extract_epi32 imm.bv.toNat v).toBitVec⟩ : Std.I32))

theorem laneBytes_def (v : M128) (imm : Std.I32) :
    laneBytes v imm = core.num.U32.to_be_bytes
      (IScalar.hcast UScalarTy.U32 (⟨(_mm_extract_epi32 imm.bv.toNat v).toBitVec⟩ : Std.I32)) :=
  rfl

theorem laneBytes_map (v : M128) (imm : Std.I32) :
    (laneBytes v imm).val.map byte = wordBytes v[imm.bv.toNat % 4] := by
  rw [laneBytes, to_be_bytes_bytes, extract_u32]

theorem list4 {α : Type} (l : List α) (h : l.length = 4) : l = [l[0], l[1], l[2], l[3]] := by
  match l, h with
  | [_, _, _, _], _ => rfl

theorem digest.spec (h t : State) :
    shani.digest (abef h) (cdgh h) (abef t) (cdgh t) ⦃ r =>
      bytes r.val = (digest (feed h t)).data ⦄ := by
  unfold shani.digest
  simp only [add_eq, add_abef, add_cdgh, extract_eq, lift, bind_ok, ← laneBytes_def]
  generalize hA : laneBytes (abef (feed h t)) 3#i32 = A
  generalize hB : laneBytes (abef (feed h t)) 2#i32 = B
  generalize hC : laneBytes (cdgh (feed h t)) 3#i32 = C
  generalize hD : laneBytes (cdgh (feed h t)) 2#i32 = D
  generalize hE : laneBytes (abef (feed h t)) 1#i32 = E
  generalize hF : laneBytes (abef (feed h t)) 0#i32 = F
  generalize hG : laneBytes (cdgh (feed h t)) 1#i32 = G
  generalize hH : laneBytes (cdgh (feed h t)) 0#i32 = H
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

/-- The specification's `combine`, on two 32-byte nodes: SHA-256 of a 64-byte message, that
is, two blocks. -/
theorem combine_eq (a b : Array Std.U8 32#usize) :
    EthLib.Serialization.Ssz.combine (bytes a.val) (bytes b.val)
      = (digest (pairState (pairWindow a b))).data := by
  have hsize : (ByteArray.mk (bytes a.val ++ bytes b.val)).size = 64 := by
    simp [ByteArray.size]
  have h := hash_block (ByteArray.mk (bytes a.val ++ bytes b.val)) hsize
  show (EthLib.Cryptography.Hash.Sha256.hash (ByteArray.mk (bytes a.val ++ bytes b.val))).data = _
  rw [h]
  simp [pairWindow, bytes]

/-- **`hash_pair` is the specification's `combine`.** -/
@[step]
theorem hash_pair.spec (a b : Array Std.U8 32#usize) :
    shani.hash_pair a b ⦃ r =>
      bytes r.val = EthLib.Serialization.Ssz.combine (bytes a.val) (bytes b.val) ⦄ := by
  unfold shani.hash_pair
  step as ⟨ s, hs ⟩
  rw [hs]
  step with hash_pair_loop0.spec as ⟨ s1, s', w', hs1, hr ⟩
  rw [hs1]
  step as ⟨ abef0, cdgh0, h0, h1 ⟩
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
    shani.hash_pairs_x2_loop0 scheduled (streamOf s0 w0) (streamOf s1 w1) turn ⦃ r =>
      ∃ s0' w0' s1' w1', r = (streamOf s0' w0', streamOf s1' w1') ∧
        rounds (Kfrom (4 * (4 * turn.val))) w0 s0
          = rounds (Kfrom (4 * (4 * scheduled.val))) w0' s0' ∧
        rounds (Kfrom (4 * (4 * turn.val))) w1 s1
          = rounds (Kfrom (4 * (4 * scheduled.val))) w1' s1' ⦄ := by
  unfold shani.hash_pairs_x2_loop0
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
    · rw [rounds_turn (4 * turn.val) (by scalar_tac)]
      exact e0
    · rw [rounds_turn (4 * turn.val) (by scalar_tac)]
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
          (rowOf (shani.PAD_WK.val[q]!).val))
          (rowOf (shani.PAD_WK.val[q + 1]!).val))
          (rowOf (shani.PAD_WK.val[q + 2]!).val))
          (rowOf (shani.PAD_WK.val[q + 3]!).val)) := by
  rw [pad_quad q (by omega), pad_quad (q + 1) (by omega), pad_quad (q + 2) (by omega),
    pad_quad (q + 3) (by omega)]

/-- The 64 rounds of the padding block of the two hashes, interleaved 16 at a time. -/
theorem hash_pairs_x2_loop1.spec (padded : Std.Usize) (t0 t1 : State) (turn : Std.Usize)
    (hp : padded.val ≤ 4) (ht : turn.val ≤ padded.val) :
    shani.hash_pairs_x2_loop1 padded (abef t0) (cdgh t0) (abef t1) (cdgh t1) turn ⦃ r =>
      ∃ t0' t1', r = (abef t0', cdgh t0', abef t1', cdgh t1') ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t0
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t0' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t1
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t1' ⦄ := by
  unfold shani.hash_pairs_x2_loop1
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
    have ek : wk = rowOf (shani.PAD_WK.val[4 * turn.val]!).val := by
      rw [hwk, ha, ← getElem!_pos shani.PAD_WK.val i.val (by scalar_tac), hi]
    have ek1 : wk1 = rowOf (shani.PAD_WK.val[4 * turn.val + 1]!).val := by
      rw [hwk1, ha1, ← getElem!_pos shani.PAD_WK.val i1.val (by scalar_tac), hi1, hi]
    have ek2 : wk2 = rowOf (shani.PAD_WK.val[4 * turn.val + 2]!).val := by
      rw [hwk2, ha2, ← getElem!_pos shani.PAD_WK.val i2.val (by scalar_tac), hi2, hi]
    have ek3 : wk3 = rowOf (shani.PAD_WK.val[4 * turn.val + 3]!).val := by
      rw [hwk3, ha3, ← getElem!_pos shani.PAD_WK.val i3.val (by scalar_tac), hi3, hi]
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
    shani.hash_pairs_x2 a0 b0 a1 b1 ⦃ x y =>
      bytes x.val = EthLib.Serialization.Ssz.combine (bytes a0.val) (bytes b0.val) ∧
      bytes y.val = EthLib.Serialization.Ssz.combine (bytes a1.val) (bytes b1.val) ⦄ := by
  unfold shani.hash_pairs_x2
  simp only [black_box_eq, bind_ok]
  step as ⟨ s0, hs0 ⟩
  step as ⟨ s1, hs1 ⟩
  rw [hs0, hs1]
  step with hash_pairs_x2_loop0.spec as ⟨ r0, r1, s0', w0', s1', w1', hr0, hr1, e0, e1 ⟩
  rw [hr0, hr1]
  step as ⟨ abef00, cdgh00, h00, h01 ⟩
  step as ⟨ abef10, cdgh10, h10, h11 ⟩
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
    shani.hash_pairs_x4_loop0 scheduled (streamOf s0 w0) (streamOf s1 w1) (streamOf s2 w2)
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
  unfold shani.hash_pairs_x4_loop0
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
    · rw [rounds_turn (4 * turn.val) (by scalar_tac)]
      exact e0
    · rw [rounds_turn (4 * turn.val) (by scalar_tac)]
      exact e1
    · rw [rounds_turn (4 * turn.val) (by scalar_tac)]
      exact e2
    · rw [rounds_turn (4 * turn.val) (by scalar_tac)]
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
    shani.hash_pairs_x4_loop1 padded (abef t0) (cdgh t0) (abef t1) (cdgh t1) (abef t2)
      (cdgh t2) (abef t3) (cdgh t3) turn ⦃ r =>
      ∃ t0' t1' t2' t3', r = (abef t0', cdgh t0', abef t1', cdgh t1', abef t2', cdgh t2',
          abef t3', cdgh t3') ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t0
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t0' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t1
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t1' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t2
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t2' ∧
        rounds (Kfrom (4 * (4 * turn.val))) (padW (4 * turn.val)) t3
          = rounds (Kfrom (4 * (4 * padded.val))) (padW (4 * padded.val)) t3' ⦄ := by
  unfold shani.hash_pairs_x4_loop1
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
    have ek : wk = rowOf (shani.PAD_WK.val[4 * turn.val]!).val := by
      rw [hwk, ha, ← getElem!_pos shani.PAD_WK.val i.val (by scalar_tac), hi]
    have ek1 : wk1 = rowOf (shani.PAD_WK.val[4 * turn.val + 1]!).val := by
      rw [hwk1, ha1, ← getElem!_pos shani.PAD_WK.val i1.val (by scalar_tac), hi1, hi]
    have ek2 : wk2 = rowOf (shani.PAD_WK.val[4 * turn.val + 2]!).val := by
      rw [hwk2, ha2, ← getElem!_pos shani.PAD_WK.val i2.val (by scalar_tac), hi2, hi]
    have ek3 : wk3 = rowOf (shani.PAD_WK.val[4 * turn.val + 3]!).val := by
      rw [hwk3, ha3, ← getElem!_pos shani.PAD_WK.val i3.val (by scalar_tac), hi3, hi]
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
    shani.hash_pairs_x4 a0 b0 a1 b1 a2 b2 a3 b3 ⦃ x y z w =>
      bytes x.val = EthLib.Serialization.Ssz.combine (bytes a0.val) (bytes b0.val) ∧
      bytes y.val = EthLib.Serialization.Ssz.combine (bytes a1.val) (bytes b1.val) ∧
      bytes z.val = EthLib.Serialization.Ssz.combine (bytes a2.val) (bytes b2.val) ∧
      bytes w.val = EthLib.Serialization.Ssz.combine (bytes a3.val) (bytes b3.val) ⦄ := by
  unfold shani.hash_pairs_x4
  simp only [black_box_eq, bind_ok]
  step as ⟨ s0, hs0 ⟩
  step as ⟨ s1, hs1 ⟩
  step as ⟨ s2, hs2 ⟩
  step as ⟨ s3, hs3 ⟩
  rw [hs0, hs1, hs2, hs3]
  step with hash_pairs_x4_loop0.spec as ⟨ r0, r1, r2, r3, s0', w0', s1', w1', s2', w2', s3', w3',
    hr0, hr1, hr2, hr3, e0, e1, e2, e3 ⟩
  rw [hr0, hr1, hr2, hr3]
  step as ⟨ abef00, cdgh00, h00, h01 ⟩
  step as ⟨ abef10, cdgh10, h10, h11 ⟩
  step as ⟨ abef20, cdgh20, h20, h21 ⟩
  step as ⟨ abef30, cdgh30, h30, h31 ⟩
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

/-- A tree node: 32 bytes. -/
abbrev Node := Array Std.U8 32#usize

/-- The nodes a layer reads: those of `level` when hashing in place; otherwise, those of
`below`. -/
def sourceOf (in_place : Bool) (below level : Slice Node) : Slice Node :=
  if in_place then level else below

theorem source_eq (in_place : Bool) (below level : Slice Node) :
    shani.source in_place below level = ok (sourceOf in_place below level) := by
  cases in_place <;> rfl

theorem sourceOf_length (in_place : Bool) (below level level' : Slice Node)
    (h : level'.length = level.length) :
    (sourceOf in_place below level').length = (sourceOf in_place below level).length := by
  cases in_place <;> simp [sourceOf, h]

theorem sourceOf_getElem? (in_place : Bool) (below level level' : Slice Node) (j : Nat)
    (h : level'.val[j]? = level.val[j]?) :
    (sourceOf in_place below level').val[j]? = (sourceOf in_place below level).val[j]? := by
  cases in_place <;> simp [sourceOf, h]

/-- Parent `k` of a layer: the `combine` of nodes `2k` and `2k + 1`. If the layer has an odd
number of nodes, the last one has no sibling and `zero` takes its place. -/
def parentOf (src : List Node) (zero : Node) (k : Nat) : EthLib.Serialization.Ssz.Bytes :=
  EthLib.Serialization.Ssz.combine (bytes (src[2 * k]?.getD zero).val)
    (bytes (src[2 * k + 1]?.getD zero).val)

theorem parentOf_eq (src : List Node) (zero : Node) (k : Nat) (a b : Node)
    (ha : src[2 * k]? = some a) (hb : src[2 * k + 1]?.getD zero = b) :
    parentOf src zero k =
      EthLib.Serialization.Ssz.combine (bytes a.val) (bytes b.val) := by
  simp [parentOf, ha, hb]

/-- Writing two slots does not touch the others. -/
theorem set2_other (level : Slice Node) (k i4 : Std.Usize) (x y : Node) (j : Nat)
    (h : j ≠ k.val) (h' : j ≠ i4.val) :
    ((level.set k x).set i4 y).val[j]? = level.val[j]? := by
  simp only [Slice.set_val_eq]
  rw [List.getElem?_set_ne (Ne.symm h'), List.getElem?_set_ne (Ne.symm h)]

theorem set2_first (level : Slice Node) (k i4 : Std.Usize) (x y : Node)
    (h : k.val < level.length) (h' : i4.val ≠ k.val) :
    ((level.set k x).set i4 y).val[k.val]? = some x := by
  simp only [Slice.set_val_eq]
  rw [List.getElem?_set_ne h', List.getElem?_set_self h]

theorem set2_second (level : Slice Node) (k i4 : Std.Usize) (x y : Node)
    (h : i4.val < level.length) :
    ((level.set k x).set i4 y).val[i4.val]? = some y := by
  simp only [Slice.set_val_eq]
  rw [List.getElem?_set_self (by simpa using h)]

theorem getElem?_of_eq {α : Type} (l : List α) (i j : Nat) (h : i < l.length) (a : α)
    (ha : a = l[i]) (hij : i = j) : l[j]? = some a := by
  subst hij ha
  exact List.getElem?_eq_getElem h

@[step]
theorem sibling.spec (nodes : Slice Node) (k : Std.Usize) (zero : Node)
    (h : 2 * k.val + 1 ≤ Usize.max) :
    shani.sibling nodes k zero ⦃ r => r = nodes.val[2 * k.val + 1]?.getD zero ⦄ := by
  unfold shani.sibling
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

/-- Writing four consecutive slots, from `k` to `k + 3`: reads what was written there, and
what was there before everywhere else. -/
theorem set4_getElem? (level : Slice Node) (k i9 i10 i8 : Std.Usize) (x y z w : Node)
    (h9 : i9.val = k.val + 1) (h10 : i10.val = k.val + 2) (h8 : i8.val = k.val + 3)
    (hlen : k.val + 4 ≤ level.length) (j : Nat) :
    ((((level.set k x).set i9 y).set i10 z).set i8 w).val[j]? =
      if j = k.val then some x else if j = k.val + 1 then some y
      else if j = k.val + 2 then some z else if j = k.val + 3 then some w
      else level.val[j]? := by
  have hl : k.val + 4 ≤ level.val.length := hlen
  simp only [Slice.set_val_eq, List.getElem?_set, List.length_set, h9, h10, h8]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Node `j ≥ k` of the layer below, as read while hashing: it is the one in `src`. -/
theorem src_node (below level : Slice Node) (in_place : Bool) (src : List Node) (k : Std.Usize)
    (hsrc : ∀ j, k.val ≤ j → (sourceOf in_place below level).val[j]? = src[j]?)
    (i : Std.Usize) (j : Nat) (hi : i.val < (sourceOf in_place below level).val.length)
    (a : Node) (ha : a = (sourceOf in_place below level).val[i.val]) (hij : i.val = j)
    (hkj : k.val ≤ j) : src[j]? = some a := by
  rw [← hsrc j hkj]
  exact getElem?_of_eq _ i.val j hi a ha hij

/-- The loop of `hash_layer`: four parents per iteration. It reads from `src` (the layer below
as it was at the start) and writes the parents into `level`. When hashing in place, what has
not been read yet (from `k` on) is still intact. -/
theorem hash_layer_loop.spec (below level : Slice Node) (in_place : Bool) (zero : Node)
    (total k : Std.Usize) (src : List Node)
    (hlen : (sourceOf in_place below level).length = src.length)
    (hsrc : ∀ j, k.val ≤ j → (sourceOf in_place below level).val[j]? = src[j]?)
    (htotal : 2 * total.val ≤ src.length + 1)
    (hk : k.val ≤ total.val) (hlevel : total.val ≤ level.length) :
    shani.hash_layer_loop below level in_place zero total k ⦃ r =>
      ∃ level' k', r = (level', k') ∧ level'.length = level.length ∧
        k.val ≤ k'.val ∧ k'.val ≤ total.val ∧ total.val < k'.val + 4 ∧
        (∀ j, k.val ≤ j → j < k'.val →
          (level'.val[j]?.map fun n => bytes n.val) = some (parentOf src zero j)) ∧
        (∀ j, j < k.val ∨ k'.val ≤ j → level'.val[j]? = level.val[j]?) ⦄ := by
  unfold shani.hash_layer_loop
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
    shani.hash_layer below level in_place zero ⦃ r =>
      r.length = level.length ∧
      (∀ j, j < (sourceOf in_place below level).length / 2 +
            (sourceOf in_place below level).length % 2 →
          (r.val[j]?.map fun n => bytes n.val) =
            some (parentOf (sourceOf in_place below level).val zero j)) ∧
      (∀ j, (sourceOf in_place below level).length / 2 +
            (sourceOf in_place below level).length % 2 ≤ j →
          r.val[j]? = level.val[j]?) ⦄ := by
  unfold shani.hash_layer
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

end Libssz.Merkle
