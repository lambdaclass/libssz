module
public import Libssz.Proofs.Container
public import EthLib.Serialization.Proofs.Ssz.Codec.Loops
@[expose] public section

/-!
# Fixed-size consensus-layer containers, libssz ≡ EthLib

For a struct whose fields are all fixed-size, `ssz-derive` uses neither `ContainerEncoder` nor
`ContainerDecoder`. The decode checks that the length is the sum of the widths and cuts each
field with `split_at`. The encode does not append the fields one after another either: since
every field knows how to write itself in place (`ssz_has_write_fixed`), `ssz_append` grows
the buffer once and `ssz_write_fixed` writes each field into its segment, cutting with
`split_at_mut`.

* On the EthLib side, `eth_decode_fixed` and `eth_encode_fixed` hold for any list of fixed
  fields: the exact length (`scope`), and then `deserializeFields` on the chunks (`cuts`), or
  the concatenation of the encodings.
* On the Rust side, the `fixed_field` tactic walks one field of the decode's `split_at` chain.
  For the encode, `append_via_write_fixed` reduces the derived `ssz_append` to its
  `ssz_write_fixed`, and each `S.ssz_write_fixed.bytes_spec` states which bytes it leaves in
  the segment.
* `Checkpoint` is written by hand. `Fork`, `BeaconBlockHeader`, `Validator` and
  `AttestationData` come from `scripts/gen_fixed.py`, from the list of fields.
  `AttestationData` uses the `Checkpoint` theorem for its two `Checkpoint` fields.

The decodes are exact (`Agrees` with `ErrMatch`), for every input shorter than 2³² bytes.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz_codec
open Libssz.Proofs

namespace Libssz.Proofs

/-! ## EthLib: a container of fixed-size fields -/

/-- The chunks of the input for fields of widths `ws`, starting at position `p`. -/
def cuts (data : Bytes) : Nat → List Nat → List Bytes
  | _, [] => []
  | p, w :: ws => data.extract p (p + w) :: cuts data (p + w) ws

theorem fieldsFixedSize_of : ∀ (fields : List Desc) (ws : List Nat),
    fields.map Desc.fixedSize = ws.map some → Desc.fieldsFixedSize fields = some ws.sum
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | f :: fs, w :: ws, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Desc.fieldsFixedSize, h.1, fieldsFixedSize_of fs ws h.2]
    simp

theorem readSlots_fixed : ∀ (fields : List Desc) (ws : List Nat),
    fields.map Desc.fixedSize = ws.map some → ∀ (data : Bytes) (p : Nat),
    p + ws.sum ≤ data.size →
    readSlots fields data p = .ok ((cuts data p ws).map Slot.inline, p + ws.sum)
  | [], [], _, _, p, _ => by simp [readSlots, cuts]
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | f :: fs, w :: ws, h, data, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.sum_cons] at hp
    rw [readSlots, h.1]
    simp only [show ¬ (p + w > data.size) by omega, ↓reduceIte]
    rw [readSlots_fixed fs ws h.2 data (p + w) (by omega)]
    simp only [cuts, List.map_cons, List.sum_cons, Nat.add_assoc]
    rfl

theorem bodyStarts_inline : ∀ (l : List Bytes), bodyStarts (l.map Slot.inline) = []
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, bodyStarts]; exact bodyStarts_inline l

theorem held_inline (l : List Bytes) : (l.map Slot.inline).map Slot.held = l := by
  simp [Function.comp_def, Slot.held]

/-- **Decode of a fixed-size container in EthLib**: the length must be exactly the sum of the
widths, and then each field is decoded in its chunk, in order. -/
theorem eth_decode_fixed (names : List String) (fields : List Desc) (ws : List Nat)
    (hw : fields.map Desc.fixedSize = ws.map some) (data : Bytes) (hsz : data.size < 2 ^ 32) :
    deserialize (.container names fields) data =
      if data.size ≠ ws.sum then .error (.scope ws.sum data.size)
      else match deserializeFields fields (cuts data 0 ws) with
        | .ok vs => .ok (.seq vs)
        | .error e => .error e := by
  conv_lhs => rw [deserialize]
  conv_lhs => rw [deserializeStruct]
  simp only [structSlots, show ¬ (data.size ≥ 2 ^ (8 * bytesPerOffset)) by
    simp [bytesPerOffset]; omega, ↓reduceIte, structBudget, fieldsFixedSize_of fields ws hw]
  by_cases hne : data.size ≠ ws.sum
  · simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte, bne_iff_ne]
    rfl
  · have heq : data.size = ws.sum := by omega
    simp only [hne, ↓reduceIte, heq, bne_self_eq_false, Bool.false_eq_true, ex_ok_bind]
    rw [readSlots_fixed fields ws hw data 0 (by omega)]
    simp only [ex_ok_bind, bodyStarts_inline, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, structBodies, Nat.zero_add, heq, bne_self_eq_false,
      held_inline]
    show (do let slices ← (pure (cuts data 0 ws) : Except Err (List Bytes))
             deserializeFields fields slices) >>= (fun vs => pure (Value.seq vs)) = _
    simp only [pure, Except.pure, ex_ok_bind]
    cases deserializeFields fields (cuts data 0 ws) <;> simp <;> rfl

/-- **Encode of a fixed-size container in EthLib**: the encodings of the fields, one after
another, if the total is shorter than 2³². -/
theorem eth_encode_fixed (names : List String) (fields : List Desc) (vs : List Value)
    (parts : List Bytes) (hfix : fields.map Desc.isFixed = parts.map fun _ => true)
    (hser : serializeFields fields vs = .ok parts) (hsz : (concatParts parts).size < 2 ^ 32) :
    serialize (.container names fields) (.seq vs) = .ok (concatParts parts) := by
  rw [serialize]
  simp only [serializeStruct, hser, ex_ok_bind]
  rw [hfix, assemble_inline_eq]
  simp only [show ¬ ((concatParts parts).size ≥ 2 ^ (8 * bytesPerOffset)) by
    simp [bytesPerOffset]; omega, ↓reduceIte]

/-! ## On the Rust side -/

theorem bytes_take_drop (l : List Std.U8) (p w : Nat) :
    bytes ((l.drop p).take w) = (bytes l).extract p (p + w) := by
  rw [bytes_extract]; simp

theorem bytes_take (l : List Std.U8) (w : Nat) : bytes (l.take w) = (bytes l).extract 0 w := by
  simpa using bytes_take_drop l 0 w

/-- One field of the `split_at` chain of the fixed-size decode generated by `ssz-derive`.

`prev` is the proof that the slice being cut is `s.val.drop p`. It cuts `sl` and `rest`
(with `hrest : rest.val = s.val.drop (p + w)`), decodes `sl` with `spec` and compares with the
`deserialize` of the field in EthLib: if it fails, it closes the goal with `ErrMatch`;
otherwise, it replaces that `deserialize` with its value. -/
syntax "fixed_field " ident ident ident " := " term ", " term " from " term " using " term
  (" with " term)? : tactic

macro_rules
  | `(tactic| fixed_field $sl $rest $hrest := $cur, $w from $prev using $spec $[with $h?]?) => do
    let h ← match h? with
      | some h => pure h
      | none => `(Nat.add_zero)
    let bi (i : Lean.TSyntax `ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i.raw]⟩
    let slB := bi sl
    let restB := bi rest
    let hrestB := bi hrest
    `(tactic| (
      step with core.slice.Slice.split_at.spec $cur $w
        (by rw [Slice.length, $prev:term, List.length_drop]; scalar_tac)
        as ⟨ $slB, $restB, hsll, _, hsl, $hrestB ⟩
      rw [$prev:term] at hsl
      rw [$prev:term, List.drop_drop] at $hrest:ident
      step with $spec $sl
        (by simp only [Slice.length, hsl, List.length_take, List.length_drop]; scalar_tac)
        as ⟨ x, hx ⟩
      simp only [hsl, bytes_take_drop, Nat.reduceAdd, $h:term] at hx
      try simp only [$h:term] at $hrest:ident
      rcases x with v | e
      swap
      · obtain ⟨e', he', hm⟩ := Agrees.err_eq hx
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, he', ex_error_bind, Agrees]
        try exact hm
      try simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Agrees.ok_eq hx,
        ex_ok_bind]))

/-- The decodes of each field type, in the form used by `fixed_field`. -/
theorem U64.dec (s : Slice Std.U8) (_ : s.length < 2 ^ 32) :
    U64.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees (fun x : Std.U64 => .uint x.val) r (deserialize Desc.uint64 (bytes s.val)) ⦄ :=
  U64.from_ssz_bytes.spec s

theorem Bool.dec (s : Slice Std.U8) (_ : s.length < 2 ^ 32) :
    Bool.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees Value.bool r (deserialize .bool (bytes s.val)) ⦄ :=
  Bool.from_ssz_bytes.spec s

/-! ### The encodes of each field type -/

theorem U64.ser (x : Std.U64) : serialize Desc.uint64 (.uint x.val) = .ok (uintBytes 8 x.val) := by
  have := x.hBounds
  simp [serialize, Desc.uint64]
  scalar_tac

theorem Bool.ser (b : Bool) : serialize .bool (.bool b) = .ok (boolByte b) := by
  cases b <;> simp [serialize, boolByte]

theorem ArrayU8N.ser (N : Std.Usize) (hN : N.val < 2 ^ 32) (a : Array Std.U8 N) :
    serialize (.byteVector N.val) (.bytes (bytes a.val)) = .ok (bytes a.val) := by
  have ha : (bytes a.val).size = N.val := by simp
  have h32 : ¬ ((bytes a.val).size ≥ 2 ^ (8 * bytesPerOffset)) := by
    rw [ha, bytesPerOffset]; norm_num; exact hN
  simp only [serialize, ha, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hltN : ¬ (2 ^ (8 * bytesPerOffset) ≤ N.val) := by rw [← ha]; omega
  simp only [hltN, ↓reduceIte]; rfl

/-- `ArrayU8N.ser` with the width as a number (`.byteVector 32` rather than
`.byteVector ↑32#usize`). -/
theorem ArrayU8N.ser' (n : Nat) (N : Std.Usize) (hn : N.val = n) (hN : n < 2 ^ 32)
    (a : Array Std.U8 N) :
    serialize (.byteVector n) (.bytes (bytes a.val)) = .ok (bytes a.val) := by
  subst hn; exact ArrayU8N.ser N hN a

theorem ArrayU8N.enc (N : Std.Usize) (hN : N.val < 2 ^ 32) (a : Array Std.U8 N)
    (buf : alloc.vec.Vec Std.U8) (h : buf.length + (bytes a.val).size ≤ Usize.max) :
    ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_append a buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ bytes a.val ⦄ := by
  have ha : (bytes a.val).size = N.val := by simp
  apply WP.spec_mono (ArrayU8N.ssz_append.spec N a buf hN (by rw [← ha]; exact h))
  rintro buf' ⟨enc, henc, hb⟩
  rw [ArrayU8N.ser N hN a] at henc
  cases henc
  exact hb

theorem Bool.enc (b : Bool) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (boolByte b).size ≤ Usize.max) :
    Bool.Insts.LibsszEncodeSszEncode.ssz_append b buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ boolByte b ⦄ :=
  Bool.ssz_append.bytes_spec b buf (by simp [boolByte] at h; omega)

theorem concatParts_two (a b : Bytes) : concatParts [a, b] = a ++ b := by simp [concatParts]

theorem bytes_len {b b' : alloc.vec.Vec Std.U8} {e : Bytes} (h : bytes b'.val = bytes b.val ++ e) :
    b'.val.length = b.val.length + e.size := by
  have := congrArg Array.size h; simpa [bytes] using this

/-! ### The direct-write path (`ssz_write_fixed`) -/

/-- `ssz_write_fixed` of `[u8; N]`, with the bytes it leaves written. -/
theorem ArrayU8N.wr (N : Std.Usize) (hN : N.val < 2 ^ 32) (a : Array Std.U8 N)
    (out : Slice Std.U8) (h : out.length = N.val) :
    ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_write_fixed a out ⦃ out' =>
      bytes out'.val = bytes a.val ⦄ := by
  apply WP.spec_mono (ArrayU8N.ssz_write_fixed.spec N a out hN h)
  rintro out' ⟨enc, henc, hb⟩
  rw [ArrayU8N.ser N hN a] at henc
  cases henc
  exact hb

/-- The length of a slice whose bytes are `e`. -/
theorem slice_len_of_bytes {s : Slice Std.U8} {e : Bytes} (h : bytes s.val = e) :
    s.length = e.size := by
  have := congrArg Array.size h; simpa [bytes] using this

/-- A computation satisfying `⦃ r => r = v ⦄` is `ok v`. -/
theorem ok_of_spec {α : Type} {m : Result α} {v : α} (h : m ⦃ r => r = v ⦄) : m = ok v := by
  cases m with
  | ret r => rw [WP.spec_ok] at h; rw [h]
  | vis e k => exact ((WP.spec_vis e k).mp h).elim
  | div => exact (WP.spec_div.mp h).elim

/-- **The direct-write path of the derived `ssz_append`**: grows the buffer by `w` bytes
(with any fill value; the code uses `0xff`), takes the new segment and writes the value there.
If `write` leaves `enc` in any `w`-byte segment, the buffer ends up with `enc` appended. -/
theorem append_via_write_fixed {T : Type} (write : T → Slice Std.U8 → Result (Slice Std.U8))
    (x : T) (enc : Bytes) (w : Std.Usize) (buf : alloc.vec.Vec Std.U8)
    (hsize : enc.size = w.val)
    (hwrite : ∀ out : Slice Std.U8, out.length = w.val →
      write x out ⦃ out' => bytes out'.val = enc ⦄)
    (h : buf.length + w.val ≤ Usize.max) :
    (do
      let __end ← alloc.vec.Vec.len buf + w
      let buf1 ← alloc.vec.Vec.resize core.clone.CloneU8 buf __end 255#u8
      let (s, index_mut_back) ←
        alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) buf1
          { start := alloc.vec.Vec.len buf, «end» := __end }
      let s1 ← write x s
      ok (index_mut_back s1)) ⦃ buf' => bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  have hbl : (alloc.vec.Vec.len buf).val = buf.length := by simp
  step as ⟨ e, he ⟩
  step with alloc.vec.Vec.resize_spec as ⟨ b1, hb1 ⟩
  have hb1v : b1.val = buf.val ++ List.replicate w.val 255#u8 := by
    rw [hb1, resize_grow _ _ _ (by scalar_tac)]
    congr 2; scalar_tac
  have hb1l : b1.length = buf.length + w.val := by
    simp only [alloc.vec.Vec.length, hb1v, List.length_append, List.length_replicate]
  step as ⟨ s, back, hs, hsl, hback ⟩
  step with hwrite s (by scalar_tac) as ⟨ s1, hs1 ⟩
  have hs1l : s1.val.length = w.val := by
    have := slice_len_of_bytes hs1; simpa [hsize] using this
  rw [hback, vec_setSlice_val, hb1v, show (alloc.vec.Vec.len buf).val = buf.val.length by simp,
    setSlice!_append _ _ _ (by simp [hs1l]), hs1l]
  simp [← hs1]

/-! ## `Checkpoint { epoch: u64, root: [u8; 32] }` -/

def cpNames : List String := ["epoch", "root"]
def cpFields : List Desc := [Desc.uint64, .byteVector 32]

def cpToV (c : verif_example.Checkpoint) : Value :=
  .seq [.uint c.epoch.val, .bytes (bytes c.root.val)]

theorem Checkpoint.enc_is_fixed_size :
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.is_fixed_size = ok true := by
  simp [verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.is_fixed_size,
    U64.Insts.LibsszEncodeSszEncode.is_fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size]

theorem Checkpoint.is_fixed_size :
    verif_example.Checkpoint.Insts.LibsszDecodeSszDecode.is_fixed_size = ok true := by
  simp [verif_example.Checkpoint.Insts.LibsszDecodeSszDecode.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.is_fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.is_fixed_size]

@[step]
theorem Checkpoint.fixed_size.spec :
    verif_example.Checkpoint.Insts.LibsszDecodeSszDecode.fixed_size ⦃ n => n.val = 40 ⦄ := by
  simp only [verif_example.Checkpoint.Insts.LibsszDecodeSszDecode.fixed_size, Checkpoint.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size,
    bind_ok, ↓reduceIte]
  step*

theorem Checkpoint.from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    verif_example.Checkpoint.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees cpToV r (deserialize (.container cpNames cpFields) (bytes s.val)) ⦄ := by
  rw [eth_decode_fixed cpNames cpFields [8, 32] rfl _ (by rw [bytes_size]; exact hs)]
  simp only [bytes_size, cuts, cpFields, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  unfold verif_example.Checkpoint.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  simp only [Checkpoint.is_fixed_size, bind_ok, ↓reduceIte]
  step with Checkpoint.fixed_size.spec as ⟨ ex, hex ⟩
  have hl := Slice.len_val s
  by_cases hne : s.length ≠ 40
  · have : (s.len != ex) = true := by simp; scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok, hne, ne_eq, not_false_eq_true, Agrees]
    have := ErrMatch.fixedLength ex s.len
    rw [hex, hl] at this
    exact this
  have hl' : s.val.length = 40 := by simp [Slice.length] at hne; exact hne
  have : ¬ (s.len != ex) = true := by simp; scalar_tac
  simp only [this, Bool.false_eq_true, ↓reduceIte, hl', ne_eq, not_true_eq_false,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size,
    bind_ok]
  rw [deserializeFields, deserializeFields, deserializeFields]
  fixed_field s1 r1 hr1 := s, 8#usize from (List.drop_zero (l := s.val)).symm using U64.dec
  fixed_field s2 r2 hr2 := r1, 32#usize from hr1 using ArrayU8N.from_ssz_bytes.spec 32#usize
  simp only [WP.spec_ok, Except.pure, ex_ok_bind, Agrees]
  rfl

/-- What libssz writes for a `Checkpoint`. -/
def cpEnc (c : verif_example.Checkpoint) : Bytes := uintBytes 8 c.epoch.val ++ bytes c.root.val

theorem cpEnc_size (c : verif_example.Checkpoint) : (cpEnc c).size = 40 := by
  simp [cpEnc, uintBytes_size]

theorem Checkpoint.has_write_fixed :
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed = ok true := by
  simp [verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed,
    U64.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed,
    ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed]

theorem Checkpoint.enc_fixed_size :
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.fixed_size = ok 40#usize := by
  simp only [verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.fixed_size,
    Checkpoint.enc_is_fixed_size, U64.Insts.LibsszEncodeSszEncode.fixed_size,
    ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, bind_ok, ↓reduceIte]
  apply ok_of_spec
  step*

/-- **`ssz_write_fixed` of `Checkpoint`**: overwrites a 40-byte segment with the encoding. -/
theorem Checkpoint.ssz_write_fixed.bytes_spec (c : verif_example.Checkpoint) (out : Slice Std.U8)
    (h : out.length = 40) :
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_write_fixed c out ⦃ out' =>
      bytes out'.val = cpEnc c ⦄ := by
  unfold verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  simp only [Checkpoint.has_write_fixed, U64.Insts.LibsszEncodeSszEncode.fixed_size, bind_ok,
    ↓reduceIte]
  step with core.slice.Slice.split_at_mut.spec as ⟨ hd, rest, back, hl1, hl2, hv1, hv2, hback ⟩
  step with U64.ssz_write_fixed.bytes_spec c.epoch hd hl1 as ⟨ hd1, hhd1 ⟩
  step with ArrayU8N.wr 32#usize (by simp) c.root rest (by rw [hl2, h]; rfl) as ⟨ rest1, hrest1 ⟩
  rw [(hback hd1 rest1 (by rw [slice_len_of_bytes hhd1]; simp [uintBytes_size])
    (by rw [slice_len_of_bytes hrest1, h]; simp)).1, bytes_append, hhd1, hrest1, cpEnc]

theorem Checkpoint.ssz_append.bytes_spec (c : verif_example.Checkpoint) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (cpEnc c).size ≤ Usize.max) :
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_append c buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ cpEnc c ⦄ := by
  rw [cpEnc_size] at h
  unfold verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [Checkpoint.has_write_fixed, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  exact append_via_write_fixed _ c (cpEnc c) 40#usize buf (cpEnc_size c)
    (fun out ho => Checkpoint.ssz_write_fixed.bytes_spec c out ho) h

theorem Checkpoint.ethlib_encode (c : verif_example.Checkpoint) :
    serialize (.container cpNames cpFields) (cpToV c) = .ok (cpEnc c) := by
  rw [cpToV, cpFields, cpEnc, ← concatParts_two]
  apply eth_encode_fixed _ _ _ _ rfl
  · rw [serializeFields_cons, U64.ser, ex_ok_bind, serializeFields_cons,
      ArrayU8N.ser' 32 32#usize rfl (by decide) c.root, ex_ok_bind, serializeFields_nil]
    rfl
  · rw [concatParts_two, ← cpEnc, cpEnc_size]; omega

/-- **Encode of `Checkpoint` ≡ EthLib.** -/
theorem Checkpoint.encode.agrees (c : verif_example.Checkpoint) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 40 ≤ Usize.max) :
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_append c buf ⦃ buf' =>
      ∃ enc, serialize (.container cpNames cpFields) (cpToV c) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  apply WP.spec_mono (Checkpoint.ssz_append.bytes_spec c buf (by rw [cpEnc_size]; exact h))
  intro b' hb'
  exact ⟨_, Checkpoint.ethlib_encode c, hb'⟩

/-! ## `Fork` (16 bytes) -/

def forkNames : List String := ["previous_version", "current_version", "epoch"]
def forkFields : List Desc := [.byteVector 4, .byteVector 4, Desc.uint64]

def forkToV (x : verif_example.Fork) : Value :=
  .seq [.bytes (bytes x.previous_version.val), .bytes (bytes x.current_version.val), .uint x.epoch.val]

/-- What libssz writes for a `Fork`: the fields, one after another. -/
def forkEnc (x : verif_example.Fork) : Bytes :=
  bytes x.previous_version.val ++ bytes x.current_version.val ++ uintBytes 8 x.epoch.val

theorem forkEnc_size (x : verif_example.Fork) : (forkEnc x).size = 16 := by
  simp [forkEnc, uintBytes_size, boolByte, cpEnc_size]

theorem Fork.is_fixed_size :
    verif_example.Fork.Insts.LibsszDecodeSszDecode.is_fixed_size = ok true := by
  simp [verif_example.Fork.Insts.LibsszDecodeSszDecode.is_fixed_size, U64.Insts.LibsszDecodeSszDecode.is_fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.is_fixed_size, Bool.Insts.LibsszDecodeSszDecode.is_fixed_size, Checkpoint.is_fixed_size]

theorem Fork.enc_is_fixed_size :
    verif_example.Fork.Insts.LibsszEncodeSszEncode.is_fixed_size = ok true := by
  simp [verif_example.Fork.Insts.LibsszEncodeSszEncode.is_fixed_size, U64.Insts.LibsszEncodeSszEncode.is_fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size, Bool.Insts.LibsszEncodeSszEncode.is_fixed_size, Checkpoint.enc_is_fixed_size]

@[step]
theorem Fork.fixed_size.spec :
    verif_example.Fork.Insts.LibsszDecodeSszDecode.fixed_size ⦃ n => n.val = 16 ⦄ := by
  simp only [verif_example.Fork.Insts.LibsszDecodeSszDecode.fixed_size, Fork.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok, ↓reduceIte]
  step*

/-- **Decode of `Fork` ≡ EthLib**, with exact errors (`ErrMatch`). -/
theorem Fork.from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    verif_example.Fork.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees forkToV r (deserialize (.container forkNames forkFields) (bytes s.val)) ⦄ := by
  rw [eth_decode_fixed forkNames forkFields [4, 4, 8] rfl _ (by rw [bytes_size]; exact hs)]
  simp only [bytes_size, cuts, forkFields, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  unfold verif_example.Fork.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  simp only [Fork.is_fixed_size, bind_ok, ↓reduceIte]
  step with Fork.fixed_size.spec as ⟨ ex, hex ⟩
  have hl := Slice.len_val s
  by_cases hne : s.length ≠ 16
  · have : (s.len != ex) = true := by simp; scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok, hne, ne_eq, not_false_eq_true, Agrees]
    have := ErrMatch.fixedLength ex s.len
    rw [hex, hl] at this
    exact this
  have hl' : s.val.length = 16 := by simp [Slice.length] at hne; exact hne
  have : ¬ (s.len != ex) = true := by simp; scalar_tac
  simp only [this, Bool.false_eq_true, ↓reduceIte, hl', ne_eq, not_true_eq_false,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok]
  rw [deserializeFields, deserializeFields, deserializeFields, deserializeFields]
  fixed_field s1 r1 hr1 := s, 4#usize from (List.drop_zero (l := s.val)).symm using ArrayU8N.from_ssz_bytes.spec 4#usize
  fixed_field s2 r2 hr2 := r1, 4#usize from hr1 using ArrayU8N.from_ssz_bytes.spec 4#usize
  fixed_field s3 r3 hr3 := r2, 8#usize from hr2 using U64.dec
  simp only [WP.spec_ok, Except.pure, ex_ok_bind, Agrees]
  rfl

theorem Fork.has_write_fixed :
    verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed = ok true := by
  simp [verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, U64.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Bool.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Checkpoint.has_write_fixed]

theorem Fork.enc_fixed_size :
    verif_example.Fork.Insts.LibsszEncodeSszEncode.fixed_size = ok 16#usize := by
  simp only [verif_example.Fork.Insts.LibsszEncodeSszEncode.fixed_size, Fork.enc_is_fixed_size,
    U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  apply ok_of_spec
  step*

/-- **`ssz_write_fixed` of `Fork`**: overwrites a 16-byte segment with the encoding. -/
theorem Fork.ssz_write_fixed.bytes_spec (x : verif_example.Fork) (out : Slice Std.U8)
    (h : out.length = 16) :
    verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      bytes out'.val = forkEnc x ⦄ := by
  unfold verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  simp only [Fork.has_write_fixed, U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a1, r1, back1, hal1, hrl1, hav1, hrv1, hback1 ⟩
  step with ArrayU8N.wr 4#usize (by simp) x.previous_version a1 (by scalar_tac) as ⟨ c1, hc1 ⟩
  have hcl1 : c1.length = 4 := by
    rw [slice_len_of_bytes hc1]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a2, r2, back2, hal2, hrl2, hav2, hrv2, hback2 ⟩
  step with ArrayU8N.wr 4#usize (by simp) x.current_version a2 (by scalar_tac) as ⟨ c2, hc2 ⟩
  have hcl2 : c2.length = 4 := by
    rw [slice_len_of_bytes hc2]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with U64.ssz_write_fixed.bytes_spec x.epoch r2 (by scalar_tac) as ⟨ c3, hc3 ⟩
  have hcl3 : c3.length = 8 := by
    rw [slice_len_of_bytes hc3]; simp [uintBytes_size, boolByte, cpEnc_size]
  have e2 := hback2 c2 (c3) (by scalar_tac) (by scalar_tac)
  have e1 := hback1 c1 (back2 (c2, c3)) (by scalar_tac) (by scalar_tac)
  rw [e1.1, bytes_append, hc1, e2.1, bytes_append, hc2, hc3, forkEnc]
  simp only [Array.append_assoc]

theorem Fork.ssz_append.bytes_spec (x : verif_example.Fork) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (forkEnc x).size ≤ Usize.max) :
    verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ forkEnc x ⦄ := by
  rw [forkEnc_size] at h
  unfold verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [Fork.has_write_fixed, Fork.enc_fixed_size, bind_ok, ↓reduceIte]
  exact append_via_write_fixed _ x (forkEnc x) 16#usize buf (forkEnc_size x)
    (fun out ho => Fork.ssz_write_fixed.bytes_spec x out ho) h

theorem Fork.ethlib_encode (x : verif_example.Fork) :
    serialize (.container forkNames forkFields) (forkToV x) = .ok (forkEnc x) := by
  have hc : forkEnc x = concatParts [bytes x.previous_version.val, bytes x.current_version.val, uintBytes 8 x.epoch.val] := by
    simp [forkEnc, concatParts, Array.append_assoc]
  rw [forkToV, forkFields, hc]
  apply eth_encode_fixed _ _ _ _ rfl
  · rw [serializeFields_cons, ArrayU8N.ser' 4 4#usize rfl (by decide) x.previous_version, ex_ok_bind, serializeFields_cons, ArrayU8N.ser' 4 4#usize rfl (by decide) x.current_version, ex_ok_bind, serializeFields_cons, U64.ser x.epoch, ex_ok_bind, serializeFields_nil]
    rfl
  · rw [← hc, forkEnc_size]; omega

/-- **Encode of `Fork` ≡ EthLib.** -/
theorem Fork.encode.agrees (x : verif_example.Fork) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 16 ≤ Usize.max) :
    verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize (.container forkNames forkFields) (forkToV x) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  apply WP.spec_mono (Fork.ssz_append.bytes_spec x buf (by rw [forkEnc_size]; exact h))
  intro b' hb'
  exact ⟨_, Fork.ethlib_encode x, hb'⟩

/-! ## `BeaconBlockHeader` (112 bytes) -/

def bbhNames : List String := ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
def bbhFields : List Desc := [Desc.uint64, Desc.uint64, .byteVector 32, .byteVector 32, .byteVector 32]

def bbhToV (x : verif_example.BeaconBlockHeader) : Value :=
  .seq [.uint x.slot.val, .uint x.proposer_index.val, .bytes (bytes x.parent_root.val), .bytes (bytes x.state_root.val), .bytes (bytes x.body_root.val)]

/-- What libssz writes for a `BeaconBlockHeader`: the fields, one after another. -/
def bbhEnc (x : verif_example.BeaconBlockHeader) : Bytes :=
  uintBytes 8 x.slot.val ++ uintBytes 8 x.proposer_index.val ++ bytes x.parent_root.val ++ bytes x.state_root.val ++ bytes x.body_root.val

theorem bbhEnc_size (x : verif_example.BeaconBlockHeader) : (bbhEnc x).size = 112 := by
  simp [bbhEnc, uintBytes_size, boolByte, cpEnc_size]

theorem BeaconBlockHeader.is_fixed_size :
    verif_example.BeaconBlockHeader.Insts.LibsszDecodeSszDecode.is_fixed_size = ok true := by
  simp [verif_example.BeaconBlockHeader.Insts.LibsszDecodeSszDecode.is_fixed_size, U64.Insts.LibsszDecodeSszDecode.is_fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.is_fixed_size, Bool.Insts.LibsszDecodeSszDecode.is_fixed_size, Checkpoint.is_fixed_size]

theorem BeaconBlockHeader.enc_is_fixed_size :
    verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.is_fixed_size = ok true := by
  simp [verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.is_fixed_size, U64.Insts.LibsszEncodeSszEncode.is_fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size, Bool.Insts.LibsszEncodeSszEncode.is_fixed_size, Checkpoint.enc_is_fixed_size]

@[step]
theorem BeaconBlockHeader.fixed_size.spec :
    verif_example.BeaconBlockHeader.Insts.LibsszDecodeSszDecode.fixed_size ⦃ n => n.val = 112 ⦄ := by
  simp only [verif_example.BeaconBlockHeader.Insts.LibsszDecodeSszDecode.fixed_size, BeaconBlockHeader.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok, ↓reduceIte]
  step*

/-- **Decode of `BeaconBlockHeader` ≡ EthLib**, with exact errors (`ErrMatch`). -/
theorem BeaconBlockHeader.from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    verif_example.BeaconBlockHeader.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees bbhToV r (deserialize (.container bbhNames bbhFields) (bytes s.val)) ⦄ := by
  rw [eth_decode_fixed bbhNames bbhFields [8, 8, 32, 32, 32] rfl _ (by rw [bytes_size]; exact hs)]
  simp only [bytes_size, cuts, bbhFields, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  unfold verif_example.BeaconBlockHeader.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  simp only [BeaconBlockHeader.is_fixed_size, bind_ok, ↓reduceIte]
  step with BeaconBlockHeader.fixed_size.spec as ⟨ ex, hex ⟩
  have hl := Slice.len_val s
  by_cases hne : s.length ≠ 112
  · have : (s.len != ex) = true := by simp; scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok, hne, ne_eq, not_false_eq_true, Agrees]
    have := ErrMatch.fixedLength ex s.len
    rw [hex, hl] at this
    exact this
  have hl' : s.val.length = 112 := by simp [Slice.length] at hne; exact hne
  have : ¬ (s.len != ex) = true := by simp; scalar_tac
  simp only [this, Bool.false_eq_true, ↓reduceIte, hl', ne_eq, not_true_eq_false,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok]
  rw [deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields]
  fixed_field s1 r1 hr1 := s, 8#usize from (List.drop_zero (l := s.val)).symm using U64.dec
  fixed_field s2 r2 hr2 := r1, 8#usize from hr1 using U64.dec
  fixed_field s3 r3 hr3 := r2, 32#usize from hr2 using ArrayU8N.from_ssz_bytes.spec 32#usize
  fixed_field s4 r4 hr4 := r3, 32#usize from hr3 using ArrayU8N.from_ssz_bytes.spec 32#usize
  fixed_field s5 r5 hr5 := r4, 32#usize from hr4 using ArrayU8N.from_ssz_bytes.spec 32#usize
  simp only [WP.spec_ok, Except.pure, ex_ok_bind, Agrees]
  rfl

theorem BeaconBlockHeader.has_write_fixed :
    verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed = ok true := by
  simp [verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, U64.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Bool.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Checkpoint.has_write_fixed]

theorem BeaconBlockHeader.enc_fixed_size :
    verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.fixed_size = ok 112#usize := by
  simp only [verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.fixed_size, BeaconBlockHeader.enc_is_fixed_size,
    U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  apply ok_of_spec
  step*

/-- **`ssz_write_fixed` of `BeaconBlockHeader`**: overwrites a 112-byte segment with the
encoding. -/
theorem BeaconBlockHeader.ssz_write_fixed.bytes_spec (x : verif_example.BeaconBlockHeader) (out : Slice Std.U8)
    (h : out.length = 112) :
    verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      bytes out'.val = bbhEnc x ⦄ := by
  unfold verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  simp only [BeaconBlockHeader.has_write_fixed, U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a1, r1, back1, hal1, hrl1, hav1, hrv1, hback1 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.slot a1 (by scalar_tac) as ⟨ c1, hc1 ⟩
  have hcl1 : c1.length = 8 := by
    rw [slice_len_of_bytes hc1]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a2, r2, back2, hal2, hrl2, hav2, hrv2, hback2 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.proposer_index a2 (by scalar_tac) as ⟨ c2, hc2 ⟩
  have hcl2 : c2.length = 8 := by
    rw [slice_len_of_bytes hc2]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a3, r3, back3, hal3, hrl3, hav3, hrv3, hback3 ⟩
  step with ArrayU8N.wr 32#usize (by simp) x.parent_root a3 (by scalar_tac) as ⟨ c3, hc3 ⟩
  have hcl3 : c3.length = 32 := by
    rw [slice_len_of_bytes hc3]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a4, r4, back4, hal4, hrl4, hav4, hrv4, hback4 ⟩
  step with ArrayU8N.wr 32#usize (by simp) x.state_root a4 (by scalar_tac) as ⟨ c4, hc4 ⟩
  have hcl4 : c4.length = 32 := by
    rw [slice_len_of_bytes hc4]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with ArrayU8N.wr 32#usize (by simp) x.body_root r4 (by scalar_tac) as ⟨ c5, hc5 ⟩
  have hcl5 : c5.length = 32 := by
    rw [slice_len_of_bytes hc5]; simp [uintBytes_size, boolByte, cpEnc_size]
  have e4 := hback4 c4 (c5) (by scalar_tac) (by scalar_tac)
  have e3 := hback3 c3 (back4 (c4, c5)) (by scalar_tac) (by scalar_tac)
  have e2 := hback2 c2 (back3 (c3, back4 (c4, c5))) (by scalar_tac) (by scalar_tac)
  have e1 := hback1 c1 (back2 (c2, back3 (c3, back4 (c4, c5)))) (by scalar_tac) (by scalar_tac)
  rw [e1.1, bytes_append, hc1, e2.1, bytes_append, hc2, e3.1, bytes_append, hc3, e4.1, bytes_append, hc4, hc5, bbhEnc]
  simp only [Array.append_assoc]

theorem BeaconBlockHeader.ssz_append.bytes_spec (x : verif_example.BeaconBlockHeader) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (bbhEnc x).size ≤ Usize.max) :
    verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ bbhEnc x ⦄ := by
  rw [bbhEnc_size] at h
  unfold verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [BeaconBlockHeader.has_write_fixed, BeaconBlockHeader.enc_fixed_size, bind_ok, ↓reduceIte]
  exact append_via_write_fixed _ x (bbhEnc x) 112#usize buf (bbhEnc_size x)
    (fun out ho => BeaconBlockHeader.ssz_write_fixed.bytes_spec x out ho) h

theorem BeaconBlockHeader.ethlib_encode (x : verif_example.BeaconBlockHeader) :
    serialize (.container bbhNames bbhFields) (bbhToV x) = .ok (bbhEnc x) := by
  have hc : bbhEnc x = concatParts [uintBytes 8 x.slot.val, uintBytes 8 x.proposer_index.val, bytes x.parent_root.val, bytes x.state_root.val, bytes x.body_root.val] := by
    simp [bbhEnc, concatParts, Array.append_assoc]
  rw [bbhToV, bbhFields, hc]
  apply eth_encode_fixed _ _ _ _ rfl
  · rw [serializeFields_cons, U64.ser x.slot, ex_ok_bind, serializeFields_cons, U64.ser x.proposer_index, ex_ok_bind, serializeFields_cons, ArrayU8N.ser' 32 32#usize rfl (by decide) x.parent_root, ex_ok_bind, serializeFields_cons, ArrayU8N.ser' 32 32#usize rfl (by decide) x.state_root, ex_ok_bind, serializeFields_cons, ArrayU8N.ser' 32 32#usize rfl (by decide) x.body_root, ex_ok_bind, serializeFields_nil]
    rfl
  · rw [← hc, bbhEnc_size]; omega

/-- **Encode of `BeaconBlockHeader` ≡ EthLib.** -/
theorem BeaconBlockHeader.encode.agrees (x : verif_example.BeaconBlockHeader) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 112 ≤ Usize.max) :
    verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize (.container bbhNames bbhFields) (bbhToV x) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  apply WP.spec_mono (BeaconBlockHeader.ssz_append.bytes_spec x buf (by rw [bbhEnc_size]; exact h))
  intro b' hb'
  exact ⟨_, BeaconBlockHeader.ethlib_encode x, hb'⟩

/-! ## `Validator` (121 bytes) -/

def valNames : List String := ["pubkey", "withdrawal_credentials", "effective_balance", "slashed", "activation_eligibility_epoch", "activation_epoch", "exit_epoch", "withdrawable_epoch"]
def valFields : List Desc := [.byteVector 48, .byteVector 32, Desc.uint64, .bool, Desc.uint64, Desc.uint64, Desc.uint64, Desc.uint64]

def valToV (x : verif_example.Validator) : Value :=
  .seq [.bytes (bytes x.pubkey.val), .bytes (bytes x.withdrawal_credentials.val), .uint x.effective_balance.val, .bool x.slashed, .uint x.activation_eligibility_epoch.val, .uint x.activation_epoch.val, .uint x.exit_epoch.val, .uint x.withdrawable_epoch.val]

/-- What libssz writes for a `Validator`: the fields, one after another. -/
def valEnc (x : verif_example.Validator) : Bytes :=
  bytes x.pubkey.val ++ bytes x.withdrawal_credentials.val ++ uintBytes 8 x.effective_balance.val ++ boolByte x.slashed ++ uintBytes 8 x.activation_eligibility_epoch.val ++ uintBytes 8 x.activation_epoch.val ++ uintBytes 8 x.exit_epoch.val ++ uintBytes 8 x.withdrawable_epoch.val

theorem valEnc_size (x : verif_example.Validator) : (valEnc x).size = 121 := by
  simp [valEnc, uintBytes_size, boolByte, cpEnc_size]

theorem Validator.is_fixed_size :
    verif_example.Validator.Insts.LibsszDecodeSszDecode.is_fixed_size = ok true := by
  simp [verif_example.Validator.Insts.LibsszDecodeSszDecode.is_fixed_size, U64.Insts.LibsszDecodeSszDecode.is_fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.is_fixed_size, Bool.Insts.LibsszDecodeSszDecode.is_fixed_size, Checkpoint.is_fixed_size]

theorem Validator.enc_is_fixed_size :
    verif_example.Validator.Insts.LibsszEncodeSszEncode.is_fixed_size = ok true := by
  simp [verif_example.Validator.Insts.LibsszEncodeSszEncode.is_fixed_size, U64.Insts.LibsszEncodeSszEncode.is_fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size, Bool.Insts.LibsszEncodeSszEncode.is_fixed_size, Checkpoint.enc_is_fixed_size]

@[step]
theorem Validator.fixed_size.spec :
    verif_example.Validator.Insts.LibsszDecodeSszDecode.fixed_size ⦃ n => n.val = 121 ⦄ := by
  simp only [verif_example.Validator.Insts.LibsszDecodeSszDecode.fixed_size, Validator.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok, ↓reduceIte]
  step*

/-- **Decode of `Validator` ≡ EthLib**, with exact errors (`ErrMatch`). -/
theorem Validator.from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    verif_example.Validator.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees valToV r (deserialize (.container valNames valFields) (bytes s.val)) ⦄ := by
  rw [eth_decode_fixed valNames valFields [48, 32, 8, 1, 8, 8, 8, 8] rfl _ (by rw [bytes_size]; exact hs)]
  simp only [bytes_size, cuts, valFields, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  unfold verif_example.Validator.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  simp only [Validator.is_fixed_size, bind_ok, ↓reduceIte]
  step with Validator.fixed_size.spec as ⟨ ex, hex ⟩
  have hl := Slice.len_val s
  by_cases hne : s.length ≠ 121
  · have : (s.len != ex) = true := by simp; scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok, hne, ne_eq, not_false_eq_true, Agrees]
    have := ErrMatch.fixedLength ex s.len
    rw [hex, hl] at this
    exact this
  have hl' : s.val.length = 121 := by simp [Slice.length] at hne; exact hne
  have : ¬ (s.len != ex) = true := by simp; scalar_tac
  simp only [this, Bool.false_eq_true, ↓reduceIte, hl', ne_eq, not_true_eq_false,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok]
  rw [deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields]
  fixed_field s1 r1 hr1 := s, 48#usize from (List.drop_zero (l := s.val)).symm using ArrayU8N.from_ssz_bytes.spec 48#usize
  fixed_field s2 r2 hr2 := r1, 32#usize from hr1 using ArrayU8N.from_ssz_bytes.spec 32#usize
  fixed_field s3 r3 hr3 := r2, 8#usize from hr2 using U64.dec
  fixed_field s4 r4 hr4 := r3, 1#usize from hr3 using Bool.dec
  fixed_field s5 r5 hr5 := r4, 8#usize from hr4 using U64.dec
  fixed_field s6 r6 hr6 := r5, 8#usize from hr5 using U64.dec
  fixed_field s7 r7 hr7 := r6, 8#usize from hr6 using U64.dec
  fixed_field s8 r8 hr8 := r7, 8#usize from hr7 using U64.dec
  simp only [WP.spec_ok, Except.pure, ex_ok_bind, Agrees]
  rfl

theorem Validator.has_write_fixed :
    verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed = ok true := by
  simp [verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, U64.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Bool.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Checkpoint.has_write_fixed]

theorem Validator.enc_fixed_size :
    verif_example.Validator.Insts.LibsszEncodeSszEncode.fixed_size = ok 121#usize := by
  simp only [verif_example.Validator.Insts.LibsszEncodeSszEncode.fixed_size, Validator.enc_is_fixed_size,
    U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  apply ok_of_spec
  step*

/-- **`ssz_write_fixed` of `Validator`**: overwrites a 121-byte segment with the encoding. -/
theorem Validator.ssz_write_fixed.bytes_spec (x : verif_example.Validator) (out : Slice Std.U8)
    (h : out.length = 121) :
    verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      bytes out'.val = valEnc x ⦄ := by
  unfold verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  simp only [Validator.has_write_fixed, U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a1, r1, back1, hal1, hrl1, hav1, hrv1, hback1 ⟩
  step with ArrayU8N.wr 48#usize (by simp) x.pubkey a1 (by scalar_tac) as ⟨ c1, hc1 ⟩
  have hcl1 : c1.length = 48 := by
    rw [slice_len_of_bytes hc1]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a2, r2, back2, hal2, hrl2, hav2, hrv2, hback2 ⟩
  step with ArrayU8N.wr 32#usize (by simp) x.withdrawal_credentials a2 (by scalar_tac) as ⟨ c2, hc2 ⟩
  have hcl2 : c2.length = 32 := by
    rw [slice_len_of_bytes hc2]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a3, r3, back3, hal3, hrl3, hav3, hrv3, hback3 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.effective_balance a3 (by scalar_tac) as ⟨ c3, hc3 ⟩
  have hcl3 : c3.length = 8 := by
    rw [slice_len_of_bytes hc3]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a4, r4, back4, hal4, hrl4, hav4, hrv4, hback4 ⟩
  step with Bool.ssz_write_fixed.bytes_spec x.slashed a4 (by scalar_tac) as ⟨ c4, hc4 ⟩
  have hcl4 : c4.length = 1 := by
    rw [slice_len_of_bytes hc4]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a5, r5, back5, hal5, hrl5, hav5, hrv5, hback5 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.activation_eligibility_epoch a5 (by scalar_tac) as ⟨ c5, hc5 ⟩
  have hcl5 : c5.length = 8 := by
    rw [slice_len_of_bytes hc5]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a6, r6, back6, hal6, hrl6, hav6, hrv6, hback6 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.activation_epoch a6 (by scalar_tac) as ⟨ c6, hc6 ⟩
  have hcl6 : c6.length = 8 := by
    rw [slice_len_of_bytes hc6]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a7, r7, back7, hal7, hrl7, hav7, hrv7, hback7 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.exit_epoch a7 (by scalar_tac) as ⟨ c7, hc7 ⟩
  have hcl7 : c7.length = 8 := by
    rw [slice_len_of_bytes hc7]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with U64.ssz_write_fixed.bytes_spec x.withdrawable_epoch r7 (by scalar_tac) as ⟨ c8, hc8 ⟩
  have hcl8 : c8.length = 8 := by
    rw [slice_len_of_bytes hc8]; simp [uintBytes_size, boolByte, cpEnc_size]
  have e7 := hback7 c7 (c8) (by scalar_tac) (by scalar_tac)
  have e6 := hback6 c6 (back7 (c7, c8)) (by scalar_tac) (by scalar_tac)
  have e5 := hback5 c5 (back6 (c6, back7 (c7, c8))) (by scalar_tac) (by scalar_tac)
  have e4 := hback4 c4 (back5 (c5, back6 (c6, back7 (c7, c8)))) (by scalar_tac) (by scalar_tac)
  have e3 := hback3 c3 (back4 (c4, back5 (c5, back6 (c6, back7 (c7, c8))))) (by scalar_tac) (by scalar_tac)
  have e2 := hback2 c2 (back3 (c3, back4 (c4, back5 (c5, back6 (c6, back7 (c7, c8)))))) (by scalar_tac) (by scalar_tac)
  have e1 := hback1 c1 (back2 (c2, back3 (c3, back4 (c4, back5 (c5, back6 (c6, back7 (c7, c8))))))) (by scalar_tac) (by scalar_tac)
  rw [e1.1, bytes_append, hc1, e2.1, bytes_append, hc2, e3.1, bytes_append, hc3, e4.1, bytes_append, hc4, e5.1, bytes_append, hc5, e6.1, bytes_append, hc6, e7.1, bytes_append, hc7, hc8, valEnc]
  simp only [Array.append_assoc]

theorem Validator.ssz_append.bytes_spec (x : verif_example.Validator) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (valEnc x).size ≤ Usize.max) :
    verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ valEnc x ⦄ := by
  rw [valEnc_size] at h
  unfold verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [Validator.has_write_fixed, Validator.enc_fixed_size, bind_ok, ↓reduceIte]
  exact append_via_write_fixed _ x (valEnc x) 121#usize buf (valEnc_size x)
    (fun out ho => Validator.ssz_write_fixed.bytes_spec x out ho) h

theorem Validator.ethlib_encode (x : verif_example.Validator) :
    serialize (.container valNames valFields) (valToV x) = .ok (valEnc x) := by
  have hc : valEnc x = concatParts [bytes x.pubkey.val, bytes x.withdrawal_credentials.val, uintBytes 8 x.effective_balance.val, boolByte x.slashed, uintBytes 8 x.activation_eligibility_epoch.val, uintBytes 8 x.activation_epoch.val, uintBytes 8 x.exit_epoch.val, uintBytes 8 x.withdrawable_epoch.val] := by
    simp [valEnc, concatParts, Array.append_assoc]
  rw [valToV, valFields, hc]
  apply eth_encode_fixed _ _ _ _ rfl
  · rw [serializeFields_cons, ArrayU8N.ser' 48 48#usize rfl (by decide) x.pubkey, ex_ok_bind, serializeFields_cons, ArrayU8N.ser' 32 32#usize rfl (by decide) x.withdrawal_credentials, ex_ok_bind, serializeFields_cons, U64.ser x.effective_balance, ex_ok_bind, serializeFields_cons, Bool.ser x.slashed, ex_ok_bind, serializeFields_cons, U64.ser x.activation_eligibility_epoch, ex_ok_bind, serializeFields_cons, U64.ser x.activation_epoch, ex_ok_bind, serializeFields_cons, U64.ser x.exit_epoch, ex_ok_bind, serializeFields_cons, U64.ser x.withdrawable_epoch, ex_ok_bind, serializeFields_nil]
    rfl
  · rw [← hc, valEnc_size]; omega

/-- **Encode of `Validator` ≡ EthLib.** -/
theorem Validator.encode.agrees (x : verif_example.Validator) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 121 ≤ Usize.max) :
    verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize (.container valNames valFields) (valToV x) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  apply WP.spec_mono (Validator.ssz_append.bytes_spec x buf (by rw [valEnc_size]; exact h))
  intro b' hb'
  exact ⟨_, Validator.ethlib_encode x, hb'⟩

/-! ## `AttestationData` (128 bytes) -/

def adNames : List String := ["slot", "index", "beacon_block_root", "source", "target"]
def adFields : List Desc := [Desc.uint64, Desc.uint64, .byteVector 32, .container cpNames cpFields, .container cpNames cpFields]

def adToV (x : verif_example.AttestationData) : Value :=
  .seq [.uint x.slot.val, .uint x.index.val, .bytes (bytes x.beacon_block_root.val), cpToV x.source, cpToV x.target]

/-- What libssz writes for an `AttestationData`: the fields, one after another. -/
def adEnc (x : verif_example.AttestationData) : Bytes :=
  uintBytes 8 x.slot.val ++ uintBytes 8 x.index.val ++ bytes x.beacon_block_root.val ++ cpEnc x.source ++ cpEnc x.target

theorem adEnc_size (x : verif_example.AttestationData) : (adEnc x).size = 128 := by
  simp [adEnc, uintBytes_size, boolByte, cpEnc_size]

theorem AttestationData.is_fixed_size :
    verif_example.AttestationData.Insts.LibsszDecodeSszDecode.is_fixed_size = ok true := by
  simp [verif_example.AttestationData.Insts.LibsszDecodeSszDecode.is_fixed_size, U64.Insts.LibsszDecodeSszDecode.is_fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.is_fixed_size, Bool.Insts.LibsszDecodeSszDecode.is_fixed_size, Checkpoint.is_fixed_size]

theorem AttestationData.enc_is_fixed_size :
    verif_example.AttestationData.Insts.LibsszEncodeSszEncode.is_fixed_size = ok true := by
  simp [verif_example.AttestationData.Insts.LibsszEncodeSszEncode.is_fixed_size, U64.Insts.LibsszEncodeSszEncode.is_fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size, Bool.Insts.LibsszEncodeSszEncode.is_fixed_size, Checkpoint.enc_is_fixed_size]

@[step]
theorem AttestationData.fixed_size.spec :
    verif_example.AttestationData.Insts.LibsszDecodeSszDecode.fixed_size ⦃ n => n.val = 128 ⦄ := by
  simp only [verif_example.AttestationData.Insts.LibsszDecodeSszDecode.fixed_size, AttestationData.is_fixed_size,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok, ↓reduceIte]
  step*

/-- **Decode of `AttestationData` ≡ EthLib**, with exact errors (`ErrMatch`). -/
theorem AttestationData.from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :
    verif_example.AttestationData.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>
      Agrees adToV r (deserialize (.container adNames adFields) (bytes s.val)) ⦄ := by
  rw [eth_decode_fixed adNames adFields [8, 8, 32, 40, 40] rfl _ (by rw [bytes_size]; exact hs)]
  simp only [bytes_size, cuts, adFields, List.sum_cons, List.sum_nil, Nat.reduceAdd]
  unfold verif_example.AttestationData.Insts.LibsszDecodeSszDecode.from_ssz_bytes
  simp only [AttestationData.is_fixed_size, bind_ok, ↓reduceIte]
  step with AttestationData.fixed_size.spec as ⟨ ex, hex ⟩
  have hl := Slice.len_val s
  by_cases hne : s.length ≠ 128
  · have : (s.len != ex) = true := by simp; scalar_tac
    simp only [this, ↓reduceIte, WP.spec_ok, hne, ne_eq, not_false_eq_true, Agrees]
    have := ErrMatch.fixedLength ex s.len
    rw [hex, hl] at this
    exact this
  have hl' : s.val.length = 128 := by simp [Slice.length] at hne; exact hne
  have : ¬ (s.len != ex) = true := by simp; scalar_tac
  simp only [this, Bool.false_eq_true, ↓reduceIte, hl', ne_eq, not_true_eq_false,
    U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, Bool.Insts.LibsszDecodeSszDecode.fixed_size, bind_ok]
  rw [deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields, deserializeFields]
  fixed_field s1 r1 hr1 := s, 8#usize from (List.drop_zero (l := s.val)).symm using U64.dec
  fixed_field s2 r2 hr2 := r1, 8#usize from hr1 using U64.dec
  fixed_field s3 r3 hr3 := r2, 32#usize from hr2 using ArrayU8N.from_ssz_bytes.spec 32#usize
  step with Checkpoint.fixed_size.spec as ⟨ wcp, hwcp ⟩
  fixed_field s4 r4 hr4 := r3, wcp from hr3 using Checkpoint.from_ssz_bytes.spec with hwcp
  fixed_field s5 r5 hr5 := r4, wcp from hr4 using Checkpoint.from_ssz_bytes.spec with hwcp
  simp only [WP.spec_ok, Except.pure, ex_ok_bind, Agrees]
  rfl

theorem AttestationData.has_write_fixed :
    verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed = ok true := by
  simp [verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, U64.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Bool.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Checkpoint.has_write_fixed]

theorem AttestationData.enc_fixed_size :
    verif_example.AttestationData.Insts.LibsszEncodeSszEncode.fixed_size = ok 128#usize := by
  simp only [verif_example.AttestationData.Insts.LibsszEncodeSszEncode.fixed_size, AttestationData.enc_is_fixed_size,
    U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  apply ok_of_spec
  step*

/-- **`ssz_write_fixed` of `AttestationData`**: overwrites a 128-byte segment with the
encoding. -/
theorem AttestationData.ssz_write_fixed.bytes_spec (x : verif_example.AttestationData) (out : Slice Std.U8)
    (h : out.length = 128) :
    verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_write_fixed x out ⦃ out' =>
      bytes out'.val = adEnc x ⦄ := by
  unfold verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_write_fixed
  simp only [AttestationData.has_write_fixed, U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size, bind_ok, ↓reduceIte]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a1, r1, back1, hal1, hrl1, hav1, hrv1, hback1 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.slot a1 (by scalar_tac) as ⟨ c1, hc1 ⟩
  have hcl1 : c1.length = 8 := by
    rw [slice_len_of_bytes hc1]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a2, r2, back2, hal2, hrl2, hav2, hrv2, hback2 ⟩
  step with U64.ssz_write_fixed.bytes_spec x.index a2 (by scalar_tac) as ⟨ c2, hc2 ⟩
  have hcl2 : c2.length = 8 := by
    rw [slice_len_of_bytes hc2]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a3, r3, back3, hal3, hrl3, hav3, hrv3, hback3 ⟩
  step with ArrayU8N.wr 32#usize (by simp) x.beacon_block_root a3 (by scalar_tac) as ⟨ c3, hc3 ⟩
  have hcl3 : c3.length = 32 := by
    rw [slice_len_of_bytes hc3]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with core.slice.Slice.split_at_mut.spec as ⟨ a4, r4, back4, hal4, hrl4, hav4, hrv4, hback4 ⟩
  step with Checkpoint.ssz_write_fixed.bytes_spec x.source a4 (by scalar_tac) as ⟨ c4, hc4 ⟩
  have hcl4 : c4.length = 40 := by
    rw [slice_len_of_bytes hc4]; simp [uintBytes_size, boolByte, cpEnc_size]
  step with Checkpoint.ssz_write_fixed.bytes_spec x.target r4 (by scalar_tac) as ⟨ c5, hc5 ⟩
  have hcl5 : c5.length = 40 := by
    rw [slice_len_of_bytes hc5]; simp [uintBytes_size, boolByte, cpEnc_size]
  have e4 := hback4 c4 (c5) (by scalar_tac) (by scalar_tac)
  have e3 := hback3 c3 (back4 (c4, c5)) (by scalar_tac) (by scalar_tac)
  have e2 := hback2 c2 (back3 (c3, back4 (c4, c5))) (by scalar_tac) (by scalar_tac)
  have e1 := hback1 c1 (back2 (c2, back3 (c3, back4 (c4, c5)))) (by scalar_tac) (by scalar_tac)
  rw [e1.1, bytes_append, hc1, e2.1, bytes_append, hc2, e3.1, bytes_append, hc3, e4.1, bytes_append, hc4, hc5, adEnc]
  simp only [Array.append_assoc]

theorem AttestationData.ssz_append.bytes_spec (x : verif_example.AttestationData) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (adEnc x).size ≤ Usize.max) :
    verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ adEnc x ⦄ := by
  rw [adEnc_size] at h
  unfold verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [AttestationData.has_write_fixed, AttestationData.enc_fixed_size, bind_ok, ↓reduceIte]
  exact append_via_write_fixed _ x (adEnc x) 128#usize buf (adEnc_size x)
    (fun out ho => AttestationData.ssz_write_fixed.bytes_spec x out ho) h

theorem AttestationData.ethlib_encode (x : verif_example.AttestationData) :
    serialize (.container adNames adFields) (adToV x) = .ok (adEnc x) := by
  have hc : adEnc x = concatParts [uintBytes 8 x.slot.val, uintBytes 8 x.index.val, bytes x.beacon_block_root.val, cpEnc x.source, cpEnc x.target] := by
    simp [adEnc, concatParts, Array.append_assoc]
  rw [adToV, adFields, hc]
  apply eth_encode_fixed _ _ _ _ rfl
  · rw [serializeFields_cons, U64.ser x.slot, ex_ok_bind, serializeFields_cons, U64.ser x.index, ex_ok_bind, serializeFields_cons, ArrayU8N.ser' 32 32#usize rfl (by decide) x.beacon_block_root, ex_ok_bind, serializeFields_cons, Checkpoint.ethlib_encode x.source, ex_ok_bind, serializeFields_cons, Checkpoint.ethlib_encode x.target, ex_ok_bind, serializeFields_nil]
    rfl
  · rw [← hc, adEnc_size]; omega

/-- **Encode of `AttestationData` ≡ EthLib.** -/
theorem AttestationData.encode.agrees (x : verif_example.AttestationData) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + 128 ≤ Usize.max) :
    verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      ∃ enc, serialize (.container adNames adFields) (adToV x) = .ok enc ∧
        bytes buf'.val = bytes buf.val ++ enc ⦄ := by
  apply WP.spec_mono (AttestationData.ssz_append.bytes_spec x buf (by rw [adEnc_size]; exact h))
  intro b' hb'
  exact ⟨_, AttestationData.ethlib_encode x, hb'⟩

end Libssz.Proofs
