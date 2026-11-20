module
public import Libssz.Proofs.Container
public import EthLib.Serialization.Proofs.Ssz.Codec.Loops
@[expose] public section

/-!
# Fixed-size consensus-layer containers, libssz ≡ EthLib

For a struct whose fields are all fixed-size, `ssz-derive` uses neither `ContainerEncoder` nor
`ContainerDecoder`. The decode checks that the length is the sum of the widths and cuts each
field with `split_at`; the encode appends the fields one after another.

* On the EthLib side, `eth_decode_fixed` and `eth_encode_fixed` hold for any list of fixed
  fields: the exact length (`scope`), and then `deserializeFields` on the chunks (`cuts`), or
  the concatenation of the encodings.
* On the Rust side, the `fixed_field` tactic walks one field of the `split_at` chain.
* `Checkpoint` is written by hand. `Fork`, `BeaconBlockHeader`, `Validator` and
  `AttestationData` come from `scripts/gen_fixed.py`, from the list of fields.
  `AttestationData` uses the `Checkpoint` theorem for its two `Checkpoint` fields.

The decodes are exact (`Agrees` with `ErrMatch`), for every input shorter than 2³² bytes.
-/

open Aeneas Aeneas.Std Result
open EthLib.Serialization.Ssz
open libssz
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

theorem Checkpoint.ssz_append.bytes_spec (c : verif_example.Checkpoint) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (cpEnc c).size ≤ Usize.max) :
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_append c buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ cpEnc c ⦄ := by
  rw [cpEnc_size] at h
  unfold verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.ssz_append
    verif_example.Checkpoint.Insts.LibsszEncodeSszEncode.is_fixed_size
  simp only [U64.Insts.LibsszEncodeSszEncode.is_fixed_size,
    ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size, bind_ok, ↓reduceIte]
  step with U64.ssz_append.bytes_spec c.epoch buf
    (by simp [uintBytes_size, alloc.vec.Vec.length] at h ⊢; omega) as ⟨ b1, hb1 ⟩
  have hb1l : b1.length = buf.length + 8 := by
    have := congrArg Array.size hb1; simp [bytes, uintBytes_size] at this; simpa using this
  apply WP.spec_mono (ArrayU8N.enc 32#usize (by simp) c.root b1
    (by simp [alloc.vec.Vec.length] at hb1l h ⊢; omega))
  intro b' hb'
  rw [hb', hb1, cpEnc, Array.append_assoc]

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

theorem Fork.ssz_append.bytes_spec (x : verif_example.Fork) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (forkEnc x).size ≤ Usize.max) :
    verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ forkEnc x ⦄ := by
  rw [forkEnc_size] at h
  unfold verif_example.Fork.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [Fork.enc_is_fixed_size, bind_ok, ↓reduceIte]
  step with ArrayU8N.enc 4#usize (by simp) x.previous_version buf
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b1, hb1 ⟩
  have hl1 := bytes_len hb1
  step with ArrayU8N.enc 4#usize (by simp) x.current_version b1
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b2, hb2 ⟩
  have hl2 := bytes_len hb2
  apply WP.spec_mono (U64.ssz_append.bytes_spec x.epoch b2
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega))
  intro b' hb'
  rw [hb', hb2, hb1, forkEnc]
  simp only [Array.append_assoc]

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

theorem BeaconBlockHeader.ssz_append.bytes_spec (x : verif_example.BeaconBlockHeader) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (bbhEnc x).size ≤ Usize.max) :
    verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ bbhEnc x ⦄ := by
  rw [bbhEnc_size] at h
  unfold verif_example.BeaconBlockHeader.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [BeaconBlockHeader.enc_is_fixed_size, bind_ok, ↓reduceIte]
  step with U64.ssz_append.bytes_spec x.slot buf
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b1, hb1 ⟩
  have hl1 := bytes_len hb1
  step with U64.ssz_append.bytes_spec x.proposer_index b1
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b2, hb2 ⟩
  have hl2 := bytes_len hb2
  step with ArrayU8N.enc 32#usize (by simp) x.parent_root b2
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b3, hb3 ⟩
  have hl3 := bytes_len hb3
  step with ArrayU8N.enc 32#usize (by simp) x.state_root b3
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b4, hb4 ⟩
  have hl4 := bytes_len hb4
  apply WP.spec_mono (ArrayU8N.enc 32#usize (by simp) x.body_root b4
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega))
  intro b' hb'
  rw [hb', hb4, hb3, hb2, hb1, bbhEnc]
  simp only [Array.append_assoc]

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

theorem Validator.ssz_append.bytes_spec (x : verif_example.Validator) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (valEnc x).size ≤ Usize.max) :
    verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ valEnc x ⦄ := by
  rw [valEnc_size] at h
  unfold verif_example.Validator.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [Validator.enc_is_fixed_size, bind_ok, ↓reduceIte]
  step with ArrayU8N.enc 48#usize (by simp) x.pubkey buf
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b1, hb1 ⟩
  have hl1 := bytes_len hb1
  step with ArrayU8N.enc 32#usize (by simp) x.withdrawal_credentials b1
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b2, hb2 ⟩
  have hl2 := bytes_len hb2
  step with U64.ssz_append.bytes_spec x.effective_balance b2
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b3, hb3 ⟩
  have hl3 := bytes_len hb3
  step with Bool.enc x.slashed b3
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b4, hb4 ⟩
  have hl4 := bytes_len hb4
  step with U64.ssz_append.bytes_spec x.activation_eligibility_epoch b4
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b5, hb5 ⟩
  have hl5 := bytes_len hb5
  step with U64.ssz_append.bytes_spec x.activation_epoch b5
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b6, hb6 ⟩
  have hl6 := bytes_len hb6
  step with U64.ssz_append.bytes_spec x.exit_epoch b6
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b7, hb7 ⟩
  have hl7 := bytes_len hb7
  apply WP.spec_mono (U64.ssz_append.bytes_spec x.withdrawable_epoch b7
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega))
  intro b' hb'
  rw [hb', hb7, hb6, hb5, hb4, hb3, hb2, hb1, valEnc]
  simp only [Array.append_assoc]

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

theorem AttestationData.ssz_append.bytes_spec (x : verif_example.AttestationData) (buf : alloc.vec.Vec Std.U8)
    (h : buf.length + (adEnc x).size ≤ Usize.max) :
    verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>
      bytes buf'.val = bytes buf.val ++ adEnc x ⦄ := by
  rw [adEnc_size] at h
  unfold verif_example.AttestationData.Insts.LibsszEncodeSszEncode.ssz_append
  simp only [AttestationData.enc_is_fixed_size, bind_ok, ↓reduceIte]
  step with U64.ssz_append.bytes_spec x.slot buf
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b1, hb1 ⟩
  have hl1 := bytes_len hb1
  step with U64.ssz_append.bytes_spec x.index b1
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b2, hb2 ⟩
  have hl2 := bytes_len hb2
  step with ArrayU8N.enc 32#usize (by simp) x.beacon_block_root b2
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b3, hb3 ⟩
  have hl3 := bytes_len hb3
  step with Checkpoint.ssz_append.bytes_spec x.source b3
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega) as ⟨ b4, hb4 ⟩
  have hl4 := bytes_len hb4
  apply WP.spec_mono (Checkpoint.ssz_append.bytes_spec x.target b4
    (by simp [uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length] at *; omega))
  intro b' hb'
  rw [hb', hb4, hb3, hb2, hb1, adEnc]
  simp only [Array.append_assoc]

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
