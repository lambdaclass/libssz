#!/usr/bin/env python3
"""Generates the Lean proofs of the fixed-size containers from a table.

Usage: python3 scripts/gen_fixed.py lean/Libssz/Proofs/FixedContainers.lean
(inserts before the file's `end <namespace>`, replacing what was generated before).

In libssz the derived `ssz_append` grows the buffer once and writes each field into its own
span (`ssz_write_fixed`, with `split_at_mut`). The script also keeps a legacy mode, chosen when
the file's namespace is not `Libssz.Proofs` (`LibsszVerif.Proofs`), for a derived
`ssz_append` that appends the fields one after another. Decode and the EthLib side are the
same in both modes.
"""
import sys

# (struct, prefix, [(field, kind)]) ; kind: 'u64' | 'bool' | 'cp' | ('arr', N)
STRUCTS = [
    ("Fork", "fork", [("previous_version", ("arr", 4)), ("current_version", ("arr", 4)),
                      ("epoch", "u64")]),
    ("BeaconBlockHeader", "bbh", [("slot", "u64"), ("proposer_index", "u64"),
                                  ("parent_root", ("arr", 32)), ("state_root", ("arr", 32)),
                                  ("body_root", ("arr", 32))]),
    ("Validator", "val", [("pubkey", ("arr", 48)), ("withdrawal_credentials", ("arr", 32)),
                          ("effective_balance", "u64"), ("slashed", "bool"),
                          ("activation_eligibility_epoch", "u64"), ("activation_epoch", "u64"),
                          ("exit_epoch", "u64"), ("withdrawable_epoch", "u64")]),
    ("AttestationData", "ad", [("slot", "u64"), ("index", "u64"),
                               ("beacon_block_root", ("arr", 32)), ("source", "cp"),
                               ("target", "cp")]),
]


def width(k):
    return {"u64": 8, "bool": 1, "cp": 40}[k] if isinstance(k, str) else k[1]


def desc(k):
    if isinstance(k, tuple):
        return f".byteVector {k[1]}"
    return {"u64": "Desc.uint64", "bool": ".bool", "cp": ".container cpNames cpFields"}[k]


def tov(k, e):
    if isinstance(k, tuple):
        return f".bytes (bytes {e}.val)"
    return {"u64": f".uint {e}.val", "bool": f".bool {e}", "cp": f"cpToV {e}"}[k]


def encb(k, e):
    if isinstance(k, tuple):
        return f"bytes {e}.val"
    return {"u64": f"uintBytes 8 {e}.val", "bool": f"boolByte {e}", "cp": f"cpEnc {e}"}[k]


def ser(k, e):
    if isinstance(k, tuple):
        return f"ArrayU8N.ser' {k[1]} {k[1]}#usize rfl (by decide) {e}"
    return {"u64": f"U64.ser {e}", "bool": f"Bool.ser {e}", "cp": f"Checkpoint.ethlib_encode {e}"}[k]


def encspec(k):
    if isinstance(k, tuple):
        return f"ArrayU8N.enc {k[1]}#usize (by simp)"
    return {"u64": "U64.ssz_append.bytes_spec", "bool": "Bool.enc",
            "cp": "Checkpoint.ssz_append.bytes_spec"}[k]


def decspec(k):
    if isinstance(k, tuple):
        return f"ArrayU8N.from_ssz_bytes.spec {k[1]}#usize"
    return {"u64": "U64.dec", "bool": "Bool.dec", "cp": "Checkpoint.from_ssz_bytes.spec"}[k]


FS_DEC = ("U64.Insts.LibsszDecodeSszDecode.fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.fixed_size, "
          "Bool.Insts.LibsszDecodeSszDecode.fixed_size")
ISF_DEC = ("U64.Insts.LibsszDecodeSszDecode.is_fixed_size, ArrayU8N.Insts.LibsszDecodeSszDecode.is_fixed_size, "
           "Bool.Insts.LibsszDecodeSszDecode.is_fixed_size, Checkpoint.is_fixed_size")
ISF_ENC = ("U64.Insts.LibsszEncodeSszEncode.is_fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.is_fixed_size, "
           "Bool.Insts.LibsszEncodeSszEncode.is_fixed_size, Checkpoint.enc_is_fixed_size")
SIZES = "uintBytes_size, boolByte, cpEnc_size, alloc.vec.Vec.length"


def wrspec(k, e, sl, pf):
    if isinstance(k, tuple):
        return f"ArrayU8N.wr {k[1]}#usize (by simp) {e} {sl} {pf}"
    return {"u64": f"U64.ssz_write_fixed.bytes_spec {e} {sl} {pf}",
            "bool": f"Bool.ssz_write_fixed.bytes_spec {e} {sl} {pf}",
            "cp": f"Checkpoint.ssz_write_fixed.bytes_spec {e} {sl} {pf}"}[k]


HWF_ENC = ("U64.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, "
           "ArrayU8N.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, "
           "Bool.Insts.LibsszEncodeSszEncode.ssz_has_write_fixed, Checkpoint.has_write_fixed")
FS_ENC = ("U64.Insts.LibsszEncodeSszEncode.fixed_size, ArrayU8N.Insts.LibsszEncodeSszEncode.fixed_size, "
          "Bool.Insts.LibsszEncodeSszEncode.fixed_size, Checkpoint.enc_fixed_size")
WSIZES = "uintBytes_size, boolByte, cpEnc_size"


def gen_encode_verif(w, S, p, ve, fields):
    """Legacy mode: the derived `ssz_append` appends the fields one after another."""
    w(f"theorem {S}.ssz_append.bytes_spec (x : {ve}) (buf : alloc.vec.Vec Std.U8)")
    w(f"    (h : buf.length + ({p}Enc x).size ≤ Usize.max) :")
    w(f"    {ve}.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>")
    w(f"      bytes buf'.val = bytes buf.val ++ {p}Enc x ⦄ := by")
    w(f"  rw [{p}Enc_size] at h")
    w(f"  unfold {ve}.Insts.LibsszEncodeSszEncode.ssz_append")
    w(f"  simp only [{S}.enc_is_fixed_size, bind_ok, ↓reduceIte]")
    b = "buf"
    n = len(fields)
    for i, (f, k) in enumerate(fields, 1):
        bound = f"(by simp [{SIZES}] at *; omega)"
        if i < n:
            w(f"  step with {encspec(k)} x.{f} {b}")
            w(f"    {bound} as ⟨ b{i}, hb{i} ⟩")
            w(f"  have hl{i} := bytes_len hb{i}")
            b = f"b{i}"
        else:
            w(f"  apply WP.spec_mono ({encspec(k)} x.{f} {b}")
            w(f"    {bound})")
            w("  intro b' hb'")
            chain = ["hb'"] + [f"hb{j}" for j in range(n - 1, 0, -1)]
            w(f"  rw [{', '.join(chain)}, {p}Enc]")
            w("  simp only [Array.append_assoc]\n")


def gen_encode_opt(w, S, p, ve, fields, W):
    """libssz: `ssz_append` grows the buffer and `ssz_write_fixed` writes each field."""
    n = len(fields)
    enc = f"{ve}.Insts.LibsszEncodeSszEncode"
    w(f"theorem {S}.has_write_fixed :")
    w(f"    {enc}.ssz_has_write_fixed = ok true := by")
    w(f"  simp [{enc}.ssz_has_write_fixed, {HWF_ENC}]\n")
    w(f"theorem {S}.enc_fixed_size :")
    w(f"    {enc}.fixed_size = ok {W}#usize := by")
    w(f"  simp only [{enc}.fixed_size, {S}.enc_is_fixed_size,")
    w(f"    {FS_ENC}, bind_ok, ↓reduceIte]")
    w("  apply ok_of_spec")
    w("  step*\n")
    doc = f"/-- **`ssz_write_fixed` of `{S}`**: overwrites a {W}-byte segment with the encoding. -/"
    w(doc if len(doc) <= 96 else doc.replace(" the encoding. -/", " the\nencoding. -/"))
    w(f"theorem {S}.ssz_write_fixed.bytes_spec (x : {ve}) (out : Slice Std.U8)")
    w(f"    (h : out.length = {W}) :")
    w(f"    {enc}.ssz_write_fixed x out ⦃ out' =>")
    w(f"      bytes out'.val = {p}Enc x ⦄ := by")
    w(f"  unfold {enc}.ssz_write_fixed")
    w(f"  simp only [{S}.has_write_fixed, {FS_ENC}, bind_ok, ↓reduceIte]")
    # the first n-1 fields: split off the head and write it
    for i, (f, k) in enumerate(fields[:-1], 1):
        w(f"  step with core.slice.Slice.split_at_mut.spec as ⟨ a{i}, r{i}, back{i}, hal{i}, hrl{i}, hav{i}, hrv{i}, hback{i} ⟩")
        w(f"  step with {wrspec(k, 'x.' + f, f'a{i}', '(by scalar_tac)')} as ⟨ c{i}, hc{i} ⟩")
        w(f"  have hcl{i} : c{i}.length = {width(k)} := by")
        w(f"    rw [slice_len_of_bytes hc{i}]; simp [{WSIZES}]")
    # the last one is written into what is left
    f, k = fields[-1]
    w(f"  step with {wrspec(k, 'x.' + f, f'r{n - 1}', '(by scalar_tac)')} as ⟨ c{n}, hc{n} ⟩")
    w(f"  have hcl{n} : c{n}.length = {width(k)} := by")
    w(f"    rw [slice_len_of_bytes hc{n}]; simp [{WSIZES}]")
    # put it back together, from the inside out
    inner = f"c{n}"
    for i in range(n - 1, 0, -1):
        w(f"  have e{i} := hback{i} c{i} ({inner}) (by scalar_tac) (by scalar_tac)")
        inner = f"back{i} (c{i}, {inner})"
    rws = []
    for i in range(1, n):
        rws += [f"e{i}.1", "bytes_append", f"hc{i}"]
    rws += [f"hc{n}", f"{p}Enc"]
    w(f"  rw [{', '.join(rws)}]")
    if n > 2:
        w("  simp only [Array.append_assoc]")
    w("")
    w(f"theorem {S}.ssz_append.bytes_spec (x : {ve}) (buf : alloc.vec.Vec Std.U8)")
    w(f"    (h : buf.length + ({p}Enc x).size ≤ Usize.max) :")
    w(f"    {enc}.ssz_append x buf ⦃ buf' =>")
    w(f"      bytes buf'.val = bytes buf.val ++ {p}Enc x ⦄ := by")
    w(f"  rw [{p}Enc_size] at h")
    w(f"  unfold {enc}.ssz_append")
    w(f"  simp only [{S}.has_write_fixed, {S}.enc_fixed_size, bind_ok, ↓reduceIte]")
    w(f"  exact append_via_write_fixed _ x ({p}Enc x) {W}#usize buf ({p}Enc_size x)")
    w(f"    (fun out ho => {S}.ssz_write_fixed.bytes_spec x out ho) h\n")


def gen(S, p, fields):
    ve = f"verif_example.{S}"
    ws = [width(k) for _, k in fields]
    W = sum(ws)
    names = ", ".join(f'"{f}"' for f, _ in fields)
    out = []
    w = out.append
    w(f"/-! ## `{S}` ({W} bytes) -/\n")
    w(f"def {p}Names : List String := [{names}]")
    w(f"def {p}Fields : List Desc := [{', '.join(desc(k) for _, k in fields)}]\n")
    w(f"def {p}ToV (x : {ve}) : Value :=")
    w(f"  .seq [{', '.join(tov(k, 'x.' + f) for f, k in fields)}]\n")
    article = "an" if S[0] in "AEIOU" else "a"
    w(f"/-- What libssz writes for {article} `{S}`: the fields, one after another. -/")
    w(f"def {p}Enc (x : {ve}) : Bytes :=")
    w(f"  {' ++ '.join(encb(k, 'x.' + f) for f, k in fields)}\n")
    w(f"theorem {p}Enc_size (x : {ve}) : ({p}Enc x).size = {W} := by")
    w(f"  simp [{p}Enc, uintBytes_size, boolByte, cpEnc_size]\n")
    # sizes
    w(f"theorem {S}.is_fixed_size :")
    w(f"    {ve}.Insts.LibsszDecodeSszDecode.is_fixed_size = ok true := by")
    w(f"  simp [{ve}.Insts.LibsszDecodeSszDecode.is_fixed_size, {ISF_DEC}]\n")
    w(f"theorem {S}.enc_is_fixed_size :")
    w(f"    {ve}.Insts.LibsszEncodeSszEncode.is_fixed_size = ok true := by")
    w(f"  simp [{ve}.Insts.LibsszEncodeSszEncode.is_fixed_size, {ISF_ENC}]\n")
    w("@[step]")
    w(f"theorem {S}.fixed_size.spec :")
    w(f"    {ve}.Insts.LibsszDecodeSszDecode.fixed_size ⦃ n => n.val = {W} ⦄ := by")
    w(f"  simp only [{ve}.Insts.LibsszDecodeSszDecode.fixed_size, {S}.is_fixed_size,")
    w(f"    {FS_DEC}, bind_ok, ↓reduceIte]")
    w("  step*\n")
    # decode
    w(f"/-- **Decode of `{S}` ≡ EthLib**, with exact errors (`ErrMatch`). -/")
    w(f"theorem {S}.from_ssz_bytes.spec (s : Slice Std.U8) (hs : s.length < 2 ^ 32) :")
    w(f"    {ve}.Insts.LibsszDecodeSszDecode.from_ssz_bytes s ⦃ r =>")
    w(f"      Agrees {p}ToV r (deserialize (.container {p}Names {p}Fields) (bytes s.val)) ⦄ := by")
    w(f"  rw [eth_decode_fixed {p}Names {p}Fields {ws} rfl _ (by rw [bytes_size]; exact hs)]")
    w(f"  simp only [bytes_size, cuts, {p}Fields, List.sum_cons, List.sum_nil, Nat.reduceAdd]")
    w(f"  unfold {ve}.Insts.LibsszDecodeSszDecode.from_ssz_bytes")
    w(f"  simp only [{S}.is_fixed_size, bind_ok, ↓reduceIte]")
    w(f"  step with {S}.fixed_size.spec as ⟨ ex, hex ⟩")
    w("  have hl := Slice.len_val s")
    w(f"  by_cases hne : s.length ≠ {W}")
    w("  · have : (s.len != ex) = true := by simp; scalar_tac")
    w("    simp only [this, ↓reduceIte, WP.spec_ok, hne, ne_eq, not_false_eq_true, Agrees]")
    w("    have := ErrMatch.fixedLength ex s.len")
    w("    rw [hex, hl] at this")
    w("    exact this")
    w(f"  have hl' : s.val.length = {W} := by simp [Slice.length] at hne; exact hne")
    w("  have : ¬ (s.len != ex) = true := by simp; scalar_tac")
    w("  simp only [this, Bool.false_eq_true, ↓reduceIte, hl', ne_eq, not_true_eq_false,")
    w(f"    {FS_DEC}, bind_ok]")
    w("  rw [" + ", ".join(["deserializeFields"] * (len(fields) + 1)) + "]")
    prev = "(List.drop_zero (l := s.val)).symm"
    cur = "s"
    have_cp = False
    for i, (f, k) in enumerate(fields, 1):
        extra = ""
        if k == "cp":
            if not have_cp:
                w("  step with Checkpoint.fixed_size.spec as ⟨ wcp, hwcp ⟩")
                have_cp = True
            wt = "wcp"
            extra = " with hwcp"
        else:
            wt = f"{width(k)}#usize"
        w(f"  fixed_field s{i} r{i} hr{i} := {cur}, {wt} from {prev} using {decspec(k)}{extra}")
        prev, cur = f"hr{i}", f"r{i}"
    w("  simp only [WP.spec_ok, Except.pure, ex_ok_bind, Agrees]")
    w("  rfl\n")
    # encode
    if OPT:
        gen_encode_opt(w, S, p, ve, fields, W)
    else:
        gen_encode_verif(w, S, p, ve, fields)
    parts = ", ".join(encb(k, 'x.' + f) for f, k in fields)
    w(f"theorem {S}.ethlib_encode (x : {ve}) :")
    w(f"    serialize (.container {p}Names {p}Fields) ({p}ToV x) = .ok ({p}Enc x) := by")
    w(f"  have hc : {p}Enc x = concatParts [{parts}] := by")
    w(f"    simp [{p}Enc, concatParts, Array.append_assoc]")
    w(f"  rw [{p}ToV, {p}Fields, hc]")
    w("  apply eth_encode_fixed _ _ _ _ rfl")
    sers = []
    for f, k in fields:
        sers += ["serializeFields_cons", ser(k, 'x.' + f), "ex_ok_bind"]
    w("  · rw [" + ", ".join(sers) + ", serializeFields_nil]")
    w("    rfl")
    w(f"  · rw [← hc, {p}Enc_size]; omega\n")
    w(f"/-- **Encode of `{S}` ≡ EthLib.** -/")
    w(f"theorem {S}.encode.agrees (x : {ve}) (buf : alloc.vec.Vec Std.U8)")
    w(f"    (h : buf.length + {W} ≤ Usize.max) :")
    w(f"    {ve}.Insts.LibsszEncodeSszEncode.ssz_append x buf ⦃ buf' =>")
    w(f"      ∃ enc, serialize (.container {p}Names {p}Fields) ({p}ToV x) = .ok enc ∧")
    w("        bytes buf'.val = bytes buf.val ++ enc ⦄ := by")
    w(f"  apply WP.spec_mono ({S}.ssz_append.bytes_spec x buf (by rw [{p}Enc_size]; exact h))")
    w("  intro b' hb'")
    w(f"  exact ⟨_, {S}.ethlib_encode x, hb'⟩\n")
    return "\n".join(out) + "\n"


path = sys.argv[1]
src = open(path).read()
# This branch has the verif codec only: always generate the field-by-field encode proofs
# (the direct-write `ssz_write_fixed` proofs are for the optimized codec).
OPT = False
END = "end Libssz.Proofs"
marker = "/-! ## `Fork`"
if marker in src:  # regenerating: drop what was generated before
    src = src[:src.index(marker)] + END + "\n"
j = src.index(END)
gen_txt = "".join(gen(*t) for t in STRUCTS)
open(path, "w").write(src[:j] + gen_txt + src[j:])
