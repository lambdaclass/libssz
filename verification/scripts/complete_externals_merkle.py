"""Completes TypesExternal.lean and FunsExternal.lean of the SHA-NI kernel of libssz-merkle
from the templates Aeneas generates.

Usage: python3 complete_externals_merkle.py DIR
     (DIR has TypesExternal_Template.lean and FunsExternal_Template.lean; the script writes
     TypesExternal.lean and FunsExternal.lean and deletes the templates. It also rewrites the
     shape of the `ZERO_HASHES` table in Funs.lean: see below)

`crates/ssz-merkle/src/shani.rs` uses eight intrinsics from `core::arch::x86_64`, the type
`__m128i` and `core::hint::black_box`. None of them has a Rust body Aeneas can translate, so it
leaves them as `axiom`. Here each one is replaced by a hand-written definition:

* `__m128i`: four 32-bit lanes (`Libssz.Merkle.M128`);
* the eight intrinsics: the models in `Libssz/Merkle/Intrinsics.lean`. None of them fails.
  The immediates (`IMM8`, a Rust const generic) arrive as a first `Std.I32` argument and are
  passed to the model as a natural number;
* `black_box`: the identity. Rust documents it that way: it only hides the value from the
  optimizer;
* **What the codec already defines.** `as_chunks`, `Iterator::map`, the `next` of `Map` and
  `Vec::reserve` are the same standard-library functions the codec uses, and
  `Libssz/Code/FunsExternal.lean` already defines them with their models. Defining them twice
  clashes when both extractions are imported together: the script removes the declaration from
  the template and imports that one. It is not a new assumption.
* **Linking with the codec.** The tree uses things from the `ssz` crate (the codec): the
  `SszEncode` trait and its implementations for `u64` and `[u8; N]` (in the `hash_tree_root` of
  `Vec<T>`), and `ContainerEncoder` (in the `SszEncode` the macro derives for the containers of
  `verif_example.rs`). Aeneas leaves a partial copy of the trait and holes for the functions.
  The codec extraction (`Libssz/Code/`) already has all of that, complete, translated and
  with proofs. Each codec declaration is replaced by the one with **the same Rust path** in
  that extraction: the trait and `ContainerEncoder` become the codec's, and the functions and
  implementations become aliases of the codec's. How, and what has to be trusted, is explained
  in `link.py`.

The technique (intrinsics as external functions with a hand-written model) is the one from
gattaca-com/silver, `crates/crypto_simd/proof/lean/LeanBlsSimd/Extracted/FunsExternal.lean`.

If any template has any other `axiom`, the script fails: it has to be inspected by hand.

**The `ZERO_HASHES` table.** Aeneas writes it as a single term: an array of 65 arrays of 32
literal bytes. With more than about 40 rows, Lean runs out of memory elaborating it (more than
14 GB). The script only changes its shape: each row becomes a separate definition
(`ZERO_HASHES.row0` … `ZERO_HASHES.row64`) and the table is the array of those 65 rows. The
bytes are the same, in the same order; the script fails if the table does not have exactly the
expected shape. And it does not need to be trusted: the proof shows that row 0 is the zero node
and that each row is the `combine` of the previous one with itself, so a table with one byte
changed would not pass.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import link  # noqa: E402

M = "Libssz.Merkle"
V = "core.core_arch.x86.__m128i"

# (name, signature Aeneas generates, body added to it)
FUNCTIONS = [
    ("_mm_sha256msg1_epu32",
     """@[rust_fun "core::core_arch::x86::sha::_mm_sha256msg1_epu32"]
axiom core.core_arch.x86.sha._mm_sha256msg1_epu32
  :
  core.core_arch.x86.__m128i → core.core_arch.x86.__m128i → Result
    core.core_arch.x86.__m128i
""",
     f"fun a b => ok ({M}._mm_sha256msg1_epu32 a b)"),
    ("_mm_sha256msg2_epu32",
     """@[rust_fun "core::core_arch::x86::sha::_mm_sha256msg2_epu32"]
axiom core.core_arch.x86.sha._mm_sha256msg2_epu32
  :
  core.core_arch.x86.__m128i → core.core_arch.x86.__m128i → Result
    core.core_arch.x86.__m128i
""",
     f"fun a b => ok ({M}._mm_sha256msg2_epu32 a b)"),
    ("_mm_sha256rnds2_epu32",
     """@[rust_fun "core::core_arch::x86::sha::_mm_sha256rnds2_epu32"]
axiom core.core_arch.x86.sha._mm_sha256rnds2_epu32
  :
  core.core_arch.x86.__m128i → core.core_arch.x86.__m128i →
    core.core_arch.x86.__m128i → Result core.core_arch.x86.__m128i
""",
     f"fun a b k => ok ({M}._mm_sha256rnds2_epu32 a b k)"),
    ("_mm_add_epi32",
     """@[rust_fun "core::core_arch::x86::sse2::_mm_add_epi32"]
axiom core.core_arch.x86.sse2._mm_add_epi32
  :
  core.core_arch.x86.__m128i → core.core_arch.x86.__m128i → Result
    core.core_arch.x86.__m128i
""",
     f"fun a b => ok ({M}._mm_add_epi32 a b)"),
    ("_mm_set_epi32",
     """@[rust_fun "core::core_arch::x86::sse2::_mm_set_epi32"]
axiom core.core_arch.x86.sse2._mm_set_epi32
  :
  Std.I32 → Std.I32 → Std.I32 → Std.I32 → Result
    core.core_arch.x86.__m128i
""",
     f"fun e3 e2 e1 e0 => ok ({M}._mm_set_epi32 (Int32.ofBitVec e3.bv) "
     "(Int32.ofBitVec e2.bv)\n    (Int32.ofBitVec e1.bv) (Int32.ofBitVec e0.bv))"),
    ("_mm_shuffle_epi32",
     """@[rust_fun "core::core_arch::x86::sse2::_mm_shuffle_epi32"]
axiom core.core_arch.x86.sse2._mm_shuffle_epi32
  (IMM8 : Std.I32) :
  core.core_arch.x86.__m128i → Result core.core_arch.x86.__m128i
""",
     f"fun a => ok ({M}._mm_shuffle_epi32 IMM8.bv.toNat a)"),
    ("_mm_extract_epi32",
     """@[rust_fun "core::core_arch::x86::sse41::_mm_extract_epi32"]
axiom core.core_arch.x86.sse41._mm_extract_epi32
  (IMM8 : Std.I32) : core.core_arch.x86.__m128i → Result Std.I32
""",
     f"fun a => ok ⟨({M}._mm_extract_epi32 IMM8.bv.toNat a).toBitVec⟩"),
    ("_mm_alignr_epi8",
     """@[rust_fun "core::core_arch::x86::ssse3::_mm_alignr_epi8"]
axiom core.core_arch.x86.ssse3._mm_alignr_epi8
  (IMM8 : Std.I32) :
  core.core_arch.x86.__m128i → core.core_arch.x86.__m128i → Result
    core.core_arch.x86.__m128i
""",
     f"fun a b => ok ({M}._mm_alignr_epi8 IMM8.bv.toNat a b)"),
    ("black_box",
     """@[rust_fun "core::hint::black_box"]
axiom core.hint.black_box {T : Type _} : T → Result T
""",
     "fun x => ok x"),
]

CODEC = None  # (origin, index) of the codec extraction: set by main()
AT_ROOT = None  # the names that Libssz/Code/FunsExternal.lean defines
RENAMES = {}  # the codec structures that are removed from Types.lean
COUNTS = {}


def link_codec(src, renames=None):
    """Links what comes from the `ssz` crate with the codec, and removes the holes the codec
    already defines with the same name (the standard-library models)."""
    return link.link_blocks(src, "libssz_merkle::", [CODEC], COUNTS, renames, AT_ROOT,
                            linkable=lambda path: path.startswith("libssz::"))


def complete_functions(src):
    src = src.replace(
        '-- This is a template file: rename it to "FunsExternal.lean" and fill the holes.',
        "-- Generated by scripts/complete_externals_merkle.py from the Aeneas template.")
    src = link_codec(link.rename(src, RENAMES))
    imports = "public import Libssz.Merkle.Code.Types\n"
    assert src.count(imports) == 1, "the header of the functions template changed"
    src = src.replace(imports, imports + "public import Libssz.Code.Funs\n")
    for name, signature, body in FUNCTIONS:
        assert src.count(signature) == 1, f"the signature of {name} changed in the template"
        definition = signature.replace("\naxiom ", "\ndef ", 1).rstrip("\n")
        comment = (
            "/- Hand-written model: the identity (`black_box` only hides the value from the\n"
            "optimizer). -/\n" if name == "black_box" else
            "/- Hand-written model: see `Libssz/Merkle/Intrinsics.lean`. -/\n")
        src = src.replace(signature, comment + definition + " :=\n  " + body + "\n")
    assert "axiom" not in src, "an axiom was left without a model in FunsExternal"
    return src


TYPE = f"""@[rust_type "core::core_arch::x86::__m128i"]
axiom {V} : Type
"""


def complete_types(src):
    src = src.replace(
        '-- This is a template file: rename it to "TypesExternal.lean" and fill the holes.',
        "-- Generated by scripts/complete_externals_merkle.py from the Aeneas template.")
    imports = "public import Aeneas\n"
    assert src.count(imports) == 1, "the header of the types template changed"
    src = src.replace(imports, imports + f"public import {M}.Intrinsics\n")
    assert src.count(TYPE) == 1, "the declaration of __m128i changed in the template"
    # The name `__m128i` comes from Rust; Mathlib's naming linter complains about `__`.
    option = "set_option linter.internalConstructors false\n"
    assert src.count(option) == 1, "the header of the types template changed"
    src = src.replace(option, option + "set_option linter.style.nameCheck false\n")
    src = link.rename(link_codec(src, RENAMES), RENAMES)
    src = src.replace(TYPE, f"""/- Hand-written model: see `Libssz/Merkle/Intrinsics.lean`. -/
@[rust_type "core::core_arch::x86::__m128i"]
abbrev {V} : Type := {M}.M128
""")
    assert "axiom" not in src, "an axiom was left without a model in TypesExternal"
    return src


TABLE_START = (
    "@[global_simps, irreducible]\n"
    "def ZERO_HASHES : Array (Array Std.U8 32#usize) 65#usize :=\n"
    "  let a := Array.repeat 32#usize 0#u8\n"
    "  Array.make 65#usize [\n"
    "    a,\n")
TABLE_END = "\n      ]\n    ]\n"


def split_table(src):
    assert src.count(TABLE_START) == 1, "the shape of ZERO_HASHES changed in Funs.lean"
    i = src.index(TABLE_START)
    j = src.index(TABLE_END, i) + len(TABLE_END)
    body = src[i + len(TABLE_START):j - len("    ]\n")]
    rows = re.findall(r"Array\.make 32#usize \[([^\]]*)\]", body)
    assert len(rows) == 64, f"ZERO_HASHES: {len(rows)} literal rows, expected 64"
    rest = re.sub(r"Array\.make 32#usize \[[^\]]*\]", "", body)
    assert set(rest) <= set(" ,\n"), "ZERO_HASHES has something besides the rows"
    bytes_ = [[int(b) for b in re.findall(r"(\d+)#u8", f)] for f in rows]
    assert all(len(f) == 32 and all(0 <= b < 256 for b in f) for f in bytes_)
    assert all(re.sub(r"\d+#u8|[\s,]", "", f) == "" for f in rows)
    defs = ["/-- Row 0 of `ZERO_HASHES`: the zero node. -/\n"
            "def ZERO_HASHES.row0 : Array Std.U8 32#usize := Array.repeat 32#usize 0#u8\n"]
    for k, f in enumerate(bytes_, start=1):
        lines = [", ".join(f"{b}#u8" for b in f[m:m + 8]) for m in range(0, 32, 8)]
        defs.append(f"/-- Row {k} of `ZERO_HASHES`. -/\n"
                    f"def ZERO_HASHES.row{k} : Array Std.U8 32#usize :=\n"
                    "  Array.make 32#usize [\n    " + ",\n    ".join(lines) + "\n  ]\n")
    table = ("@[global_simps, irreducible]\n"
             "def ZERO_HASHES : Array (Array Std.U8 32#usize) 65#usize :=\n"
             "  Array.make 65#usize [\n    "
             + ",\n    ".join(f"ZERO_HASHES.row{k}" for k in range(65)) + "\n  ]\n")
    # The rows go before the doc comment of the table.
    doc = src.rindex("/-- [libssz_merkle::ZERO_HASHES]", 0, i)
    notice = ("-- The 65 rows of `ZERO_HASHES`, split by scripts/complete_externals_merkle.py\n"
              "-- so that Lean can elaborate the table. The bytes are the ones Aeneas generated.\n")
    return src[:doc] + notice + "\n".join(defs) + "\n" + src[doc:i] + table + src[j:]


def main():
    global CODEC, AT_ROOT
    folder = sys.argv[1]
    codec = os.path.join(folder, "..", "..", "Code")
    CODEC = link.extraction(codec, "libssz_codec", "codec")
    AT_ROOT = link.root_names(os.path.join(codec, "FunsExternal.lean"))
    # Types first (TypesExternal and Types): they collect in RENAMES the codec structures and
    # types that are removed, which are then renamed in Funs and FunsExternal.
    types_template = os.path.join(folder, "TypesExternal_Template.lean")
    with open(types_template) as f:
        external_types = complete_types(f.read())
    types = os.path.join(folder, "Types.lean")
    with open(types) as f:
        src = f.read()
    imports = "public import Aeneas\n"
    assert src.count(imports) == 1, "the Types.lean header changed"
    src = src.replace(imports, imports + "public import Libssz.Code.Types\n")
    src = link.rename(link_codec(src, RENAMES), RENAMES)
    with open(types, "w") as f:
        f.write(src)
    external_types = link.rename(external_types, RENAMES)
    with open(os.path.join(folder, "TypesExternal.lean"), "w") as f:
        f.write(external_types)
    os.remove(types_template)
    funs = os.path.join(folder, "Funs.lean")
    with open(funs) as f:
        src = split_table(link_codec(link.rename(f.read(), RENAMES)))
    with open(funs, "w") as f:
        f.write(src)
    template = os.path.join(folder, "FunsExternal_Template.lean")
    with open(template) as f:
        src = complete_functions(f.read())
    with open(os.path.join(folder, "FunsExternal.lean"), "w") as f:
        f.write(src)
    os.remove(template)
    print(f"linked with the codec: {COUNTS.get('codec', 0)}; "
          f"already defined by the codec: {COUNTS.get('already defined', 0)}")


if __name__ == "__main__":
    main()
