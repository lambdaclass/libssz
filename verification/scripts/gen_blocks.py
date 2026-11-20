"""Generates lean/Libssz/SszTypes/Proofs/Blocks.lean.

Usage: python3 -I gen_blocks.py OUTPUT
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rows import row  # noqa: E402

T = "libssz_types.verif_example"
AU8 = "libssz_types.ArrayU8N.Insts.Libssz_merkleHashTreeRoot.hash_tree_root"
AU64 = "libssz_types.U64.Insts.Libssz_merkleHashTreeRoot.hash_tree_root"
def MAL(n): return f"libssz_types.libssz_merkle.verif_example.{n}.Insts.Libssz_merkleHashTreeRoot.hash_tree_root"

# Field: (name, desc, value, step, alias to unfold)
def bytesf(f, n): return (f, f".byteVector {n}", f".bytes (bytes x.{f}.val)",
    f"ArrayU8N.hash_tree_root.spec inst h hl x.{f}", AU8)
def u64f(f): return (f, "Desc.uint64", f".uint x.{f}.val", f"U64.hash_tree_root.spec inst h x.{f}", AU64)
def merklef(f, ty, names, fields, v):  # container from the tree extraction
    return (f, f".container {names} {fields}", f"{v} x.{f}", f"{ty}.hash_tree_root.spec inst h hl x.{f}", MAL(ty))
def localf(f, ty, names, fields, v, hyps=""):
    return (f, f".container {names} {fields}", f"{v} x.{f}", f"{ty}.hash_tree_root.spec inst h hl x.{f}{hyps}", None)
def listc(f, ty, names, fields, v, n, hlen, good="trivial", local=True):
    """A list of containers: its items give their root through their rows (`{ty}.rows`), and
    `good` proves the invariant of each item `y ∈ x.{f}` (`hy`)."""
    hi = f"{T}.{ty}.Insts.Libssz_merkleHashTreeRoot" if local else f"libssz_types.libssz_merkle.verif_example.{ty}.Insts.Libssz_merkleHashTreeRoot"
    ei = f"{T}.{ty}.Insts.LibsszEncodeSszEncode" if local else f"libssz_types.libssz_merkle.verif_example.{ty}.Insts.LibsszEncodeSszEncode"
    return (f, f".list (.container {names} {fields}) {n}", f".seq (x.{f}.val.map {v})",
        f"SszList.composite_root inst h hl\n      {hi}\n      {ei} rfl\n      (.container {names} {fields}) rfl {v} _ _ ({ty}.rows inst h hl)\n      x.{f} {hlen} (fun y hy => {good})", None)
def vec32(f, n, hl): return (f, f".vector (.byteVector 32) {n}", f"bytesSeqV x.{f}",
    f"SszVectorBytes32.hash_tree_root.spec inst h hl x.{f} {hl} (by scalar_tac)", None)
def list32(f, n, hl): return (f, f".list (.byteVector 32) {n}", f"bytesSeqV x.{f}",
    f"SszListBytes32.hash_tree_root.spec inst h hl x.{f} {hl} (by scalar_tac)", None)
def vecu64(f, n, hl): return (f, f".vector Desc.uint64 {n}", f"uintSeqV x.{f}",
    f"SszVectorU64.hash_tree_root.spec inst h hl x.{f} {hl} (by scalar_tac)", None)

C = []  # (name, Lean type, names, fields, value, hypotheses, extra binders, doc, prefix)
def cont(name, fields, hyps="", doc="", ty=None, extra=""):
    C.append((name, ty or f"{T}.{name}", fields, hyps, doc, extra))

pre = {"Eth1Data": "eth", "SignedBeaconBlockHeader": "sbh", "ProposerSlashing": "ps",
       "AttesterSlashing": "as", "VoluntaryExit": "ve", "SignedVoluntaryExit": "sve",
       "BeaconBlockBody": "body", "BeaconBlock": "block", "BeaconState": "state"}

cont("Eth1Data", [bytesf("deposit_root", 32), u64f("deposit_count"), bytesf("block_hash", 32)],
     doc="phase0")
cont("SignedBeaconBlockHeader", [merklef("message", "BeaconBlockHeader", "Proofs.bbhNames", "Proofs.bbhFields", "bbhV"),
     bytesf("signature", 96)], doc="phase0")
cont("ProposerSlashing", [localf("signed_header_1", "SignedBeaconBlockHeader", "sbhNames", "sbhFields", "sbhV"),
     localf("signed_header_2", "SignedBeaconBlockHeader", "sbhNames", "sbhFields", "sbhV")], doc="phase0")
cont("AttesterSlashing", [localf("attestation_1", "IndexedAttestation", "iaNames", "iaFields", "iaV", " h1"),
     localf("attestation_2", "IndexedAttestation", "iaNames", "iaFields", "iaV", " h2")],
     hyps="\n    (h1 : x.attestation_1.attesting_indices.length ≤ 2048)\n    (h2 : x.attestation_2.attesting_indices.length ≤ 2048)",
     doc="phase0. Requires both index lists to be within their limit")
cont("VoluntaryExit", [u64f("epoch"), u64f("validator_index")], doc="phase0")
cont("SignedVoluntaryExit", [localf("message", "VoluntaryExit", "veNames", "veFields", "veV"), bytesf("signature", 96)],
     doc="phase0")

def asinv(y): return f"(∀ s ∈ {y}.val, s.attestation_1.attesting_indices.length ≤ 2048 ∧ s.attestation_2.attesting_indices.length ≤ 2048)"
cont("BeaconBlockBody", [
    bytesf("randao_reveal", 96),
    localf("eth1_data", "Eth1Data", "ethNames", "ethFields", "ethV"),
    bytesf("graffiti", 32),
    listc("proposer_slashings", "ProposerSlashing", "psNames", "psFields", "psV", 16, "hps"),
    listc("attester_slashings", "AttesterSlashing", "asNames", "asFields", "asV", 2, "has",
          "has' y hy"),
    listc("attestations", "Attestation", "attNames", "attFields", "attV", 128, "hatt",
          "hatt' y hy"),
    listc("deposits", "Deposit", "depNames", "depFields", "depV", 16, "hdep", "hdep' y hy"),
    listc("voluntary_exits", "SignedVoluntaryExit", "sveNames", "sveFields", "sveV", 16, "hve"),
  ], hyps="""
    (hps : x.proposer_slashings.length ≤ 16) (has : x.attester_slashings.length ≤ 2)
    (has' : ∀ s ∈ x.attester_slashings.val,
      s.attestation_1.attesting_indices.length ≤ 2048 ∧ s.attestation_2.attesting_indices.length ≤ 2048)
    (hatt : x.attestations.length ≤ 128) (hatt' : ∀ a ∈ x.attestations.val, BlInv a.aggregation_bits)
    (hdep : x.deposits.length ≤ 16) (hdep' : ∀ d ∈ x.deposits.val, d.proof.length = 33)
    (hve : x.voluntary_exits.length ≤ 16)""",
  doc="phase0, with the mainnet sizes. Requires the invariants of its lists and of their contents")
cont("BeaconBlock", [u64f("slot"), u64f("proposer_index"), bytesf("parent_root", 32), bytesf("state_root", 32),
    localf("body", "BeaconBlockBody", "bodyNames", "bodyFields", "bodyV",
           " hps has has' hatt hatt' hdep hdep' hve")],
  hyps="""
    (hps : x.body.proposer_slashings.length ≤ 16) (has : x.body.attester_slashings.length ≤ 2)
    (has' : ∀ s ∈ x.body.attester_slashings.val,
      s.attestation_1.attesting_indices.length ≤ 2048 ∧ s.attestation_2.attesting_indices.length ≤ 2048)
    (hatt : x.body.attestations.length ≤ 128) (hatt' : ∀ a ∈ x.body.attestations.val, BlInv a.aggregation_bits)
    (hdep : x.body.deposits.length ≤ 16) (hdep' : ∀ d ∈ x.body.deposits.val, d.proof.length = 33)
    (hve : x.body.voluntary_exits.length ≤ 16)""",
  doc="phase0: the same invariants as `BeaconBlockBody`, for its `body`")
cont("BeaconState", [
    u64f("genesis_time"), bytesf("genesis_validators_root", 32), u64f("slot"),
    merklef("fork", "Fork", "Proofs.forkNames", "Proofs.forkFields", "forkV"),
    merklef("latest_block_header", "BeaconBlockHeader", "Proofs.bbhNames", "Proofs.bbhFields", "bbhV"),
    vec32("block_roots", 8192, "hbr"), vec32("state_roots", 8192, "hsr"),
    list32("historical_roots", 16777216, "hhr"),
    localf("eth1_data", "Eth1Data", "ethNames", "ethFields", "ethV"),
    listc("eth1_data_votes", "Eth1Data", "ethNames", "ethFields", "ethV", 2048, "hev"),
    u64f("eth1_deposit_index"),
    ("validators", ".list (.container Proofs.valNames Proofs.valFields) VRL.val", ".seq (x.validators.val.map valV)",
     "SszListValidator.hash_tree_root.spec inst h hl _ x.validators hval", None),
    ("balances", ".list Desc.uint64 VRL.val", "uintSeqV x.balances",
     "SszListU64.hash_tree_root.spec inst h hl x.balances hbal hvrl", None),
    vec32("randao_mixes", 65536, "hrm"), vecu64("slashings", 8192, "hsl"),
    listc("previous_epoch_attestations", "PendingAttestation", "paNames", "paFields", "paV", 4096,
          "hpa", "hpa' y hy"),
    listc("current_epoch_attestations", "PendingAttestation", "paNames", "paFields", "paV", 4096,
          "hca", "hca' y hy"),
    ("justification_bits", ".bitVector 4", "bvV x.justification_bits",
     "SszBitvector.hash_tree_root.spec inst h hl x.justification_bits hjb", None),
    merklef("previous_justified_checkpoint", "Checkpoint", "Proofs.cpNames", "Proofs.cpFields", "cpV"),
    merklef("current_justified_checkpoint", "Checkpoint", "Proofs.cpNames", "Proofs.cpFields", "cpV"),
    merklef("finalized_checkpoint", "Checkpoint", "Proofs.cpNames", "Proofs.cpFields", "cpV"),
  ], ty=f"({T}.BeaconState VRL)", extra="{VRL : Std.Usize} ",
  hyps="""
    (hvrl : 8 * VRL.val ≤ Usize.max)
    (hbr : x.block_roots.length = 8192) (hsr : x.state_roots.length = 8192)
    (hhr : x.historical_roots.length ≤ 16777216) (hev : x.eth1_data_votes.length ≤ 2048)
    (hval : x.validators.length ≤ VRL.val) (hbal : x.balances.length ≤ VRL.val)
    (hrm : x.randao_mixes.length = 65536) (hsl : x.slashings.length = 8192)
    (hpa : x.previous_epoch_attestations.length ≤ 4096)
    (hpa' : ∀ a ∈ x.previous_epoch_attestations.val, BlInv a.aggregation_bits)
    (hca : x.current_epoch_attestations.length ≤ 4096)
    (hca' : ∀ a ∈ x.current_epoch_attestations.val, BlInv a.aggregation_bits)
    (hjb : Canon (bytes x.justification_bits.bytes.val) 4)""",
  doc="phase0, with `VALIDATOR_REGISTRY_LIMIT` as a parameter (`VRL`). Requires the "
      "invariants of its lists, vectors and bitfields, and that `8 · VRL` fit in a `usize` "
      "(on mainnet, 2^43)")

out = []
for name, ty, fields, hyps, doc, extra in C:
    p = pre[name]
    names = ", ".join(f'"{f[0]}"' for f in fields)
    descs = ", ".join(f[1] for f in fields)
    vals = ", ".join(f[2] for f in fields)
    params = f" ({extra.strip()[1:-1]})" if extra else ""
    vparams = f" {{VRL : Std.Usize}}" if extra else ""
    argfields = " VRL" if extra else ""
    if extra:
        out.append(f"def {p}Names : List String := [{names}]\ndef {p}Fields (VRL : Std.Usize) : List Desc := [{descs}]\n"
                   f"def {p}V{vparams} (x : {ty}) : Value :=\n  .seq [{vals}]\n")
    else:
        out.append(f"def {p}Names : List String := [{names}]\ndef {p}Fields : List Desc := [{descs}]\n"
                   f"def {p}V (x : {ty}) : Value :=\n  .seq [{vals}]\n")
# The containers that appear in lists, with their invariant (about `x`) and the tactic that
# names what their steps use.
ROWS = {
    "Eth1Data": ("True", ""),
    "ProposerSlashing": ("True", ""),
    "AttesterSlashing": ("x.attestation_1.attesting_indices.length ≤ 2048 ∧ "
                         "x.attestation_2.attesting_indices.length ≤ 2048",
                         "obtain ⟨ h1, h2 ⟩ := hgood"),
    "SignedVoluntaryExit": ("True", ""),
}

C2 = []
for name, ty, fields, hyps, doc, extra in C:
    p = pre[name]
    n = len(fields)
    fargs = f"{p}Fields VRL" if extra else f"{p}Fields"
    al = sorted({f[4] for f in fields if f[4]})
    xs = ", ".join(f"bytes a{i}.val" for i in range(n))
    arr = ", ".join(f"a{i}" for i in range(n))
    hs = ", ".join(f"h{i}" for i in range(n))
    steps = "\n".join(f"  step with {f[3]} as ⟨ a{i}, h{i} ⟩" for i, f in enumerate(fields))
    helpers = "".join(f" {hh}" for hh in ("bytesSeqV", "uintSeqV", "bvV", "blV")
                      if any(hh in f[2] for f in fields))
    unf = ("  simp only [" + ",\n    ".join(al + ["libssz_types.libssz_merkle.merkleize_in_place"]) + "]\n")
    C2.append(f'''include hl in
/-- **`{name}`** ({doc}): the `hash_tree_root` the macro generates is EthLib's. -/
theorem {name}.hash_tree_root.spec {extra}(x : {ty}){hyps} :
    {T}.{name}.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
      inst x h ⦃ r => hashTreeRoot (.container {p}Names ({fargs})) ({p}V x) = .ok (bytes r.val) ⦄ := by
  unfold {T}.{name}.Insts.Libssz_merkleHashTreeRoot.hash_tree_root
{unf}{steps}
  simp only [lift, bind_ok, Array.to_slice_mut]
  step with merkleize_in_place.spec inst h hl _ none (by simp) as ⟨ r, rest, hr, _ ⟩
  unfold {p}V{helpers}
  rw [hashTreeRoot_container _ _ _ [{xs}] rfl
    (by simp only [{p}Fields] at *; simp [{hs}, Pure.pure, Except.pure, Bind.bind, Except.bind])]
  have hc : chunksOf (Array.make {n}#usize [{arr}] (by simp)).to_slice.val =
      #[{xs}] := by simp [chunksOf, Array.to_slice]
  simp only [hc, Option.map_none] at hr
  rw [show ({fargs}).length = (#[{xs}]).size from rfl, merkleizeBounded_some_self, ← hr]
''')
    if name in ROWS:
        good, naming = ROWS[name]
        C2.append(row(name, f"{T}.{name}", f"{p}Names", fargs, f"{p}V", [f[3] for f in fields],
                      alias=al, helpers=[hh for hh in ("bytesSeqV", "uintSeqV", "bvV", "blV")
                                         if any(hh in f[2] for f in fields)],
                      good=good, naming=naming))

head = '''module
public import Libssz.SszTypes.Proofs.Bits
@[expose] public section

/-!
# `BeaconBlock` and `BeaconState` (phase0)

The remaining phase0 containers, with the mainnet sizes: the list items of `BeaconBlockBody`
(`ProposerSlashing`, `AttesterSlashing`, `SignedVoluntaryExit`, …), `BeaconBlockBody`,
`BeaconBlock` and `BeaconState`. Each one composes the theorems of its fields: lists of
containers (`SszList.composite_root`), lists and vectors of bytes and of integers, and
bitfields (`Bits.lean`).

`BeaconState` takes the limit of `validators` and `balances` as a parameter (`VRL`): in the
Aeneas model `usize` may be 32 bits wide, and then mainnet's 2^40 is not a `usize`. The
theorem holds for every `VRL`; on 64 bits, `BeaconState<2^40>` is the mainnet one.

The hypotheses are the invariants of the Rust types (the length of each `SszVector`, the bound
of each `SszList`, the canonical bytes of each bitfield), also for what is inside the lists.

This file is generated by `scripts/gen_blocks.py`.
-/

open Aeneas Aeneas.Std Result
open Libssz.Proofs (byte bytes)
open EthLib.Serialization.Ssz
open Libssz.Merkle

namespace Libssz.SszTypes

'''
body = "\n".join(out) + '''
section Containers

variable {H : Type} (inst : libssz_merkle.Sha256Hasher H) (h : H) (hl : Lawful inst h)

''' + "\n".join(C2) + '''
end Containers

end Libssz.SszTypes
'''
open(sys.argv[1], "w").write(head + body)
