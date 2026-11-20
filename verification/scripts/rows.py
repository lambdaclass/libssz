"""Generates the proof of the rows (`Rows`) of a container from `verif_example.rs`.

Lists and vectors of containers ask `hash_tree_roots` for the roots of their items, which uses
`hash_tree_root_row`: the row of a container is the roots of its fields, padded with zeros up
to the next power of two. The row proof has the same per-field steps as the proof of the
container's `hash_tree_root`; only what happens to the roots changes (they are written into
the row instead of being passed to `merkleize_in_place`), and so does the closing step
(`container_row_root`).

`row(...)` returns the text of the theorem `<Name>.rows`.
"""


def width(k):
    """The first power of two that is not smaller than `k`, and its exponent."""
    w, d = 1, 0
    while w < k:
        w, d = 2 * w, d + 1
    return w, d


def row(name, path, names, fields, value, steps, alias=(), helpers=(), good="True",
        naming="", doc="", reduce=True):
    """`path`: the Lean type (`libssz_types.verif_example.Name`). `steps`: the step of each
    field, as in the `hash_tree_root` proof (`U64.hash_tree_root.spec inst h x.f`).
    `good`: the item invariant (about `x`); `naming`: the tactic that gives its parts the
    names the steps use."""
    k = len(steps)
    w, d = width(k)
    inst = f"{path}.Insts.Libssz_merkleHashTreeRoot"
    bs = ", ".join(f"b{i}" for i in range(w))
    lines = []
    for i, step in enumerate(steps):
        lines.append(f"    step with {step} as ⟨ a{i}, h{i} ⟩")
        lines.append(f"    step as ⟨ row{i + 1}, hrow{i + 1} ⟩")
        lines.append(f"    have hl{i + 1} : row{i + 1}.length = {w} := by")
        prev = "hlen" if i == 0 else f"hl{i}"
        lines.append(f"      rw [hrow{i + 1}]; simp only [Slice.length, Slice.set_val_eq, "
                     f"List.length_set]; exact {prev}")
    for j in range(k, w):
        lines.append(f"    step as ⟨ row{j + 1}, hrow{j + 1} ⟩")
        lines.append(f"    have hl{j + 1} : row{j + 1}.length = {w} := by")
        lines.append(f"      rw [hrow{j + 1}]; simp only [Slice.length, Slice.set_val_eq, "
                     f"List.length_set]; exact hl{j}")
    elems = ", ".join([f"a{i}" for i in range(k)] + ["zeroNode"] * (w - k))
    roots = ", ".join(f"a{i}" for i in range(k))
    xs = ", ".join(f"bytes a{i}.val" for i in range(k))
    hs = ", ".join(f"h{i}" for i in range(k))
    rewrites = ", ".join(f"hrow{i}" for i in range(w, 0, -1))
    unf_alias = ("    simp only [" + ",\n      ".join(alias) + "]\n") if alias else ""
    unf_val = " ".join([value] + list(helpers))
    padding = ""
    if w > k:
        padding = f", padded with {w - k} zero root" + ("s" if w - k > 1 else "")
    return f'''include hl in
/-- **The rows of `{name}`**{doc}: the roots of its {k} fields{padding}, the bottom level
of its tree. -/
theorem {name}.rows :
    Rows inst h {inst} (.container {names} {fields}) {value}
      (fun x => {good}) {d} where
  small := by omega
  width := ⟨ {w}#usize, rfl, rfl ⟩
  row x row hgood hlen := by
{("    simp only [" + inst + "]" + chr(10)) if reduce else ""}    unfold {inst}.hash_tree_root_row
{unf_alias}{("    " + naming + chr(10)) if naming else ""}    have hlen' : row.val.length = {w} := hlen
    obtain ⟨ {bs}, hrowv ⟩ := list_len{w} row.val hlen'
{chr(10).join(lines)}
    have hrv : row{w}.val = [{elems}] := by
      rw [{rewrites}]
      simp only [Slice.set_val_eq, hrowv]
      rfl
    refine ⟨ by simp [Slice.length, hrv], ?_ ⟩
    unfold RowRoot {unf_val}
    rw [hashTreeRoot_container _ _ _ [{xs}] rfl
      (by simp only [{fields}] at *; simp [{hs}, Pure.pure, Except.pure, Bind.bind, Except.bind])]
    rw [hrv]
    exact container_row_root [{roots}] {d} (by simp [depthFor])
'''


if __name__ == "__main__":
    import sys

    print(row("Example", "libssz_types.verif_example.Example", "exNames", "exFields", "exV",
              ["U64.hash_tree_root.spec inst h x.a", "U64.hash_tree_root.spec inst h x.b",
               "U64.hash_tree_root.spec inst h x.c"]), file=sys.stdout)
