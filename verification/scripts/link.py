"""Linking between extractions: what one Aeneas extraction uses from another crate is replaced
by the declaration with the same Rust path in that crate's extraction.

Used by `complete_externals_merkle.py` (the tree, linked with the codec) and
`complete_externals_types.py` (`ssz-types`, linked with the tree and the codec).

Charon does not translate the bodies of other crates. Aeneas leaves their functions as holes,
and writes **partial copies** of their traits and types: a trait only has the methods the code
of this extraction names. Those copies cannot be used with the proofs of the other
extraction, which are about its complete trait, and cannot be passed to a function of the
other extraction that expects the trait.

Each declaration from another crate is replaced by the one with **the same Rust path** in the
other extraction. The path is the one Aeneas writes in the doc comment of each declaration.

* A trait or a type (a `structure`, an `inductive`, or an opaque type that Aeneas leaves as
  `axiom … : Type`) is removed, and the code of this extraction names the other one directly
  (and, for an `inductive`, its constructors). An `abbrev` does not work: `impl_def`, the
  Aeneas macro for trait implementations, needs to see the structure.
* A function, an implementation or a hole becomes an alias (`abbrev`) with its signature from
  here. Arguments are passed by name: a binder from here goes to the binder with the same name
  in the target, explicit or implicit there.
* A hole that the other extraction already defines at the root with the same name (the
  standard-library models) is removed: defining it twice clashes when both are imported.
* A trait implementation that Aeneas did translate here (a `{ … }` with the methods, which are
  linked holes) and that the other extraction does not have as a value is left as is.

Lean checks that each alias has the type the code here expects. The assumption is that the
same Rust path names the same declaration in both extractions: they come from the same source
code, compiled separately.
"""
import os
import re

DOC = re.compile(r"^/-- (?:Trait declaration: |Trait implementation: )?\[(.*)\]:?\s*$")
DECL = re.compile(r"^(?:@\[.*\]\s*)?(structure|def|impl_def|abbrev|axiom|inductive)\b\s*(\S*)")


def top_level(s, target):
    """The first position of `target` in `s` outside parentheses, braces and brackets."""
    depth = 0
    for i in range(len(s)):
        c = s[i]
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
        elif depth == 0 and s.startswith(target, i):
            return i
    return None


def head(kind, decl):
    """The binders of a declaration: what goes between the name and the `:` of the type (or
    the `where` of a structure)."""
    m = DECL.match(decl)
    rest = decl[m.end():]
    if not m.group(2):
        rest = rest.split(None, 1)[1]
    if kind == "structure":
        return rest[:rest.index(" where")]
    end = top_level(rest, ":=")
    rest = rest if end is None else rest[:end]
    return rest[:top_level(rest, ":")]


def binders(kind, decl):
    """The names of the binders of a declaration, in order."""
    return re.findall(r"[({\[](\w+) :", head(kind, decl))


def index(file, prefix):
    """Rust path → (full Lean name, binders), for the declarations of `file`. `prefix` is the
    file's namespace (`""` if they are at the root)."""
    idx = {}
    path = None
    lines = open(file, encoding="utf-8").read().split("\n")
    for k, line in enumerate(lines):
        m = DOC.match(line)
        if m:
            path = m.group(1)
            continue
        if line.startswith("/--"):
            path = None
            continue
        m = DECL.match(line)
        if m and path is not None:
            name = m.group(2) or lines[k + 1].split()[0]
            assert path not in idx, f"repeated path in {file}: {path}"
            end = next((j for j in range(k, len(lines)) if lines[j] == ""), len(lines))
            idx[path] = (prefix + name, binders(m.group(1), "\n".join(lines[k:end])))
            path = None
    return idx


def root_names(file):
    """The names that `file` defines at the root (a FunsExternal without a namespace)."""
    src = open(file, encoding="utf-8").read()
    return set(re.findall(r"^(?:def|abbrev) (\S+)", src, re.M))


def extraction(folder, namespace, origin):
    """The index of an extraction: its Types.lean and Funs.lean (in `namespace`) and its
    FunsExternal.lean (at the root)."""
    idx = {}
    for file, prefix in (("Types.lean", namespace + "."), ("Funs.lean", namespace + "."),
                         ("FunsExternal.lean", "")):
        idx.update(index(os.path.join(folder, file), prefix))
    return (origin, idx)


def parts(block):
    """The doc comment, the kind and the name of the declaration of a block."""
    lines = block.split("\n")
    k = next(i for i, l in enumerate(lines) if DECL.match(l))
    m = DECL.match(lines[k])
    name = m.group(2) or lines[k + 1].split()[0]
    return lines, k, m.group(1), name


def doc_comment(lines, k):
    """The doc comment of a block, without the Aeneas attributes (`rust_fun`, `rust_trait`,
    …), which stay on the original declaration."""
    doc = [l for l in lines[:k] if not l.startswith("@[") and not l.startswith("  \"")]
    while doc and not doc[-1].rstrip().endswith("-/"):
        doc.pop()
    return doc


def alias(block, target, origin):
    """The block of a declaration from another crate, turned into an alias of `target`."""
    lines, k, kind, name = parts(block)
    m = DECL.match(lines[k])
    rest = "\n".join(lines[k:])[m.end():]
    if not m.group(2):
        rest = rest[rest.index(name) + len(name):]
    end = top_level(rest, ":=")
    header = f"abbrev {name}{(rest if end is None else rest[:end]).rstrip()} :="
    own = binders(kind, "\n".join(lines[k:]))
    target_name, target_binders = target
    args = " ".join(f"({b} := {b})" for b in own if b in target_binders)
    note = (f"/- Link: the same Rust declaration as `{target_name}`, from the {origin} "
            f"extraction. -/")
    body = f"_root_.{target_name}" + (f" {args}" if args else "")
    # A default method carries `trait_default`: `impl_def` unfolds it when an implementation
    # refers to itself through it.
    attribute = ["@[trait_default]"] if "trait_default" in "\n".join(lines[:k]) else []
    return "\n".join(doc_comment(lines, k) + [note] + attribute + [header, "  " + body])


def structure(block, target, origin, renames):
    """A structure (trait or type) from another crate: it is removed, and the code here names
    the one in the other extraction directly (`renames`)."""
    lines, k, kind, name = parts(block)
    renames[name] = "_root_." + target[0]
    if kind == "inductive":
        for c in re.findall(r"^\s*\|\s*(\w+)", "\n".join(lines[k:]), re.M):
            renames[f"{name}.{c}"] = f"_root_.{target[0]}.{c}"
    doc = doc_comment(lines, k)
    doc[0] = doc[0].replace("/--", "/-", 1)
    return "\n".join(doc + [f"/- Link: this is `_root_.{target[0]}`, from the {origin} "
                            f"extraction; the code below names it that way. -/"])


def rename(src, renames):
    """Replaces each name in `renames`, as a whole identifier, by its target."""
    for old, new in renames.items():
        src = re.sub(r"(?<![\w.])" + re.escape(old) + r"(?![\w.])", new, src)
    return src


def link_blocks(src, own_prefix, targets, counts, renames=None, at_root=frozenset(),
                linkable=lambda path: True):
    """Links the blocks of `src` that come from another crate (their path does not start with
    `own_prefix`) and for which `linkable(path)` is true.

    `targets` is a list of `(origin, index)`: the first one that has the path is used.
    `renames` collects the removed structures (only in Types.lean). `at_root` are the names
    that another extraction already defines at the root: a hole with one of those names is
    removed."""
    out = []
    for b in src.split("\n\n"):
        lines = b.split("\n")
        path = next((DOC.match(l).group(1) for l in lines if DOC.match(l)), None)
        if path is None or not any(DECL.match(l) for l in lines) or path.startswith(own_prefix):
            out.append(b)
            continue
        _, _, kind, name = parts(b)
        is_type = kind in ("structure", "inductive") or (kind == "axiom" and "@[rust_type" in b)
        if kind == "axiom" and name in at_root:
            out.append(f"-- `{name}`: defined by another extraction, with the same name.")
            counts["already defined"] = counts.get("already defined", 0) + 1
            continue
        if not linkable(path):
            out.append(b)
            continue
        target = next(((o, idx[path]) for o, idx in targets if path in idx), None)
        if target is None and kind in ("def", "impl_def") and "Trait implementation" in b:
            out.append(b)
            counts["translated here"] = counts.get("translated here", 0) + 1
            continue
        if target is None:
            raise SystemExit(f"no extraction has `{path}`")
        origin, decl = target
        if is_type:
            assert renames is not None, f"a structure from another crate outside Types.lean: {path}"
            out.append(structure(b, decl, origin, renames))
        else:
            out.append(alias(b, decl, origin))
        counts[origin] = counts.get(origin, 0) + 1
    return "\n\n".join(out)
