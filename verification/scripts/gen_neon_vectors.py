"""Generates the vectors for the differential test of the AArch64 kernel.

Usage: python3 -I scripts/gen_neon_vectors.py   (from verification/, after running
     `lake build difftest-merkle-neon` in lean/)

The test in `difftest-merkle/tests/neon.rs` runs on an AArch64 machine and compares the
processor with the Lean models. That machine does not need Lean: this script runs the
`difftest-merkle-neon` executable here (the intrinsic models of
`Libssz/MerkleNeon/Intrinsics.lean` and the Aeneas model of `neon.rs`) on random and edge
inputs, and saves each input with Lean's answer:

* `difftest-merkle/vectors/neon-intrinsics.txt`: one line per intrinsic call, `INPUT<tab>LEAN`;
* `difftest-merkle/vectors/neon-kernel.txt`: pairs, double pairs, quadruple pairs and layers.

Before saving, the script checks the kernel cases with `hashlib`: the Aeneas model must give
the SHA-256 of each pair (and EthLib's `combine`, which the executable also returns). If
anything does not match, it fails and writes nothing. The inputs are deterministic: running it
twice gives the same files.
"""
import hashlib
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean", ".lake", "build", "bin", "difftest-merkle-neon")
OUTPUT = os.path.join(ROOT, "difftest-merkle", "vectors")
M64 = (1 << 64) - 1


class Rng:
    """xorshift64, the same one the Rust tests use."""

    def __init__(self, seed):
        self.s = seed

    def next(self):
        s = self.s
        s ^= (s << 13) & M64
        s ^= s >> 7
        s ^= (s << 17) & M64
        self.s = s
        return s

    def bytes(self, n):
        out = b""
        while len(out) < n:
            out += self.next().to_bytes(8, "little")
        return out[:n]


def hx(b):
    return b.hex()


def vectors(r, random):
    """Edge vectors (all zeros, all ones, a single bit, distinct lanes) and random ones."""
    out = [bytes(16), b"\xff" * 16, b"\x80" * 16, b"\x7f" * 16, bytes(range(1, 17))]
    for at in range(16):
        for bit in (0x01, 0x80):
            v = bytearray(16)
            v[at] = bit
            out.append(bytes(v))
    out += [r.bytes(16) for _ in range(random)]
    return out


def edge_nodes():
    out = [bytes(32), b"\xff" * 32, b"\x80" * 32, b"\x7f" * 32]
    for at in range(32):
        n = bytearray(32)
        n[at] = 0x80
        out.append(bytes(n))
        n[at] = 0x01
        out.append(bytes(n))
        n = bytearray(b"\xff" * 32)
        n[at] = 0
        out.append(bytes(n))
    return out


def sha_pair(a, b):
    return hashlib.sha256(a + b).digest()


def lean(lines):
    if not os.path.exists(LEAN):
        sys.exit(f"{LEAN} not found: run `lake build difftest-merkle-neon` in lean/")
    p = subprocess.run([LEAN], input="\n".join(lines) + "\n", capture_output=True, text=True,
                       check=True)
    got = p.stdout.splitlines()
    assert len(got) == len(lines), "the Lean executable did not answer every case"
    bad = [l for l, g in zip(lines, got) if g in ("BAD_INPUT", "DIV")]
    assert not bad, f"invalid answers from Lean, for example {bad[0][:80]}"
    return got


def intrinsics():
    r = Rng(0x5eed_1234_abcd_ef01)
    vs = vectors(r, 150)
    n = len(vs)
    lines = []
    for i, a in enumerate(vs):
        k = vs[(5 * i + 11) % n]
        for b in (vs[(i + 1) % n], vs[(7 * i + 3) % n], a):
            c = vs[(3 * i + 2) % n]
            lines += [f"add {hx(a)} {hx(b)}", f"su0 {hx(a)} {hx(b)}",
                      f"su1 {hx(a)} {hx(b)} {hx(c)}", f"h {hx(a)} {hx(b)} {hx(k)}",
                      f"h2 {hx(a)} {hx(b)} {hx(k)}"]
    words = [0, 1, 0x7fff_ffff, 0x8000_0000, 0xffff_ffff, 0x0102_0304]
    words += [r.next() & 0xffff_ffff for _ in range(120)]
    for w in words:
        lines.append(f"dup {w:08x}")
    for i, v in enumerate(vs[:120]):
        for lane in range(4):
            lines.append(f"get {lane} {hx(v)}")
            lines.append(f"set {lane} {words[(3 * i + lane) % len(words)]:08x} {hx(v)}")
    return lines, lean(lines)


def kernel():
    r = Rng(0x0dd_ba11_cafe_f00d)
    nodes = edge_nodes() + [r.bytes(32) for _ in range(200)]
    n = len(nodes)
    lines, want = [], []
    for i, a in enumerate(nodes):
        for b in (nodes[(i + 1) % n], nodes[(7 * i + 5) % n], a):
            lines.append(f"pair {hx(a)} {hx(b)}")
            want.append(f"{hx(sha_pair(a, b))}\t{hx(sha_pair(a, b))}")
    for i in range(n):
        q = [nodes[i], nodes[(3 * i + 1) % n], nodes[(5 * i + 2) % n], nodes[(11 * i + 7) % n]]
        lines.append("pairs2 " + " ".join(hx(x) for x in q))
        want.append(f"{hx(sha_pair(q[0], q[1]))},{hx(sha_pair(q[2], q[3]))}")
    for i in range(n):
        o = [nodes[(13 * i + 7 * j + j * j) % n] for j in range(8)]
        lines.append("pairs4 " + " ".join(hx(x) for x in o))
        want.append(",".join(hx(sha_pair(o[2 * j], o[2 * j + 1])) for j in range(4)))
    zero = r.bytes(32)

    def parents(below):
        return [sha_pair(below[k], below[k + 1] if k + 1 < len(below) else zero)
                for k in range(0, len(below), 2)]

    def cat(ns):
        return "".join(hx(x) for x in ns) or "-"

    for length in list(range(22)) + [31, 32, 33, 64, 65]:
        below = [r.bytes(32) for _ in range(length)]
        p = (length + 1) // 2
        sizes = [p, p + 1, p + 3] + ([p - 1, 0] if p > 0 else [])
        for size in sizes:
            level = [b"\xaa" * 32] * size
            lines.append(f"layer 0 {hx(zero)} {cat(below)} {cat(level)}")
            want.append("PANIC" if size < p else cat(parents(below) + level[p:]))
        for other in ([], [b"\x55" * 32] * 3):
            lines.append(f"layer 1 {hx(zero)} {cat(other)} {cat(below)}")
            want.append(cat(parents(below) + below[p:]))
    got = lean(lines)
    bad = [(l, w, g) for l, w, g in zip(lines, want, got) if w != g]
    for l, w, g in bad[:5]:
        print(f"LEAN ≠ hashlib  {l[:60]}…\n    hashlib: {w[:70]}\n    Lean:    {g[:70]}")
    assert not bad, f"{len(bad)} kernel cases where the Aeneas model does not give SHA-256"
    return lines, got


def save(name, lines, got):
    os.makedirs(OUTPUT, exist_ok=True)
    with open(os.path.join(OUTPUT, name), "w") as f:
        for l, g in zip(lines, got):
            f.write(f"{l}\t{g}\n")
    print(f"{name}: {len(lines)} cases")


def main():
    li, gi = intrinsics()
    lk, gk = kernel()
    save("neon-intrinsics.txt", li, gi)
    save("neon-kernel.txt", lk, gk)
    print("the Aeneas model of the kernel gives SHA-256 (hashlib) and EthLib's combine in "
          f"all {len(lk)} kernel cases")


if __name__ == "__main__":
    main()
