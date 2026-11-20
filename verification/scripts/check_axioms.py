"""Checks the output of `lake env lean Axioms.lean` (read from stdin).

Fails unless Lean printed no error and every `#print axioms` in Axioms.lean reported only
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`): in particular no
`sorryAx` and no `axiom` of the model.

Usage: lake env lean Axioms.lean 2>&1 | python3 -I ../scripts/check_axioms.py Axioms.lean
"""
import re
import sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}

expected = len(re.findall(r"^#print axioms ", open(sys.argv[1]).read(), re.M))
out = sys.stdin.read()

errors = [l for l in out.splitlines() if "error" in l.lower()]
# `#print axioms` output may wrap the list over several lines.
reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                     out)
bad = []
for name, axioms in reports:
    used = {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()}
    if used - STANDARD:
        bad.append(f"{name}: {', '.join(sorted(used - STANDARD))}")

ok = not errors and not bad and len(reports) == expected
for l in errors:
    print("error:", l)
for b in bad:
    print("non-standard axioms:", b)
if len(reports) != expected:
    print(f"expected {expected} axiom reports, got {len(reports)}")
print(f"{len(reports)} theorems, {'only standard axioms' if ok else 'CHECK FAILED'}")
sys.exit(0 if ok else 1)
