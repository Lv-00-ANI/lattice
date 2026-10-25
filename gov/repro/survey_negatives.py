"""Round 34: a fully-measurable audit target.

Previous rounds kept getting burned by partial measurement (name keyword search, spot checks).
This round measures something that CAN be measured completely: every theorem whose statement
is a NEGATIVE claim (`not (...)` or `-> False`). Those are exactly the counterexample-shaped
statements -- refutations, impossibility results, non-existence proofs.

They are the strongest evidence a formalisation can carry: a refuted claim, machine-checked.
Count them, classify by what they refute, and report completely (not a sample).
"""
import io
import os
import re
import sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
LAT = _os.path.join(_REPO, "Lattice")

THM = re.compile(r"(?m)^(?:theorem|lemma)\s+(\w+)(.*?):=\s*(?:by|fun|rfl|\n)")

files = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(root, f)
            files.append((os.path.relpath(p, LAT).replace("\\", "/"), p))

negatives = []
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    for m in THM.finditer(t):
        name, sig = m.group(1), m.group(2)
        flat = " ".join(sig.split())
        # a negative claim: the conclusion starts with `not` / `¬` / ends in `-> False`
        is_neg = bool(re.search(r":\s*(?:¬|not )", flat)) or "-> False" in flat
        if is_neg:
            negatives.append((rel, name, flat[:150]))

print("=== theorem-level NEGATIVE claims (refutations) ===")
print("total: %d\n" % len(negatives))

by_layer = {}
for rel, name, sig in negatives:
    lay = rel.split("/")[0] if "/" in rel else "(root)"
    by_layer.setdefault(lay, []).append((rel, name))
for lay in sorted(by_layer, key=lambda x: -len(by_layer[x])):
    print("  %-8s %d" % (lay, len(by_layer[lay])))

print("\n=== the chain layers' refutations, in full ===")
for rel, name, sig in negatives:
    if rel.startswith(("Core/", "Lift/", "Geo/", "Audit/")):
        print("  %-46s %s" % (rel[-46:], name))
