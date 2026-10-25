"""Two bugs in the census build:

1. `layer()` reads `rel.split("/")[0]` but `rel` was already TRUNCATED by the dump format
   (`%-46s` of `rel[-46:]`), so paths lost their prefix. Fix: dump the FULL relative path.
2. The family classifier puts 122 into "other", which is too coarse to be useful.

Rewrite the extractor to emit full paths, then rebuild.
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
# intermediate artefacts this pipeline writes live beside the script, not outside the repo
_WORK = _os.path.join(_HERE, "_work")
_os.makedirs(_WORK, exist_ok=True)


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
LAT = r"C:\Users\xingg\Desktop\agent\lattice-new\Lattice"

files = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(root, f)
            files.append((os.path.relpath(p, LAT).replace("\\", "/"), p))

PAT = re.compile(r"^(?:theorem|lemma)\s+(\w+)(.*?):=", re.S | re.M)


def concl_of(stmt):
    s = stmt.lstrip(": ").strip()
    depth = 0
    last = -1
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            last = i
    return s[last + 1:].strip() if last >= 0 else s


records = []
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    for m in PAT.finditer(t):
        name, sig = m.group(1), m.group(2)
        flat = " ".join(sig.split())
        c = concl_of(flat)
        # `¬ ∃ ...` counts; a bare `∃ ...` does NOT.
        # The old `[¬\s]*` allowed ZERO negations, sweeping in 109 positive existence
        # theorems: Taylor points, characterisations, confluence witnesses. None refute.
        neg = (c.startswith("¬") or c.startswith("not ") or c.endswith("False")
               or re.match(r"^\s*¬\s*(∃|exists)", c) is not None)
        if neg:
            records.append((rel, name, c))

with io.open(_os.path.join(_WORK, "neg_full.txt"), "w",
             encoding="utf-8", newline="\n") as fh:
    for rel, name, c in records:
        fh.write("%s\t%s\t%s\n" % (rel, name, c.replace("\n", " ")))

print("records: %d" % len(records))
from collections import Counter
lay = Counter(r[0].split("/")[0] if "/" in r[0] else "(root)" for r in records)
print("by layer (full paths):")
for l, n in lay.most_common():
    print("  %-10s %d" % (l, n))
