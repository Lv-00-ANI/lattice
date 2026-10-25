"""Macro picture: how much of the four-rung goal does the tree actually cover?

Not a quality judgement -- a coverage measurement per rung, so the next plan targets the
thinnest part rather than the most familiar part.
"""
import io
import os
import re
import sys
from collections import Counter
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
LAT = _os.path.join(_REPO, "Lattice")

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(theorem|lemma|def|structure|abbrev|inductive)[ \t]+"
                  r"([A-Za-z0-9_'!?]+)")


def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if not depth and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if not depth:
            out.append(src[i])
        i += 1
    return "".join(out)


# per-file counts
rows = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, LAT).replace("\\", "/")
        t = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
        kinds = Counter(m.group(1) for m in DECL.finditer(t))
        rows.append((rel, kinds))

by_layer = {}
for rel, kinds in rows:
    layer = rel.split("/")[0] if "/" in rel else "(root)"
    d = by_layer.setdefault(layer, Counter())
    for k, v in kinds.items():
        d[k] += v

print("%-14s %-8s %-8s %-8s %-8s" % ("layer", "theorem", "lemma", "def", "total"))
print("-" * 52)
for layer in sorted(by_layer, key=lambda x: -sum(by_layer[x].values())):
    d = by_layer[layer]
    tot = sum(d.values())
    print("%-14s %-8d %-8d %-8d %-8d" % (layer, d.get("theorem", 0), d.get("lemma", 0),
                                          d.get("def", 0), tot))

# the rung-relevant modules
RUNG_KEYWORDS = {
    "L0 data <-> L1 token": ["Token", "Detok", "Char", "Bytes"],
    "L1 token <-> L2 symbol": ["Pipeline", "Decode", "Payload", "Symbol"],
    "L2 symbol <-> L3 weight": ["Compiler", "Compile", "Weight", "Extract", "Penalty"],
    "verification loop": ["Verif", "Sampled", "Bound", "Lipschitz"],
}
print("\nrung-relevant modules (by filename substring):")
for rung, kws in RUNG_KEYWORDS.items():
    hits = [rel for rel, _ in rows if any(k.lower() in rel.lower() for k in kws)]
    print("  %-26s %d modules" % (rung, len(hits)))
    for h in sorted(hits)[:6]:
        print("       " + h)
