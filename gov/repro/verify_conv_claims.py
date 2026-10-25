"""Verify the two claims I just wrote into CONVENTIONS §7.

1. "most of the 36 camelCase theorems are regex false positives -- type aliases"
2. "all 10 oversized files are in Lib; none in Core/Lift/Geo"

Both were asserted from spot-checking a few entries. Check them properly, because writing an
unverified claim into a document about verification would be the worst possible place for it.
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

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+|partial[ \t]+)*(theorem|lemma|def|structure|abbrev|"
                  r"inductive|class|instance)[ \t]+([A-Za-z0-9_'!?]+)")

files = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(root, f)
            files.append((os.path.relpath(p, LAT).replace("\\", "/"), p))

# --- claim 1: are camelCase theorems aliases? ---
print("=== the 36 camelCase theorems, with their BODY kind ===")
alias = 0
real = 0
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    lines = t.split("\n")
    for m in DECL.finditer(t):
        kind, name = m.group(1), m.group(2)
        if kind not in ("theorem", "lemma"):
            continue
        if "_" in name or not re.search(r"[a-z][A-Z]", name):
            continue
        line_no = t[:m.start()].count("\n")
        body = " ".join(lines[line_no:line_no + 4])
        is_alias = re.search(r":=\s*[A-Z][A-Za-z0-9_.]*\s*$|:=\s*[A-Z]\w*(\s+\w+)*\s*$",
                             body) is not None
        tag = "ALIAS" if is_alias else "REAL "
        if is_alias:
            alias += 1
        else:
            real += 1
        print("  %-6s %-46s %s" % (tag, rel[-46:], name))

print("\n  alias-like: %d   real look: %d   total: %d" % (alias, real, alias + real))

# --- claim 2: oversized files by layer ---
print("\n=== oversized files ( > 60 decls ) by layer ===")
LAYERS = ("Core", "Lift", "Geo", "Lib", "Audit")
by_layer = {l: 0 for l in LAYERS}
by_layer["(root)"] = 0
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    n = sum(1 for _ in DECL.finditer(t))
    if n <= 60:
        continue
    head = rel.split("/")[0] if "/" in rel else "(root)"
    by_layer[head] = by_layer.get(head, 0) + 1
for k, v in sorted(by_layer.items()):
    print("  %-8s %d" % (k, v))
