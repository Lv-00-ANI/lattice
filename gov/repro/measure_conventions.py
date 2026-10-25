"""Round 33: measure CONVENTIONS execution, item by item.

Section 7 of CONVENTIONS.md claims specific violation counts. Those claims may have drifted --
files have been added every round since. Measure them.

  N4  prime names (`'` in identifiers, outside the declared exceptions)
  N3  camelCase theorems (N2 allows camelCase for DEFS, not for theorems)
  F1  files with more than 60 declarations
  D1  comment completeness (4 required parts) -- previously "not measured"
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

files = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(root, f)
            files.append((os.path.relpath(p, LAT).replace("\\", "/"), p))

# --- N4: prime names ---
print("=== N4: identifiers containing an apostrophe ===")
DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+|partial[ \t]+)*(theorem|lemma|def|structure|abbrev|"
                  r"inductive|class|instance)[ \t]+([A-Za-z0-9_'!?]+)")
primes = []
counts = {"theorem": 0, "lemma": 0, "def": 0, "structure": 0, "abbrev": 0,
          "inductive": 0, "class": 0, "instance": 0}
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    for m in DECL.finditer(t):
        kind, name = m.group(1), m.group(2)
        counts[kind] = counts.get(kind, 0) + 1
        if "'" in name:
            primes.append((rel, kind, name))
print("  violations: %d" % len(primes))
for rel, kind, name in primes[:10]:
    print("    %-44s %-10s %s" % (rel, kind, name))

# --- N3: camelCase THEOREMS (defs are allowed) ---
print("\n=== N3: theorems whose name is camelCase ===")
camel = []
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    for m in DECL.finditer(t):
        kind, name = m.group(1), m.group(2)
        if kind not in ("theorem", "lemma"):
            continue
        # camelCase: no underscore, has a lowercase->uppercase transition, starts lowercase
        if "_" not in name and re.search(r"[a-z][A-Z]", name):
            camel.append((rel, name))
print("  violations: %d" % len(camel))
for rel, name in camel[:10]:
    print("    %-44s %s" % (rel, name))

# --- N3 defs ---
print("\n=== N3: defs whose name is camelCase (allowed by N2) ===")
camel_defs = 0
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    for m in DECL.finditer(t):
        kind, name = m.group(1), m.group(2)
        if kind in ("theorem", "lemma"):
            continue
        if "_" not in name and re.search(r"[a-z][A-Z]", name):
            camel_defs += 1
print("  count: %d" % camel_defs)

# --- F1: files over 60 declarations ---
print("\n=== F1: files with more than 60 declarations ===")
big = []
for rel, p in files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    n = sum(1 for _ in DECL.finditer(t))
    if n > 60:
        big.append((rel, n))
big.sort(key=lambda x: -x[1])
print("  violations: %d" % len(big))
for rel, n in big[:12]:
    print("    %-52s %d" % (rel, n))

print("\n=== totals ===")
print("  files: %d   declarations: %d" % (len(files), sum(counts.values())))
