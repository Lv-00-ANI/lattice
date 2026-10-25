"""Do the 102 architecture/attention files connect to the four-rung chain at all?

STATE-2026-10 claimed they do not serve the chain. That is a strong claim about 102 files;
measure it instead of asserting it.

Three tests per file:
  1. does it import anything from Core / Lift / Geo (the chain layers)?
  2. does anything in Core / Lift / Geo import it (chain consuming the architecture)?
  3. does it mention the chain's vocabulary (LinearForm, Constraint, Penalty, poly, sqDist)?
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
NEW = _REPO
LAT = os.path.join(NEW, "Lattice")
SECTIONS = ["Architectures", "Attention"]

CHAIN_PREFIX = ("Lattice.Core", "Lattice.Lift", "Lattice.Geo")
CHAIN_WORDS = ["LinearForm", "Constraint", "Penalty", "poly", "sqDist", "EqConstraint",
               "Point", "tokenize", "decodePayload", "Ladder"]

arch_files = []
for sec in SECTIONS:
    d = os.path.join(LAT, "Lib", sec)
    for root, _, fs in os.walk(d):
        for f in fs:
            if f.endswith(".lean"):
                arch_files.append(os.path.join(root, f))

print("architecture/attention files: %d" % len(arch_files))

imports_chain = []
mentions = []
for p in arch_files:
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    imps = re.findall(r"(?m)^import\s+(Lattice\.\S+)$", t)
    if any(i.startswith(CHAIN_PREFIX) for i in imps):
        imports_chain.append((os.path.relpath(p, LAT), [i for i in imps if i.startswith(CHAIN_PREFIX)]))
    if any(w in t for w in CHAIN_WORDS):
        hits = [w for w in CHAIN_WORDS if w in t]
        mentions.append((os.path.relpath(p, LAT), hits))

print("\nimporting a chain-layer module: %d" % len(imports_chain))
for rel, mods in imports_chain[:12]:
    print("  %-52s %s" % (rel, mods[:2]))

print("\nmentioning chain vocabulary: %d" % len(mentions))
for rel, hits in mentions[:12]:
    print("  %-52s %s" % (rel, hits[:4]))

# reverse: who in the chain imports an architecture module?
print("\nchain files importing an architecture module:")
n = 0
for root, _, fs in os.walk(LAT):
    rel_root = os.path.relpath(root, LAT).replace("\\", "/")
    if rel_root.startswith("Lib/Architectures") or rel_root.startswith("Lib/Attention"):
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        t = io.open(p, "rb").read().decode("utf-8", errors="replace")
        for m in re.finditer(r"(?m)^import\s+(Lattice\.Lib\.(?:Architectures|Attention)\.\S+)$", t):
            print("  %-52s -> %s" % (os.path.relpath(p, LAT), m.group(1)))
            n += 1
print("  total: %d" % n)
