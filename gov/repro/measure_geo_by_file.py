"""The keyword-name survey that produced ROADMAP-v4 §0 was methodologically wrong.

It searched DECLARATION NAMES for words like "synth". But `Geo/Synthesis.lean`'s key theorems
are named `samples_sound`, `synthesize_perpendicular_samples` -- and the FILE name carries the
topic, not the declaration names. Worse, `Geo/Initialise.lean` and `Geo/Invariant.lean` are
exactly the "structured initialisation" and "data synthesis" paths, and both were missed.

This script measures by FILE, reading each Geo file's own header to see what it claims to do.
That is the honest way: the module docstring states the intent, and the declarations below it
are the evidence.
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
LAT = _os.path.join(_REPO, "Lattice", "Geo")

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(theorem|lemma|def|structure|abbrev|inductive)[ \t]+"
                  r"([A-Za-z0-9_'!?]+)")

print("%-24s %-6s %-6s %s" % ("file", "thms", "defs", "first heading line"))
print("-" * 100)
rows = []
for f in sorted(os.listdir(LAT)):
    if not f.endswith(".lean"):
        continue
    p = os.path.join(LAT, f)
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    thms = len(re.findall(r"(?m)^[ \t]*(?:noncomputable[ \t]+|private[ \t]+)?(?:theorem|lemma)[ \t]", t))
    defs = len(re.findall(r"(?m)^[ \t]*(?:noncomputable[ \t]+|private[ \t]+)?(?:def|structure|abbrev|inductive)[ \t]", t))
    # first markdown heading inside the module docstring
    m = re.search(r"(?m)^#\s+(.+)$", t)
    head = m.group(1).strip()[:60] if m else "(no heading)"
    rows.append((f, thms, defs, head))

for f, thms, defs, head in rows:
    print("%-24s %-6d %-6d %s" % (f, thms, defs, head))

# The three files the keyword survey missed
print("\n=== files the keyword survey MISSED as chain-relevant ===")
for name, label in (("Synthesis.lean", "data synthesis"),
                    ("Initialise.lean", "structured initialisation"),
                    ("Invariant.lean", "invariance laws that synthesis needs")):
    p = os.path.join(LAT, name)
    if not os.path.exists(p):
        print("  %-20s MISSING" % name)
        continue
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    names = [m.group(2) for m in DECL.finditer(t)]
    print("  %-20s (%s): %d declarations" % (name, label, len(names)))
    for n in names[:8]:
        print("       " + n)
