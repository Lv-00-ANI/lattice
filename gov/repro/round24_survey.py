"""Round 24: what does the Lift layer actually contain, file by file?

Lift is the layer where "symbol <-> weight" lives -- the project's stated only real difficulty.
Previous surveys counted declarations or searched names; this reads each file's heading.

Also checks the specific question the remaining slots raise: is there any abstraction over
ENCODINGS (as opposed to instances of them)?
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
LAT = _os.path.join(_REPO, "Lattice", "Lift")

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(theorem|lemma|def|structure|abbrev|inductive|class)[ \t]+"
                  r"([A-Za-z0-9_'!?]+)")

print("%-34s %-5s %-5s %s" % ("file", "thm", "def", "heading"))
print("-" * 108)
rows = []
for f in sorted(os.listdir(LAT)):
    if not f.endswith(".lean"):
        continue
    p = os.path.join(LAT, f)
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    thms = len(re.findall(r"(?m)^[ \t]*(?:noncomputable[ \t]+)?(?:theorem|lemma)[ \t]", t))
    defs = len(re.findall(r"(?m)^[ \t]*(?:noncomputable[ \t]+)?"
                          r"(?:def|structure|abbrev|inductive|class)[ \t]", t))
    m = re.search(r"(?m)^#\s+(.+)$", t)
    head = m.group(1).strip()[:60] if m else "(no heading)"
    rows.append((f, thms, defs, head, t))
    print("%-34s %-5d %-5d %s" % (f, thms, defs, head))

print("\ntotals: %d files, %d theorems, %d defs"
      % (len(rows), sum(r[1] for r in rows), sum(r[2] for r in rows)))

# Does anything abstract over encodings?
print("\n=== does any structure/class abstract over ENCODINGS? ===")
for f, thms, defs, head, t in rows:
    for m in DECL.finditer(t):
        if m.group(1) in ("structure", "class"):
            name = m.group(2)
            if re.search(r"Encode|Encoding|Backend|Codec|Translation", name):
                print("  %-30s %s %s" % (f, m.group(1), name))

# Which files mention `encode` at all
print("\n=== files defining or using `encode` ===")
for f, thms, defs, head, t in rows:
    if re.search(r"\bencode\b", t):
        n = len(re.findall(r"\bencode\b", t))
        print("  %-34s %d mention(s)" % (f, n))
