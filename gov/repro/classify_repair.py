"""Classify the "repair/fix" declarations in Lib by MEANING, not by name.

Last round's lesson: a keyword screen is not a measurement. So this reads each file's
heading and the shape of its declarations:

  A. implements a `Repair` instance  -- `: Repair ... where` or similar
  B. operates on a `Repair` (theorems taking one as a parameter)
  C. mentions "fix"/"fixed" in an unrelated sense (fixed point of a function, fixed mask,
     fixed-width, ...) -- these are the字面命中 that inflate the count

Then report how many of the 278 "repair/fix" declarations fall in each class.
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
                  r"noncomputable[ \t]+)*(theorem|lemma|def|structure|abbrev|inductive)[ \t]+"
                  r"([A-Za-z0-9_'!?]+)")


def heading(t):
    m = re.search(r"(?m)^#\s+(.+)$", t)
    return m.group(1).strip()[:70] if m else ""


files = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, LAT).replace("\\", "/")
        t = io.open(p, "rb").read().decode("utf-8", errors="replace")
        files.append((rel, t))

# --- A: files that DEFINE a Repair instance (a `where` block typed `Repair`)
defines = []
# --- B: files that take a `Repair` as a parameter
uses = []
# --- C: files with fix-named declarations but no Repair mention
mentions_only = []

for rel, t in files:
    has_repair_def = re.search(r":\s*(?:Lattice\.Core\.)?Repair\b[^\n]*\bwhere\b", t) is not None
    mentions = re.search(r"\bRepair\b", t) is not None
    fix_names = [m.group(2) for m in DECL.finditer(t)
                 if re.search(r"fix|Fix|repair|Repair", m.group(2))]
    if has_repair_def:
        defines.append((rel, len(fix_names), heading(t)))
    elif mentions and fix_names:
        uses.append((rel, len(fix_names), heading(t)))
    elif fix_names:
        mentions_only.append((rel, len(fix_names), heading(t)))

def show(title, rows):
    print("\n=== %s: %d files, %d fix-named declarations ===" %
          (title, len(rows), sum(r[1] for r in rows)))
    for rel, n, h in sorted(rows, key=lambda r: -r[1])[:14]:
        print("  %-46s %-4d %s" % (rel, n, h))

show("A. DEFINES a Repair instance", defines)
show("B. mentions Repair + has fix-named declarations", uses)
show("C. fix-named declarations but NO Repair mention (字面命中)", mentions_only)
