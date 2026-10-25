"""Find the 3 new files that define a Repair instance, so REPAIR-CENSUS can be corrected.

The doc says 6 (A-class); the tree has 9. The extras were added in rounds 22-37 and the census
was never re-measured -- exactly the drift pattern CONVENTIONS §7 records.
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

DOC_A = {  # the 6 the census lists
    "Geo/Loop.lean", "Geo/LoopPerp.lean", "Geo/ConjRepair.lean", "Core/Repair.lean",
    "Lib/Linear/Residual.lean", "Lib/Linear/Multivar.lean",
}

found = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, LAT).replace("\\", "/")
        t = io.open(p, "rb").read().decode("utf-8", errors="replace")
        if re.search(r":\s*(?:Lattice\.Core\.)?Repair\b[^\n]*\bwhere\b", t):
            found.append(rel)

print("files defining a Repair instance: %d" % len(found))
print("\nin the census already:")
for r in sorted(set(found) & DOC_A):
    print("  %s" % r)
print("\nNOT in the census (new since it was written):")
for r in sorted(set(found) - DOC_A):
    print("  %s" % r)
    p = os.path.join(*([LAT] + r.split("/")))
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    # what does it define?
    for m in re.finditer(r"(?m)^(?:noncomputable\s+)?def\s+(\w+)[^\n]*:\s*(?:Lattice\.Core\.)?Repair", t):
        print("       defines %s" % m.group(1))
