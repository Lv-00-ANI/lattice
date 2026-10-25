"""Inject a real I3 defect and see whether the gate reports I3.

The audit reported that injecting a duplicate `abbrev` produced only I7, leaving I3
silent. That matters because I3 is the invariant the migration narrative leans on
("12 duplicate definitions found and fixed"): if I3 cannot fire, there is no regression
guard on that claim.

Method: pick a module that is already compiled (so I7 stays quiet) and append a duplicate
declaration to it, run the gate, then restore the file byte-for-byte.
"""
import hashlib
import io
import os
import subprocess
import sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = _REPO
GOV = os.path.join(NEW, "gov")
GATE = os.path.join(GOV, "gate.py")

CASES = [
    ("duplicate abbrev (same qualified name)",
     "Lattice/Core/Simulation.lean",
     "\nabbrev Star {S L : Type*} (R : S → L → S → Prop) (s : S) (l : L) (t : S) : Prop :=\n"
     "  Relation.ReflTransGen (fun a b => R a l b) s t\n"),
    ("duplicate semantic concept (eval)",
     "Lattice/Core/Semantics.lean",
     "\ndef eval (x : Nat) : Nat := x\n"),
]


def run_gate():
    r = subprocess.run([sys.executable, GATE, "--quiet"], cwd=GOV, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


for name, rel, snippet in CASES:
    p = os.path.join(NEW, *rel.split("/"))
    orig = io.open(p, "rb").read()
    digest = hashlib.sha256(orig).hexdigest()
    try:
        io.open(p, "wb").write(orig + snippet.encode("utf-8"))
        code, out = run_gate()
        # which invariants are reported?
        fired = [ln.split()[0] for ln in out.splitlines()
                 if ln.strip().startswith("I") and "finding" in ln]
        print("%-42s exit=%-2d fired=%s" % (name, code, fired or "none"))
        for ln in out.splitlines():
            if "finding" in ln:
                print("      ", ln.strip()[:90])
    finally:
        io.open(p, "wb").write(orig)
        assert hashlib.sha256(io.open(p, "rb").read()).hexdigest() == digest, "restore failed"
print("\nrestored all files (sha256 verified)")
code, _ = run_gate()
print("gate exit after restore:", code)
