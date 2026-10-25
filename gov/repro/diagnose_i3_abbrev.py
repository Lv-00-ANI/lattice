"""Narrow down why the duplicate-`abbrev` injection did not fire I3.

Two hypotheses:
  H1 the check requires `abbrev` at the start of a line, and my append glued it to the
     previous line (the source file may not end with a newline);
  H2 the check compares only (name) globally and the duplicate landed in the same file,
     which `prev_file != r` treats as "same file -> fine".
"""
import io, os, subprocess, sys
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
P = os.path.join(NEW, "Lattice", "Core", "Simulation.lean")

orig = io.open(P, "rb").read()
print("original ends with newline:", orig.endswith(b"\n"))

SNIP = ("\n\nabbrev Star {S L : Type*} (R : S → L → S → Prop) (s : S) (l : L) (t : S) : Prop :=\n"
        "  Relation.ReflTransGen (fun a b => R a l b) s t\n")


def run():
    r = subprocess.run([sys.executable, GATE, "--quiet"], cwd=GOV, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.returncode, r.stdout


try:
    # H1: append with explicit blank lines separating it
    io.open(P, "wb").write(orig + SNIP.encode("utf-8"))
    code, out = run()
    print("H1 (same file, blank-line separated) exit=%d  I3 fired: %s"
          % (code, "I3" in out and "finding" in out))
    print("   tail of file:")
    for ln in io.open(P, encoding="utf-8").read().splitlines()[-4:]:
        print("     |", ln)
finally:
    io.open(P, "wb").write(orig)

# H2: duplicate across two DIFFERENT files
P2 = os.path.join(NEW, "Lattice", "Core", "Logic.lean")
orig2 = io.open(P2, "rb").read()
try:
    io.open(P, "wb").write(orig + SNIP.encode("utf-8"))
    io.open(P2, "wb").write(orig2 + SNIP.replace("abbrev Star {S L : Type*}", "abbrev Star {S L : Type*}").encode("utf-8"))
    code, out = run()
    print("H2 (two different files) exit=%d  I3 fired: %s" % (code, "I3" in out and "finding" in out))
    for ln in out.splitlines():
        if "abbrev" in ln:
            print("   ", ln.strip()[:100])
finally:
    io.open(P, "wb").write(orig)
    io.open(P2, "wb").write(orig2)

code, _ = run()
print("gate exit after restore:", code)
