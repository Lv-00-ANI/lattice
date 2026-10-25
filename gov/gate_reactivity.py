# -*- coding: utf-8 -*-
"""Gate reactivity test: plant each defect IN THE REAL TREE, confirm the gate reds,
then restore. Run against a scratch module so the real files are never at risk.

This is the discipline the legacy project lacked. `scripts/check-xref.ps1` there
reported 822 findings on its first run, nearly all false, which taught contributors to
ignore it. A gate earns trust only by failing when it should.
"""
import io
import os
import shutil
import subprocess
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# The probe must live INSIDE a zone the gate actually walks. It used to be written to
# `Lattice/Probe.lean`, which is the `root` zone -- not covered by the `kernel` scope that
# `verify_all.py --fast` sets. Measured: under `--fast` all four cases reported "got 0",
# i.e. this test failed because the gate never looked at the file, not because the gate
# was blind. A reactivity test that cannot see its own probe is a false alarm generator.
PROBE = os.path.join(ZERO, "Lattice", "Core", "Probe.lean")
GATE = os.path.join(ZERO, "gov", "gate.py")

CASES = [
    # (name, source, expected exit codes as a set)
    ("I2 sorry",          "import Lattice.Core.Syntax\n\ntheorem probe_thm : 1 = 1 := sorry\n", {2}),
    ("I1 axiom",          "import Lattice.Core.Syntax\n\naxiom probe_axiom : False\n", {1}),
    # An unbuilt probe has no olean, so I7 (artifact) legitimately fires as well.
    # What matters is that I1/I2 stay silent for a word inside a comment.
    ("I2 inside comment", "import Lattice.Core.Syntax\n\n/- a comment saying sorry -/\ntheorem probe_ok : 1 = 1 := rfl\n", {8}),
    ("I5 fake e2e",       "import Lattice.Core.Syntax\n\ntheorem e2e_fake : True := by trivial\n", {5, 8}),
]


def run_gate():
    r = subprocess.run([sys.executable, GATE, "--quiet"], cwd=ZERO,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def main():
    print("baseline gate exit:", run_gate()[0])
    failures = 0
    for name, src, expected in CASES:
        io.open(PROBE, "w", encoding="utf-8", newline="\n").write(src)
        try:
            code, out = run_gate()
            ok = code in expected
            # additionally require that I1/I2 are genuinely silent in the comment case
            if name == "I2 inside comment":
                ok = ok and ("I1   no axiom/opaque      ok" in out) and ("I2   no sorry/admit       ok" in out)
            if not ok:
                failures += 1
            print("  %-20s expect %-8s got %d  %s" %
                  (name, sorted(expected), code, "OK" if ok else "** FAIL **"))
            if not ok:
                for ln in out.splitlines()[:10]:
                    print("        " + ln)
        finally:
            if os.path.exists(PROBE):
                os.remove(PROBE)
    # artifacts check will complain about a stale probe olean if one was made
    print("=" * 60)
    print("restored; final gate exit:", run_gate()[0])
    print("=" * 60)
    print("REACTIVITY: %s" % ("ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures))
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
