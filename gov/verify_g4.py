# -*- coding: utf-8 -*-
"""G4 verification: does removing a filler actually break the downstream?

Requirement (2) says an unproved proposition must be an explicit hole so that "any theorem
that cannot be proved still leaves the framework valid". The half that has never been
demonstrated is the *other* direction: if a filler is withdrawn, the theorems that depended on
it must turn red rather than silently survive.

The experiment manipulates a scratch theorem, not a target theorem:

  1. add a probe module that discharges `PenaltyExact` for a trivial embedding and then
     USES it to derive a downstream fact;
  2. confirm the module builds;
  3. delete the discharge, keep the use;
  4. confirm the build FAILS, with the failure attributable to the missing hypothesis.

Step 4 is the point. A framework where removing a proof leaves everything green is a
framework where proofs are decoration.
"""
import io
import os
import shutil
import subprocess
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROBE = os.path.join(ZERO, "Lattice", "G4Probe.lean")

WITH_FILLER = """import Mathlib
import Lattice.Runtime.PenaltyEmbedding

/-! Probe for G4: a filler is present, so the downstream theorem builds. -/

open Lattice.Lift
open Lattice.Core

/-- A trivial embedding whose only point is accepted. -/
def probeEmbedding : PenaltyEmbedding Unit Unit where
  loss := fun _ _ => 0
  Sat := fun _ _ => True

/-- The discharge: the embedding is exact at level B. -/
theorem probeEmbedding_exact : PenaltyExact probeEmbedding :=
  fun _ _ _ => trivial

/-- Downstream: a minimiser satisfies the constraint, citing the discharge. -/
theorem probe_downstream (x : Unit) (hmin : IsLocalMin (probeEmbedding.loss ()) x) :
    probeEmbedding.Sat () x :=
  embedding_sound_at_minimiser probeEmbedding_exact hmin
"""

WITHOUT_FILLER = """import Mathlib
import Lattice.Runtime.PenaltyEmbedding

/-! Probe for G4: the filler has been WITHDRAWN; the downstream theorem must fail. -/

open Lattice.Lift
open Lattice.Core

/-- A trivial embedding whose only point is accepted. -/
def probeEmbedding : PenaltyEmbedding Unit Unit where
  loss := fun _ _ => 0
  Sat := fun _ _ => True

/-- Downstream still cites `probeEmbedding_exact`, which no longer exists. -/
theorem probe_downstream (x : Unit) (hmin : IsLocalMin (probeEmbedding.loss ()) x) :
    probeEmbedding.Sat () x :=
  embedding_sound_at_minimiser probeEmbedding_exact hmin
"""


def toolchain_available():
    """Can this check run at all? Returns `(ok, why_not)`.

    Round 175, P2-12. This is the ONE gate that shells out to `lake` and needs a warm build tree, so it
    is the only gate that cannot run offline. Failing for that reason reads as "G4 is broken" when the
    truth is "the check did not run", and a reader cannot tell the two apart from an exit code.

    So the availability of the toolchain is checked FIRST and reported as `SKIP`, not as a pass and not
    as a failure. `SKIP` is printed loudly and the exit code is 0 only because a check that could not
    execute has not found anything.
    """
    if shutil.which("lake") is None:
        return False, "`lake` is not on PATH"
    if not os.path.isdir(os.path.join(ZERO, ".lake")):
        return False, "no `.lake/` build directory (nothing has been built here)"
    return True, ""


def build(target=None):
    cmd = ["lake", "build"] + ([target] if target else [])
    r = subprocess.run(cmd, cwd=ZERO, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, ((r.stdout or "") + (r.stderr or ""))


def main():
    ok, why = toolchain_available()
    if not ok:
        print("  SKIP: cannot run -- %s" % why)
        print()
        print("G4 REACTIVITY: SKIPPED (toolchain unavailable, NOT a pass and NOT a failure)")
        print("This check proves the G4 theorem goes red when its filler is withdrawn, which needs a")
        print("real `lake build`. Offline it cannot run; see backlog item P2-12.")
        # **W0-3a: a check that COULD NOT RUN is not a pass.** Exit 77 is the third state;
        # `verify_all` prints it as SKIP and never counts it as gating_ok.
        return 77

    failures = 0
    try:
        io.open(PROBE, "w", encoding="utf-8", newline="\n").write(WITH_FILLER)
        code, out = build("Lattice.G4Probe")
        ok1 = code == 0
        print("  with filler present   :", "BUILD OK" if ok1 else "** UNEXPECTED FAIL **")
        if not ok1:
            failures += 1
            print("     ", out[-800:])

        io.open(PROBE, "w", encoding="utf-8", newline="\n").write(WITHOUT_FILLER)
        code, out = build("Lattice.G4Probe")
        ok2 = code != 0 and "probeEmbedding_exact" in out
        print("  filler withdrawn      :", "RED, missing `probeEmbedding_exact`"
              if ok2 else "** DID NOT TURN RED **")
        if not ok2:
            failures += 1
            print("     ", out[-800:])
    finally:
        if os.path.exists(PROBE):
            os.remove(PROBE)
        # a stale olean for a deleted probe would trip I7
        stale = os.path.join(ZERO, ".lake", "build", "lib", "Lattice", "G4Probe.olean")
        if os.path.exists(stale):
            os.remove(stale)

    print("=" * 60)
    code, out = build("Lattice")
    print("clean rebuild exit:", code)
    print("G4:", "PASS" if failures == 0 else "%d FAILURE(S)" % failures)
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
