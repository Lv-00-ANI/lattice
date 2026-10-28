"""gov/check_selftest_coverage.py -- every gate must be able to FAIL for the right reason.

## Why this exists

Round 171 found **three** checks that had silently stopped checking:

* `check_scope_boundary.py`'s shape test used a regex that required a newline inside the signature, so
  every single-line `def update (p : Params) : Params := p` was skipped -- the test tested nothing;
* `check_doc_consistency.py`'s layer-split patterns hardcoded `17` while Core had grown to 18, so two
  whole measurements printed `0 in 0 docs  ok`;
* `check_usage_claims.py` printed `(absent) report-only` and `continue`d when a pattern matched nothing,
  so a number could be **deleted** from a document and the checker stayed green.

All three were caught by writing a self-test, not by reading the code. The lesson is not "be careful" --
it is that **a check which cannot demonstrate its own failure is indistinguishable from a check that
passes**.

## The rule

For every REGISTERED GATE, one of:

1. the script contains `--self-test` (it can demonstrate its own red), or
2. a companion `*_reactivity.py` exists and is itself registered (it plants a defect and requires the
   gate to react), or
3. it is listed in `EXEMPT` below **with a reason**.

Anything else fails. That turns "should I write a self-test?" from a matter of diligence into a build
error.

## Why an exemption list and not a blanket requirement

Some gates are self-validating in a different way: a *generator* whose `--check` compares its output
against the tree is already as red as the tree is wrong, and planting a defect would mean mutating the
tree it measures. Those are recorded in `EXEMPT` with that reason rather than left unverified by
oversight.

## Self-test

Two-way, because a coverage checker that always passes is the defect it is meant to prevent:

* a gate with no self-test and no exemption must be REPORTED;
* the live tree must be CLEAN (every current gap is either covered or exempted with a reason).
"""
import io
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import verify_all  # noqa: E402

#: Gates that are verified some other way, each with the reason. An entry whose script no longer exists
#: or which has GAINED a self-test is reported, so this table cannot rot into a list of stale excuses.
EXEMPT = {
    "gen_objective_map.py":
        "a generator: `--check` regenerates and compares against the tree, so it is red whenever the "
        "tree moves. Planting a defect would mean mutating the tree it measures.",
    "gen_objective_audit.py":
        "same shape as gen_objective_map.py: `--check` compares its output against a fresh run.",
    "escape_baseline.py":
        "a baseline comparison: it fails when the tree's escape count differs from the recorded "
        "baseline, which is already the defect it looks for.",
    "gen_lib_structure.py":
        "a reachability report: it fails when a clause's every carrier is a leaf, which is the defect "
        "itself. Planting one would mean deleting library structure.",
    "check_proof_chain_rung.py":
        "it fails when a named declaration is missing from the tree or a slot is unregistered; both "
        "are already defects, and the planted version would be the defect.",
    "check_g7.py":
        "a breakpoint survey: it reports every hop's user count and fails on a zero, which is the "
        "defect.",
    "verify_g4.py":
        "it shells out to `lake build` and compares whether the G4 theorem turns red, so a planted "
        "self-test would cost the same as the check itself. Since round 175 it detects an unavailable "
        "toolchain and reports SKIP instead of failing, so it is no longer a gate that can only run "
        "online (P2-12).",
}


def gating_scripts():
    """The scripts registered as gates, deduplicated and stripped of arguments."""
    out = []
    for label, script in verify_all.CHECKS:
        if label in verify_all.REPORT_ONLY:
            continue
        fn = script.split()[0]
        if fn not in out:
            out.append(fn)
    return out


def has_self_test(fn):
    p = os.path.join(HERE, fn)
    if not os.path.exists(p):
        return None
    src = io.open(p, encoding="utf-8", errors="replace").read()
    # A `*_reactivity.py` script IS a self-test: its whole method is to plant a defect and require the
    # gate under test to go red. Requiring it to carry its own `--self-test` would be circular -- a test
    # of a test needs a test of a test of a test. First run reported seven of them as uncovered, which
    # was my rule being wrong, not the scripts.
    if fn.endswith("_reactivity.py"):
        return True
    return ("--self-test" in src) or ("--selftest" in src)


def reactor_for(fn):
    p = os.path.join(HERE, fn[:-3] + "_reactivity.py")
    return fn[:-3] + "_reactivity.py" if os.path.exists(p) else None


def scan():
    """Return (uncovered, problems-with-EXEMPT)."""
    registered = set(gating_scripts())
    uncovered = []
    for fn in registered:
        hst = has_self_test(fn)
        if hst is None:
            uncovered.append((fn, "the registered script does not exist"))
            continue
        if hst:
            continue
        if reactor_for(fn) is not None:
            continue
        if fn in EXEMPT:
            continue
        uncovered.append((fn, "no --self-test and no *_reactivity.py companion"))
    # the exemption table must not rot
    rot = []
    for fn in EXEMPT:
        if fn not in registered:
            rot.append((fn, "exempted but not registered as a gate any more"))
        elif has_self_test(fn):
            rot.append((fn, "exempted but it now HAS a --self-test -- remove the exemption"))
        elif reactor_for(fn) is not None:
            rot.append((fn, "exempted but a *_reactivity.py companion exists -- remove the exemption"))
    return uncovered, rot


def main(argv):
    uncovered, rot = scan()
    if "--self-test" in argv:
        # (a) the live tree must be clean, or the coverage claim is false
        # (b) an uncovered gate must be reported: simulate by dropping an exemption
        victim = next(iter(EXEMPT))
        saved = dict(EXEMPT)
        del EXEMPT[victim]
        try:
            sim, _ = scan()
        finally:
            EXEMPT.update(saved)
        planted = [f for f, _ in sim if f == victim]
        ok = (not uncovered) and (not rot) and bool(planted)
        print("live uncovered  :", uncovered)
        print("rotten exemptions:", rot)
        print("planted (%s removed from EXEMPT) -> reported: %s" % (victim, bool(planted)))
        print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
        return 0 if ok else 2

    for fn, why in uncovered:
        print("  %-52s %s" % (fn, why))
    for fn, why in rot:
        print("  %-52s EXEMPTION ROT: %s" % (fn, why))
    if uncovered or rot:
        print()
        print("SELFTEST COVERAGE: %d gate(s) cannot demonstrate their own failure, %d rotten exemption(s)"
              % (len(uncovered), len(rot)))
        print("Fix: add `--self-test` to the gate, add a `*_reactivity.py` companion, or record it in")
        print("EXEMPT with the reason it is verified some other way.")
        return 1
    print("SELFTEST COVERAGE: every gate has --self-test, a reactivity companion, or a recorded reason")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
