# -*- coding: utf-8 -*-
"""Re-verification scripts must be runnable from the gate, not only by hand.

Round 30 found two real defects (an orphan artifact, an over-general claim) using these scripts. A
measurement that only exists because someone remembered to run it will not run again. `verify_all.py`
chains the reactivity tests, the re-verification scripts, the audits and the two proof-chain
generators into one command with a single
exit code, so "the project is healthy" is one reproducible statement rather than a narrative.

Deliberately NOT wired into `gate.py`: the gate is a fast invariant check run on every edit, while these
are slower audits (they walk the whole tree several times). Keeping them separate keeps the gate cheap
enough that people actually run it.
"""
import io
import os
import subprocess
import sys
import time

# The console codepage may be GBK: any non-ASCII diagnostic must not crash the report itself.
try:
    sys.stdout.reconfigure(errors="replace")
except (AttributeError, ValueError):
    pass


HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))

# Checks declared as REPORT-ONLY.
#
# Measured problem this solves: 16 of the registered scripts end `main()` with a literal
# `return 0`, so their exit code is a constant. Several say so on purpose -- "report
# only", "Exit 0 is deliberate", "a review list, not a verdict" -- because they print
# findings a human must judge. That is a defensible design, but it made the summary line
# "VERIFY ALL: PASS" misleading: it counted 32 processes whose exit code was 0, without
# saying that 16 of them could not have been anything else.
#
# So they still run -- their output is the point -- but they are counted in a separate
# column, and the summary states both numbers. Turning a reporter into a gate is a change
# to what it claims, not a one-line edit; that decision belongs to whoever owns the check.
REPORT_ONLY = {
    "reverify: requirements", "reverify: chain", "reverify: islands",
    "audit: duplicates", "audit: bodies", "audit: docs vs code", "audit: reachable",
    "audit: claims", "audit: liveness", "audit: region", "audit: tables",
    "audit: counts", "audit: abstraction", "audit: islands",
    "audit: duplicate statements", "audit: untracked work",
    "gen: proof chain (geo)", "gen: proof chain (kernel)",
}

# (label, script, expects a specific exit code or None for "any")
CHECKS = [
    ("gate", "gate.py"),
    ("gate --selftest", "gate.py --selftest"),
    ("comments", "check_comments.py"),
    ("registry", "check_registry.py"),
    ("reactivity: gate", "gate_reactivity.py"),
    ("reactivity: slots", "check_slots_reactivity.py"),
    ("reactivity: comments", "check_comments_reactivity.py"),
    ("reactivity: I8 gate", "check_i8_reactivity.py"),
    ("reactivity: registry", "check_registry_reactivity.py"),
    ("reactivity: registry-gate", "check_registry_gate_reactivity.py"),
    ("reactivity: G4", "verify_g4.py"),
    ("reverify: requirements", "reverify.py"),
    ("reverify: chain", "reverify_chain.py"),
    ("reverify: islands", "reverify_islands.py"),
    ("audit: duplicates", "audit_duplicates.py"),
    ("audit: bodies", "audit_bodies.py"),
    ("audit: geo structure", "audit_geo.py"),
    ("audit: docs vs code", "audit_docs.py"),
    ("audit: reachable", "audit_reach.py"),
    ("audit: claims", "audit_claims.py"),
    ("audit: liveness", "audit_liveness.py"),
    ("audit: region", "audit_region.py"),
    ("audit: tables", "audit_tables.py"),
    ("audit: counts", "audit_counts.py"),
    ("audit: G7 breakpoints", "check_g7.py"),
    ("audit: proof chain rung", "check_proof_chain_rung.py"),
    ("audit: abstraction", "audit_abstraction.py"),
    ("audit: islands", "audit_islands.py"),
    ("audit: duplicate statements", "audit_duplicate_statements.py"),
    ("audit: untracked work", "audit_untracked.py"),
    ("gen: proof chain (geo)", "proof_chain_geo.py"),
    ("gen: proof chain (kernel)", "chain.py"),
    ("scope: escape baseline", "escape_baseline.py --check"),
    # The frozen governance archive is data the gates read, so it needs its own guard:
    # a stale entry-count claim inside CORRECTIONS.md is the exact drift class this
    # repository spent B1-B480 learning. `--lean archive` points the tool at the
    # archive directory instead of a Lean source tree.
    ("archive: corrections count", "check-corrections-count.py --root %s --lean archive" % ZERO),
]


# Checks that are only meaningful (or only affordable) in a full run.
#
# History: this used to be {"reactivity: gate", "reactivity: G4"} -- the two checks that
# prove the gate can FAIL were exactly the two skipped by the recommended `--fast`
# command. That made the advertised fast path prove less than the full one about
# correctness, while looking like the cheap way to check health. They are cheap enough
# now that the kernel tree is a single root: measured 3 s and 6 s respectively.
SLOW_ONLY = set()


def main():
    fast = "--fast" in sys.argv
    if fast:
        os.environ["DSH_GATE_SCOPE"] = "kernel"
    failures = []
    gating_ok = 0
    reports = 0
    t_start = time.time()
    for i, (label, cmd) in enumerate(CHECKS, 1):
        if fast and label in SLOW_ONLY:
            print("  %-30s skipped (--fast)" % label)
            continue
        parts = [sys.executable] + [os.path.join(HERE, p) if p.endswith(".py") else p
                                    for p in cmd.split()]
        t0 = time.time()
        r = subprocess.run(parts, cwd=ZERO, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        dt = time.time() - t0
        report = label in REPORT_ONLY
        if report:
            # mark reporters explicitly so a reader cannot mistake "ok" for "passed a gate"
            status = "reported" if r.returncode == 0 else "FAIL(%d)" % r.returncode
            reports += 1
        else:
            status = "ok" if r.returncode == 0 else "FAIL(%d)" % r.returncode
            if r.returncode == 0:
                gating_ok += 1
        # `flush=True` matters: this run takes minutes, and a redirected stdout otherwise
        # shows nothing until the process exits -- which reads like a hang.
        print("  [%2d/%d] %-30s %-9s %5.1fs" % (i, len(CHECKS), label, status, dt), flush=True)
        if r.returncode != 0:
            failures.append((label, r.returncode, (r.stdout or "") + (r.stderr or "")))
    print("=" * 60, flush=True)
    if failures:
        for label, code, out in failures:
            print("\n--- %s (exit %d) ---" % (label, code))
            print(out.strip()[:1200])
    mode = "fast (kernel only)" if fast else "full"
    # The summary separates the two populations on purpose. A single "32/32 PASS" hid the
    # fact that 16 of those 32 could not have returned anything but 0.
    print("VERIFY ALL [%s]: %s  (%.1fs total)" %
          (mode, "PASS" if not failures else "%d FAILURE(S)" % len(failures),
           time.time() - t_start), flush=True)
    print("  gating checks passed : %d  (these CAN fail)" % gating_ok, flush=True)
    print("  report-only checks   : %d  (these print findings; exit code is not a verdict)"
          % reports, flush=True)
    if fast:
        print("note: --fast restricts every walk to the kernel zone. Run without --fast before "
              "concluding the tree is acceptable.")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
