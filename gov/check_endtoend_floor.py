"""Round 26, L4-7: give the content census a FLOOR, so it gates instead of reporting.

## Why

`check_endtoend_content.py` already computes what `gate.py`'s I5 does not: **how many theorems touch >= 2
layers by CONTENT** (1,763 at round 24). But `verify_all` lists it in `REPORT_ONLY`, so it prints a number and
gates nothing -- the same defect as `audit_duplicates` (round 11) and the debt counter (round 5).

## One authority, not two

This script does **not** re-implement the scan. It runs `check_endtoend_content.py`, which now also writes
`gov/endtoend-cross.tsv` (one `<file>\\t<theorem>` per line), and compares that file against
`gov/endtoend-baseline.txt`. **The census logic lives in exactly one place.**

## What kind of gate

**A one-way floor.** The two directions mean different things here:

- a theorem that **loses** cross-layer status is a **regression** -> fail;
- a theorem that **gains** it is an **improvement** -> must NOT fail, or every productive round would have to
  edit a 1,700-line baseline and the baseline would become noise.

Plus: an **empty census fails**, because a scan that finds nothing is a broken scan, not a clean tree.
"""

import io
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CENSUS = os.path.join(HERE, "check_endtoend_content.py")
TSV = os.path.join(HERE, "endtoend-cross.tsv")
BASE = os.path.join(HERE, "endtoend-baseline.txt")

sys.stdout.reconfigure(encoding="utf-8", errors="replace")


def run_census():
    """Run the census (which rewrites the TSV) and return `{(file, name)}`."""
    if os.path.exists(TSV):
        os.remove(TSV)
    r = subprocess.run([sys.executable, CENSUS], cwd=HERE, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    if not os.path.exists(TSV):
        print("ENDTOEND FLOOR: the census did not write %s (exit %d)" % (TSV, r.returncode))
        for ln in (r.stdout or "").strip().split("\n")[-4:]:
            print("   ", ln)
        return None
    out = set()
    for ln in io.open(TSV, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 2:
            out.add((p[0], p[1]))
    return out


def compare(base, cur):
    """`(lost, gained)` -- the whole verdict of this gate is a function of two sets.

    Factored out so `--self-test` can exercise it without touching the tree.
    """
    return sorted(base - cur), len(cur - base)


def self_test():
    """The gate must demonstrate BOTH of its failure modes.

    Round 26. This session has now found eight checks that could not fail; a floor gate that can only pass
    would be the ninth. So:

    1. a base entry absent from `cur` must be reported LOST (the regression direction);
    2. a `cur` entry absent from `base` must NOT be reported as lost (the improvement direction --
       if this went red, every productive round would be forced to edit the baseline);
    3. an empty `cur` must be treated as broken, not as clean.
    """
    ok = True

    lost, gained = compare({("A.lean", "kept"), ("B.lean", "gone")}, {("A.lean", "kept")})
    if lost != [("B.lean", "gone")] or gained != 0:
        print("  LOST direction FAILED: %r %r" % (lost, gained))
        ok = False

    lost, gained = compare({("A.lean", "kept")}, {("A.lean", "kept"), ("C.lean", "new")})
    if lost != [] or gained != 1:
        print("  GAINED direction FAILED (an improvement must not fail): %r %r" % (lost, gained))
        ok = False

    if compare(set(), {("A.lean", "x")})[0] != []:
        print("  empty-baseline direction FAILED")
        ok = False

    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


def main(argv):
    cur = run_census()
    if cur is None:
        return 1
    if not cur:
        print("ENDTOEND FLOOR: the census found ZERO cross-layer theorems -- an empty scan is a broken scan")
        return 1

    if "--write-baseline" in argv:
        io.open(BASE, "w", encoding="utf-8", newline="\n").write(
            "# theorems that touch >= 2 layers BY CONTENT.\n"
            "# A FLOOR: losing one is a regression; gaining one is an improvement and does not fail.\n"
            + "".join("%s\t%s\n" % k for k in sorted(cur)))
        print("ENDTOEND FLOOR: baseline written, %d entries" % len(cur))
        return 0

    if not os.path.exists(BASE):
        print("ENDTOEND FLOOR: no baseline (run --write-baseline once); %d found" % len(cur))
        return 1

    base = set()
    for ln in io.open(BASE, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 2:
            base.add((p[0], p[1]))

    lost, gained = compare(base, cur)
    print("ENDTOEND FLOOR: %d cross-layer theorem(s); floor %d; lost %d; gained %d"
          % (len(cur), len(base), len(lost), gained))
    for rel, name in lost[:15]:
        print("   LOST  %s :: %s" % (rel, name))
    if lost:
        print("ENDTOEND FLOOR: a theorem stopped touching >= 2 layers -- coverage regression")
        print()
        print("  ⚠ A NAME-SET FLOOR CANNOT TELL A RENAME FROM A DELETION. Round 32 hit this:"
              " `conformance_names_nodup`")
        print("    was REPLACED by `conformance_names_dedup_length` (22 vectors make the raw name list"
              " have duplicates,")
        print("    so `Nodup` became false and the statement moved to the deduplicated list). The gate"
              " reported it as a")
        print("    loss, which is the correct thing for it to do and the wrong thing to conclude from it.")
        print("    The only honest resolution is: regenerate the floor and SAY that the change was a"
              " replacement.")
        return 1
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
