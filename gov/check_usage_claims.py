"""gov/check_usage_claims.py -- guard the MEASURABLE claims that appear in USAGE.md.

## Why a separate checker

`check_doc_consistency.py` answers "do two documents agree?" It cannot answer "is the number
RIGHT?", because it has no measurement to compare against.

Round 94 found `USAGE.md` saying "all 387 refutations" in a HEADING while the real count was 284.
Nothing caught it: the consistency checker only looks at root-level `.md` files, and even if it had
looked at USAGE.md, 387 appeared exactly once so there was nothing to contradict it.

A single occurrence cannot be caught by a consistency rule. It needs a MEASUREMENT.

## What this checks

USAGE.md is the user-facing entry point, so a wrong number there is the most damaging kind: a reader
has no way to tell. This checker extracts each measurable claim and recomputes it from source.

| claim in USAGE.md | recomputed as |
|---|---|
| `全部 N 条` (refutations) | count of refutation theorems by the census criterion |
| `误差 ≤ N` for roundingLossy | the theorem `roundtrip_error_le_one`'s bound |
| `8 条不变量` | the number of I-checks in gate.py |

## It must be able to fail

`--self-test` plants a wrong number and asserts the checker reports it.
"""
import io
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(LAKE, "Lattice")

USAGE = os.path.join(LAKE, "USAGE.md")


def _read(p):
    return io.open(p, encoding="utf-8", errors="replace").read()


def measure_refutations():
    """The refutation total, taken from the census tool that OWNS the criterion.

    `check_refutation_census.py` holds `EXPECTED = {"total": N, ...}` -- the number it verifies
    against the tree. Reading it here (instead of re-deriving the rule) keeps one authority:
    round 56 showed that a re-implemented criterion drifts from the original.

    This checker therefore compares USAGE.md against the census, and the census guard separately
    compares the census against the tree. Chained, they cover the heading.
    """
    src = _read(os.path.join(HERE, "check_refutation_census.py"))
    m = re.search(r'"total"\s*:\s*(\d+)', src)
    return int(m.group(1)) if m else None


def measure_gate_invariants():
    """Count the I-numbered checks printed by gate.py.

    The I1..I8 lines are emitted from a table, so count the DISTINCT I-numbers in the report
    construction rather than the `rep.add` calls (I1/I2/I6/I8 never call `rep.add` -- they are
    reported directly, which is why counting `rep.add` gave 4).
    """
    src = _read(os.path.join(HERE, "gate.py"))
    ids = set(re.findall(r'\bI([1-9])\b', src))
    return len(ids)


def measure_rounding_bound():
    """The bound stated by `roundtrip_error_le_one`: read it from the theorem's own statement."""
    src = _read(os.path.join(LAT, "Lift", "RoundingBackend.lean"))
    # the statement is on one line: `theorem roundtrip_error_le_one (x : Z) : |...| <= 1`
    m = re.search(r"theorem roundtrip_error_le_one[^\n]*\|\s*≤\s*(\d+)", src)
    return int(m.group(1)) if m else None


CLAIMS = [
    ("refutation count in USAGE heading",
     r"全部\s*([\d,]+)\s*条",
     measure_refutations),
    ("gate invariant count",
     r"门禁（(\d+)\s*条不变量",
     measure_gate_invariants),
    ("roundingLossy error bound",
     r"整数取整，误差\s*≤\s*(\d+)",
     measure_rounding_bound),
]


def run(usage_text=None):
    text = usage_text if usage_text is not None else _read(USAGE)
    bad = 0
    print("%-38s %-10s %-10s %s" % ("claim", "documented", "measured", "verdict"))
    print("-" * 78)
    for label, pat, measure in CLAIMS:
        ms = re.findall(pat, text)
        if not ms:
            print("%-38s %-10s %-10s %s" % (label, "(absent)", "-", "report-only"))
            continue
        measured = measure()
        if measured is None:
            print("%-38s %-10s %-10s %s" % (label, ms[0], "(unmeasurable)", "report-only"))
            continue
        ok = all(int(x.replace(",", "")) == measured for x in ms)
        print("%-38s %-10s %-10s %s" % (label, ms[0], measured,
                                        "ok" if ok else "*** WRONG ***"))
        if not ok:
            bad += 1
    print()
    if bad:
        print("USAGE CLAIMS: %d claim(s) disagree with the tree" % bad)
        return 1
    print("USAGE CLAIMS: every measurable claim in USAGE.md matches the tree")
    return 0


def self_test():
    """Plant a wrong number and assert it is reported."""
    text = _read(USAGE)
    planted = re.sub(r"全部\s*([\d,]+)\s*条", "全部 99999 条", text, count=1)
    if planted == text:
        print("SELF-TEST FAILED: could not plant a wrong number")
        return 2
    rc = run(planted)
    if rc == 0:
        print("SELF-TEST FAILED: a planted wrong number was not reported")
        return 2
    print("SELF-TEST: a planted wrong number IS reported")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(run())
