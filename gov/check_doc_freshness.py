"""gov/check_doc_freshness.py -- numeric claims that describe the CURRENT tree must match it.

## Why this is separate from `check_usage_claims`

`check_usage_claims` guards 14 claims about module / theorem / declaration counts and a few naming
figures. It does NOT guard:

    OBJECTIVE-MAP.md    "条款数：14" and "载体总数：27"
    OBJECTIVE-AUDIT.md  "全库 8,328 条定理"
    README.md           "未清欠账 0" and "永久边界 4"

Those are exactly the figures that move when the tree moves -- this round alone changed the theorem
count 8,323 -> 8,328 and the boundary count 3 -> 4. Each was updated BY HAND in three or four places,
and the only reason they are correct now is that I remembered. **That is the pattern this project has
paid for repeatedly.**

## What is deliberately NOT checked

- **`PARADIGM.md`'s scores.** They are estimates with arguable weights; `PARADIGM.md` says so. A guard
  would turn a judgement into a claim of measurement.
- **Round numbers, dates, and historical figures** (`第 176 轮`, `2781→2101`, `10,820`). They describe
  the tree at the time and must not be updated -- the objective's own rule.
- **Anything inside a `第 N 轮` history line.** Those sentences are evidence about the past.

## The rule, and why absence is a failure

Same as `check_usage_claims`: a pattern that matches nothing is a FAILURE. A claim whose location moved
is indistinguishable from a claim that agrees, unless the checker says which one it is.

`--self-test` plants a wrong number for each claim and requires it to be reported; it also requires the
live tree to be clean.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, HERE)

import audit_counts          # noqa: E402
import check_objective_coverage as cov  # noqa: E402


def _read(rel):
    return io.open(os.path.join(LAKE, rel), encoding="utf-8", errors="replace").read()


def m_clauses():
    return len(cov.CLAUSES)


def m_carriers():
    return sum(len(v) for v in cov.CLAUSES.values())


def m_theorems():
    return audit_counts.total_theorems()


def _slot_counts():
    """`(owed, boundaries)` straight from the numbers `Slots.lean` proves with `decide`.

    Reading the proved numbers (rather than re-parsing the registry) keeps ONE authority: the kernel
    already checks `owedCount = 0` and `boundaryCount = 4`, so those are the values the documents must
    agree with.
    """
    src = io.open(os.path.join(LAKE, "Lattice", "Slots.lean"), "rb").read().decode("utf-8", "replace")
    owed = re.search(r"Slot\.owedCount\s+fullRegistry\s*=\s*(\d+)", src)
    bnd = re.search(r"Slot\.boundaryCount\s+fullRegistry\s*=\s*(\d+)", src)
    if not owed or not bnd:
        return None, None
    return int(owed.group(1)), int(bnd.group(1))


def m_owed():
    return _slot_counts()[0]


def m_boundaries():
    return _slot_counts()[1]


#: `(label, regex, measuring function, document)`.
CLAIMS = [
    ("OBJECTIVE-MAP: clause count", r"条款数：(\d+)", m_clauses, "OBJECTIVE-MAP.md"),
    ("OBJECTIVE-MAP: carrier count", r"载体总数：(\d+)", m_carriers, "OBJECTIVE-MAP.md"),
    ("OBJECTIVE-AUDIT: theorem count", r"全库 ([\d,]+) 条定理", m_theorems, "OBJECTIVE-AUDIT.md"),
    ("README: owed slots", r"\| \*\*未清欠账\*\* \| \*\*(\d+)\*\* \|", m_owed, "README.md"),
    ("README: permanent boundaries", r"\| \*\*永久边界\*\* \| \*\*(\d+)\*\* \|",
     m_boundaries, "README.md"),
    ("STATE-FINAL: owed slots", r"\| 未清欠账 \| \*\*(\d+)\*\* \|", m_owed, "STATE-FINAL.md"),
    ("STATE-FINAL: permanent boundaries", r"\| 永久边界 \| \*\*(\d+)\*\* \|",
     m_boundaries, "STATE-FINAL.md"),
    ("DELIVERY: owed slots", r"\| 未清欠账 \| \*\*(\d+)\*\* \|", m_owed, "DELIVERY.md"),
    ("DELIVERY: permanent boundaries", r"\| 永久边界 \| \*\*(\d+)\*\* \|",
     m_boundaries, "DELIVERY.md"),
]


def run(verbose=True):
    bad = 0
    rows = []
    for label, pat, measure, doc in CLAIMS:
        found = re.findall(pat, _read(doc))
        measured = measure()
        if not found:
            rows.append((label, "(absent)", "-", "*** PATTERN MATCHED NOTHING ***"))
            bad += 1
            continue
        if measured is None:
            rows.append((label, found[0], "(unmeasurable)", "*** CANNOT MEASURE ***"))
            bad += 1
            continue
        ok = all(int(x.replace(",", "")) == measured for x in found)
        rows.append((label, found[0], str(measured), "ok" if ok else "*** WRONG ***"))
        if not ok:
            bad += 1
    if verbose:
        print("%-38s %-10s %-10s %s" % ("claim", "documented", "measured", "verdict"))
        print("-" * 78)
        for r in rows:
            print("%-38s %-10s %-10s %s" % r)
    return bad, rows


def self_test():
    """Two-way: the live tree must be clean, and a wrong number in every claim must be reported.

    The second half is checked WITHOUT touching the documents: each claim's regex is re-run against the
    document text with the captured number replaced by a certainly-wrong one, and the comparison is
    required to fail.
    """
    failures = []
    bad, _ = run(verbose=False)
    if bad:
        failures.append("the live tree already has %d stale claim(s)" % bad)
    checked = 0
    for label, pat, measure, doc in CLAIMS:
        text = _read(doc)
        measured = measure()
        if measured is None:
            failures.append("%s: unmeasurable" % label)
            continue
        found = re.findall(pat, text)
        if not found:
            failures.append("%s: pattern matched nothing" % label)
            continue
        checked += 1
        # doctoring: rewrite the digits INSIDE the first regex match, not the first occurrence of the
        # digit string anywhere. `text.replace(found[0], bogus, 1)` was the first attempt and it broke
        # for every claim whose value is 0 -- `"0"` occurs everywhere, so the substitution landed
        # somewhere else and the claim still matched its original value, which the self-test correctly
        # reported as "a wrong number would NOT be reported".
        m = re.search(pat, text)
        bogus = str(int(found[0].replace(",", "")) + 1)
        g0, g1 = m.span(1)
        doctored = text[:g0] + bogus + text[g1:]
        again = re.findall(pat, doctored)
        if not again or int(again[0].replace(",", "")) == measured:
            failures.append("%s: a wrong number would NOT be reported" % label)
    if failures:
        for f in failures:
            print("SELF-TEST FAILED: %s" % f)
        return 2
    print("SELF-TEST: live tree clean; %d claim(s) each report a wrong number" % checked)
    return 0


def main(argv):
    if "--self-test" in argv:
        return self_test()
    bad, _ = run()
    print()
    if bad:
        print("DOC FRESHNESS: %d claim(s) disagree with the tree" % bad)
        return 1
    print("DOC FRESHNESS: every claim about the current tree matches it")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
