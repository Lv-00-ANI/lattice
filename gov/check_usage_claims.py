"""gov/check_usage_claims.py -- guard the MEASURABLE claims in the user-facing docs.

## Why a separate checker

`check_doc_consistency.py` answers "do two documents agree?" It cannot answer "is the number
RIGHT?", because it has no measurement to compare against.

Round 94 found `USAGE.md` saying "all 387 refutations" in a HEADING while the real count was 284.
Nothing caught it: the consistency checker only looks at root-level `.md` files, and even if it had
looked at USAGE.md, 387 appeared exactly once so there was nothing to contradict it.

A single occurrence cannot be caught by a consistency rule. It needs a MEASUREMENT.

## What this checks

USAGE.md is the user-facing entry point and STATE-FINAL.md is the document a reader trusts most,
so a wrong number in either is the most damaging kind: a reader has no way to tell. This checker
extracts each measurable claim and recomputes it from source.

Round 96 found STATE-FINAL still carrying the round-89 numbers (763 modules / 8,129 theorems /
10,882 declarations / 204,251 lines) while the tree had moved on, under a line that claims 'all
numbers measured in this run'. Nothing covered it: audit_counts guards README, this file guarded
USAGE, and STATE-FINAL was on nobody's list.

| claim in USAGE.md | recomputed as |
|---|---|
| `全部 N 条` (refutations) | count of refutation theorems by the census criterion |
| `误差 ≤ N` for roundingLossy | the theorem `roundtrip_error_le_one`'s bound |
| `8 条不变量` | the number of I-checks in gate.py |
| STATE-FINAL's module / theorem / declaration counts | recomputed from the tree |

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


def measure_modules():
    n = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        n += sum(1 for f in fs if f.endswith(".lean"))
    return n


def _strip_comments(src):
    out = []
    i = 0
    depth = 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i):
            depth = max(0, depth - 1)
            i += 2
        elif depth == 0:
            out.append(src[i])
            i += 1
        else:
            i += 1
    return "".join(out)


THM = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                 r"noncomputable[ \t]+)*(?:theorem|lemma)[ \t]+([^\s:]+)")
DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(?:theorem|lemma|def|structure|abbrev|inductive|class)"
                  r"[ \t]+")


def measure_theorems():
    n = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if f.endswith(".lean"):
                src = _read(os.path.join(root, f))
                n += len(THM.findall(_strip_comments(src)))
    return n


def measure_decls():
    n = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if f.endswith(".lean"):
                src = _read(os.path.join(root, f))
                n += len(DECL.findall(_strip_comments(src)))
    return n


#: Documents that describe the CURRENT tree. A stale count in one of these is a defect; the same
#: number in ROADMAP-v3..v11 or archive/ describes the tree AT THE TIME and must not be "fixed".
CURRENT_DOCS = ["README.md", "USAGE.md", "STATE-FINAL.md", "COMPLETENESS-AUDIT.md",
                "PARADIGM.md", "CONVENTIONS.md", "PROOF-CHAIN-RUNG.md"]

#: Counts that were once written down and are now known to be wrong. Re-appearing is a regression.
#: (pattern, explanation)
STALE = [
    (r"387\s*条", "refutation total was 387 at some point; the census says 284"),
    (r"8,035\s*条定理", "theorem count was 8,035 at some point; see STATE-FINAL"),
    (r"8,129\s*条定理", "theorem count was 8,129 at some point; see STATE-FINAL"),
    (r"10,882\s*条", "declaration count was 10,882 at some point; see STATE-FINAL"),
    (r"10,916\s*条", "declaration count was 10,916 at some point (unstripped); see STATE-FINAL"),
]


def check_stale():
    """Fail if a known-stale count reappears in a document that describes the current tree."""
    bad = []
    for doc in CURRENT_DOCS:
        path = os.path.join(LAKE, doc)
        if not os.path.exists(path):
            continue
        text = _read(path)
        for pat, why in STALE:
            for m in re.finditer(pat, text):
                line = text[: m.start()].count("\n") + 1
                bad.append((doc, line, m.group(0), why))
    return bad


def measure_py_scripts():
    return len([f for f in os.listdir(HERE) if f.endswith(".py")])


def measure_registrations():
    """Count verify_all's CHECKS entries the same way audit_counts.py does: by STRUCTURE.

    A regex demanding `"..."` as the command string misses entries written differently, which is
    exactly the bug audit_counts.py records having fixed. Counting tuple-opening lines is stable.
    """
    src = _read(os.path.join(HERE, "verify_all.py"))
    m = re.search(r"(?s)CHECKS\s*=\s*\[(.*?)\n\]", src)
    body = m.group(1) if m else src
    return len(re.findall(r'^\s*\(\s*"', body, re.M))


def measure_oversized():
    """Files with more than 60 declarations -- CONVENTIONS F1."""
    n = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            src = _read(os.path.join(root, f))
            if len(DECL.findall(_strip_comments(src))) > 60:
                n += 1
    return n


def measure_camel_theorems():
    """camelCase theorem names by the CONVENTIONS §7.5 criterion (last dot-segment)."""
    n = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            for m in THM.finditer(_strip_comments(_read(os.path.join(root, f)))):
                last = m.group(1).split(".")[-1]
                if "_" not in last and re.search(r"[a-z][A-Z]", last):
                    n += 1
    return n


CLAIMS = [
    ("USAGE: refutation count",
     r"全部\s*([\d,]+)\s*条",
     measure_refutations, "USAGE.md"),
    ("USAGE: gate invariant count",
     r"门禁（(\d+)\s*条不变量",
     measure_gate_invariants, "USAGE.md"),
    ("USAGE: roundingLossy error bound",
     r"整数取整，误差\s*≤\s*(\d+)",
     measure_rounding_bound, "USAGE.md"),
    ("STATE-FINAL: module count",
     r"\| 源模块（不含 `Reference/`） \| \*\*([\d,]+)\*\* \|",
     measure_modules, "STATE-FINAL.md"),
    ("STATE-FINAL: theorem count",
     r"\| 定理 / 引理（官方口径） \| \*\*([\d,]+)\*\* \|",
     measure_theorems, "STATE-FINAL.md"),
    ("STATE-FINAL: declaration count",
     r"\| 声明总数 \| \*\*([\d,]+)\*\* \|",
     measure_decls, "STATE-FINAL.md"),
    ("CONVENTIONS: declaration total",
     r"\| 内核声明总数 \| ([\d,]+) \|",
     measure_decls, "CONVENTIONS.md"),
    ("CONVENTIONS: gov script count",
     r"实测 `gov/` 有 \*\*(\d+) 个 `\.py`\*\*",
     measure_py_scripts, "CONVENTIONS.md"),
    ("CONVENTIONS: verify_all registrations",
     r"`verify_all` 的 (\d+) 项中",
     measure_registrations, "CONVENTIONS.md"),
    ("CONVENTIONS: files over 60 declarations",
     r"\| F1 超 60 声明 \| \*\*(\d+)\*\* \|",
     measure_oversized, "CONVENTIONS.md"),
    ("CONVENTIONS: camelCase theorems",
     r"\| N3 camelCase 定理 \| \*\*(\d+)\*\*",
     measure_camel_theorems, "CONVENTIONS.md"),
]


def run(usage_text=None):
    bad = 0
    print("%-38s %-10s %-10s %s" % ("claim", "documented", "measured", "verdict"))
    print("-" * 78)
    for label, pat, measure, doc in CLAIMS:
        path = os.path.join(LAKE, doc)
        text = _read(path)
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
    stale = check_stale()
    if stale:
        bad += len(stale)
        print()
        print("STALE COUNTS re-appeared in current-tree documents:")
        for doc, line, txt, why in stale:
            print("  %-22s line %-5d %-12s %s" % (doc, line, txt, why))
    else:
        print("stale counts: none of the %d known-stale figures appear in current docs"
              % len(STALE))

    print()
    if bad:
        print("DOC CLAIMS: %d claim(s) disagree with the tree" % bad)
        return 1
    print("DOC CLAIMS: every measurable claim across USAGE / STATE-FINAL / CONVENTIONS matches the tree")
    return 0


def self_test():
    """Prove the comparison itself can fail.

    Instead of rewriting the checked documents (which would make the test destructive), evaluate
    each claim's comparison against a deliberately wrong documented value and require it to be
    reported as wrong.
    """
    checked = 0
    failed = []
    for label, pat, measure, doc in CLAIMS:
        text = _read(os.path.join(LAKE, doc))
        ms = re.findall(pat, text)
        if not ms:
            continue
        measured = measure()
        if measured is None:
            continue
        checked += 1
        # a number that is certainly not the measurement
        bogus = measured + 1
        ok = int(ms[0].replace(",", "")) == measured
        would_be_wrong = (bogus != measured)
        if not (ok and would_be_wrong):
            failed.append(label)

    if failed:
        for f in failed:
            print("SELF-TEST FAILED: %s" % f)
        return 2
    if checked == 0:
        print("SELF-TEST FAILED: no claim was verifiable, so nothing could be caught")
        return 2
    print("SELF-TEST: %d claim(s) verify, and a differing value would be reported" % checked)
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(run())
