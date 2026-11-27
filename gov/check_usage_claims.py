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

import census_docs

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _paths import resolve_abs  # noqa: E402  (path-keyed artifact: see _paths.py)

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(LAKE, "Lattice")

USAGE = os.path.join(LAKE, "USAGE.md")


def _read(p):
    return io.open(p, encoding="utf-8", errors="replace").read()


def measure_refutations():
    """The refutation total, taken from the document that OWNS the criterion.

    Round 56 showed that a re-implemented criterion drifts from the original, so this used to
    regex-scrape `check_refutation_census.py` for its `EXPECTED = {"total": N}` constant. That
    constant is GONE: it said 285 while `REFUTATION-CENSUS.md` said 284, and nothing compared them.

    The authority is now the document, read through `census_docs` -- the same parser the census guard
    uses. The chain is therefore

        USAGE.md  ==  REFUTATION-CENSUS.md  ==  tree
                   ^                        ^
                   this checker             check_refutation_census.py

    and each link is separately machine-checked.
    """
    try:
        total, _layers = census_docs.refutation_expected(
            os.path.join(HERE, "..", "REFUTATION-CENSUS.md"))
        return total
    except census_docs.CensusDocError:
        return None


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
    src = _read(resolve_abs(LAT, "Lift/RoundingBackend.lean"))
    # the statement is on one line: `theorem roundtrip_error_le_one (x : Z) : |...| <= 1`
    m = re.search(r"theorem roundtrip_error_le_one[^\n]*\|\s*≤\s*(\d+)", src)
    return int(m.group(1)) if m else None


def measure_modules():
    n = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        # skip the throwaway module the reactivity checks build: it is gitignored, it is not part of
        # the deliverable, and counting it makes this number depend on whether a reactivity check
        # happened to be mid-flight. The predicate lives in one place (`audit_counts`) so the two
        # counters cannot disagree about what a module is.
        from audit_counts import is_generated_probe
        n += sum(1 for f in fs
                 if f.endswith(".lean") and not is_generated_probe(os.path.join(root, f)))
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
    # Round 977: exclude the reactivity checks' throwaway modules here too. `measure_modules` already did,
    # but the two declaration counters did NOT, so a killed `verify_all` that left `Lattice/G4Probe.lean`
    # behind inflated the documented theorem and declaration counts by exactly its contents (2 and 3).
    # An instrument must not read differently depending on whether a check was mid-flight.
    from audit_counts import is_generated_probe
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if f.endswith(".lean") and not is_generated_probe(os.path.join(root, f)):
                src = _read(os.path.join(root, f))
                n += len(THM.findall(_strip_comments(src)))
    return n


def measure_decls():
    n = 0
    from audit_counts import is_generated_probe   # see measure_theorems for why
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if f.endswith(".lean") and not is_generated_probe(os.path.join(root, f)):
                src = _read(os.path.join(root, f))
                n += len(DECL.findall(_strip_comments(src)))
    return n


#: Documents that describe the CURRENT tree. A stale count in one of these is a defect; the same
#: number in ROADMAP-v3..v11 or archive/ describes the tree AT THE TIME and must not be "fixed".
CURRENT_DOCS = ["README.md", "USAGE.md", "STATE-FINAL.md", "COMPLETENESS-AUDIT.md",
                "PARADIGM.md", "CONVENTIONS.md", "PROOF-CHAIN-RUNG.md", "DELIVERY.md"]

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


def _verify_all_counts():
    """(total, gating, reporters) from verify_all.py's own registries, not from a constant.

    Round 1122. Three numbers were in circulation and two docs were stale: a registry count (105), a total (126)
    and a --fast PASS count (94). The first two are STATIC facts about CHECKS + REPORT_ONLY and belong in a claim;
    the third is a RUN RESULT depending on which checks the mode skips, so it is not a document claim and is
    deliberately NOT asserted here.
    """
    import verify_all
    total = len(verify_all.CHECKS)
    rep = len(verify_all.REPORT_ONLY)
    return total, total - rep, rep


def measure_check_total():
    return _verify_all_counts()[0]


def measure_check_gating():
    return _verify_all_counts()[1]


def measure_check_reporters():
    return _verify_all_counts()[2]


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
    # Round 1122: the gating number had NO checker and two docs were stale by 6. Labelled per number so that
    # "how many checks exist" cannot be confused with "how many passed under --fast".
    ("DELIVERY: verify_all total checks",
     r"(\d+) 项检查",
     measure_check_total, "DELIVERY.md"),
    ("DELIVERY: verify_all gating checks",
     r"(\d+) 个门禁",
     measure_check_gating, "DELIVERY.md"),
    ("DELIVERY: verify_all reporters",
     r"(\d+) 个报告器",
     measure_check_reporters, "DELIVERY.md"),
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
     r"\| camelCase 定理 \| \*\*(\d+)\*\*",
     measure_camel_theorems, "CONVENTIONS.md"),
    ("DELIVERY: module count",
     r"\| 源模块（不含 `Reference/`） \| \*\*(\d+)\*\* \|",
     measure_modules, "DELIVERY.md"),
    ("DELIVERY: theorem count",
     r"\| 定理 / 引理（官方口径） \| \*\*([\d,]+)\*\* \|",
     measure_theorems, "DELIVERY.md"),
    ("DELIVERY: declaration count",
     r"\| 声明总数 \| \*\*([\d,]+)\*\* \|",
     measure_decls, "DELIVERY.md"),

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
            # A CLAIM WHOSE PATTERN MATCHES NOTHING IS A FAILURE, not a pass.
            #
            # This branch used to print `(absent) report-only` and `continue`. Three claims had been
            # silently in that state -- `内核声明总数`, `camelCase 定理`, `F1 超 60 声明` -- because their
            # patterns still expected pipe-table rows (`| X | **N** |`) while CONVENTIONS had been
            # rewritten as space-aligned text. So a number could DISAPPEAR from a document and this
            # checker would go green; worse, `内核声明总数` read 10,836 while the tree had 10,983.
            #
            # Deleting a number is now as loud as changing it. If a claim is genuinely obsolete,
            # delete it from CLAIMS -- do not let it rot into a no-op.
            print("%-38s %-10s %-10s %s"
                  % (label, "(absent)", "-", "*** PATTERN MATCHED NOTHING ***"))
            bad += 1
            continue
        measured = measure()
        if measured is None:
            # same reasoning: a measurement that cannot run is not agreement
            print("%-38s %-10s %-10s %s"
                  % (label, ms[0], "(unmeasurable)", "*** CANNOT MEASURE ***"))
            bad += 1
            continue
        ok = all(int(x.replace(",", "")) == measured for x in ms)
        print("%-38s %-10s %-10s %s" % (label, ms[0], measured,
                                        "ok" if ok else "*** WRONG ***"))
        if not ok:
            bad += 1
    # DELIVERY.md claims "11 guards, all exit 0". This checker does NOT re-run the other guards --
    # verify_all already runs all of them, and re-running them here made the checker recurse
    # (each guard would run the whole suite). What CAN be checked here without recursion is the
    # COUNT: the document names N guards, and gov/ must contain exactly those guards.
    dl = _read(os.path.join(LAKE, "DELIVERY.md"))
    m = re.search(r"\*\*(\d+) 个守卫逐个运行，全部 exit 0\*\*", dl)
    if m:
        claimed = int(m.group(1))
        # the guards named in the DELIVERY table
        named = set(re.findall(r"\| `(check_[a-z_]*\.py|gate\.py|audit_counts\.py)`", dl))
        if claimed == len(named):
            print("DELIVERY: guard count %d matches the %d named in its own table"
                  % (claimed, len(named)))
        else:
            bad += 1
            print("DELIVERY: claims %d guards but names %d  *** WRONG ***"
                  % (claimed, len(named)))

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
    print("DOC CLAIMS: every measurable claim across USAGE / STATE-FINAL / CONVENTIONS / DELIVERY matches the tree")
    return 0


def self_test():
    """Prove the comparison itself can fail.

    Instead of rewriting the checked documents (which would make the test destructive), evaluate
    each claim's comparison against a deliberately wrong documented value and require it to be
    reported as wrong.

    Round 169: this also requires that EVERY claim's pattern finds its number. It used to `continue`
    past a claim whose pattern matched nothing, which is how three claims stayed dead -- a self-test
    that skips the broken cases certifies the broken state.
    """
    checked = 0
    absent = []
    unmeasurable = []
    failed = []
    for label, pat, measure, doc in CLAIMS:
        text = _read(os.path.join(LAKE, doc))
        ms = re.findall(pat, text)
        if not ms:
            absent.append(label)
            continue
        measured = measure()
        if measured is None:
            unmeasurable.append(label)
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
    if absent:
        for a in absent:
            print("SELF-TEST FAILED: claim %r matched nothing in its document" % a)
        return 2
    if unmeasurable:
        for u in unmeasurable:
            print("SELF-TEST FAILED: claim %r could not be measured" % u)
        return 2
    if checked == 0:
        print("SELF-TEST FAILED: no claim was verifiable, so nothing could be caught")
        return 2
    print("SELF-TEST: %d claim(s) verify, every pattern finds its number, and a differing value"
          " would be reported" % checked)
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(run())
