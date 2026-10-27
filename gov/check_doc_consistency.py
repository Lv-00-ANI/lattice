"""A guard that catches DOCUMENT SELF-CONTRADICTION: the same measurement stated twice with
different numbers.

The three contradictions fixed this round (apostrophes 60 vs 3, oversized files 8 vs 10, registry
42 vs 43) all had one cause: a measurement was written down in two places and only one place was
updated. Individual numbers being right is not enough; the DOCUMENT must be internally consistent.

This checker looks for a small set of measurements that the documents state more than once and
verifies the copies agree. It is deliberately narrow: a general "find contradictions" checker is
not possible, but "these specific numbers must appear with one value" is.

## Two kinds of measurement

`PAIRS` compares ONE captured number across documents.

`TUPLES` compares a SEQUENCE of numbers as a single value, because a transposition inside a sequence
is invisible to a per-number check. Round 131 found DELIVERY.md reporting the layer split as
17 / 79 / 83 / 605 while two other documents and the tree said 17 / 49 / 85 / 605 -- every element
was a plausible number, and only the ORDER was wrong.

## It must be able to fail

`--self-test` plants each kind of contradiction in a temporary directory and asserts the checker
reports it.
"""
import io
import os
import re
import sys
import tempfile

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))

# (label, [regexes that each capture ONE number for the same measurement])
PAIRS = [
    # Two formats, because the two documents present the same fact differently: CONVENTIONS uses a
    # space-aligned table row (`撇号名   **3**`), COMPLETENESS-AUDIT puts it inline (`N4 撇号违规 **3**`).
    # The old patterns required a `|` in both and matched NEITHER, so this measurement was dead.
    ("N4 apostrophes in the kernel",
     [r"N4 撇号违规 \*\*(\d+)\*\*",
      r"撇号名\s+\*\*(\d+)\*\*"]),
    ("files over 60 declarations",
     [r"超 60 声明的文件（(\d+) 个）",
      r"### 7\.3 F1 超 60 声明：(\d+) 个文件",
      r"超 60 声明的文件：(\d+) 个"]),
    ("registered gate checks",
     [r"注册了 \*\*(\d+) 项\*\*"]),
    ("Lean module count",
     [r"\| Lean 模块 \| (\d+) \|"]),

    ("registered checks (narrative)", [r"注册了 \*\*(\d+) 项\*\*", r"(\d+) 项检查"]),
    ("oversized files (>60 decls)", [r"超 60 声明的文件：?(\d+) 个", r"F1 超 60 声明：?(\d+) 个"]),
    ("theorem count",
     [r"\| 定理 / 引理 \| ([\d,]+) \|"]),

    # Round 132. Round 131 found DELIVERY.md reporting the layer split as 17 / 79 / 83 / 605 while
    # README and STATE-FINAL both said 17 / 49 / 85 / 605 and the tree said the latter. Two numbers
    # had been transposed and nothing compared this row across documents.
    #
    # Round 167: the pattern then hardcoded `17` as the FIRST element, and Core grew to 18 -- so it
    # matched nothing at all and this measurement silently tested nothing. Anchoring on the LABEL
    # instead of on a value is what keeps it alive as the numbers move.
    ("layer split Core/Lift/Geo/Lib",
     [r"Core\s*/\s*Lift[^|\n]*\|\s*(\d+)"]),
]

# Measurements that capture SEVERAL numbers at once: the tuple must be identical everywhere.
# Same idea as PAIRS, but the comparison is on the whole tuple rather than one captured group.
TUPLES = [
    # Anchored on the label for the same reason: a literal first element dies as soon as that layer's
    # file count changes, and a check that matches nothing is worse than no check.
    ("layer split (ordered)",
     r"Core\s*/\s*Lift[^|\n]*\|\s*(\d+)\s*/\s*(\d+)\s*/\s*(\d+)\s*/\s*(\d+)"),
]

#: Documents FROZEN at the time they were written. Their numbers describe the tree THEN, so comparing
#: them against today's tree is a category error -- the objective's own rule is that `ROADMAP-v3..v11`
#: and `archive/` are history and must not be updated.
#:
#: Round 167: without this list the repaired layer-split check reported a "contradiction" against
#: `ROADMAP-v10.md`'s `16 / 35 / 65 / 588`, which was correct when it was written. Excluding them is
#: not weakening the check: a frozen document that DID claim to describe today would be the bug, and
#: that is what `STATE-2026-10.md` vs `STATE-FINAL.md` is for.
FROZEN = re.compile(r"^ROADMAP-v\d+\.md$")


def check(docs_dir, verbose=True):
    """Return the number of contradictions found in the .md files of `docs_dir`."""
    docs = [f for f in os.listdir(docs_dir)
            if f.endswith(".md") and not FROZEN.match(f)]
    if verbose:
        print("%-34s %-22s %s" % ("measurement", "occurrences", "verdict"))
        print("-" * 78)
    bad = 0

    def read(d):
        return io.open(os.path.join(docs_dir, d), encoding="utf-8", errors="replace").read()

    for label, pats in PAIRS:
        found = []
        for d in docs:
            t = read(d)
            for pat in pats:
                for m in re.finditer(pat, t):
                    found.append((d, m.group(1), m.start()))
        values = sorted({f[1] for f in found})
        # ZERO MATCHES IS A FAILURE, not a pass.
        #
        # Both layer-split patterns below hardcoded `17` as the first element. Core grew to 18, so
        # they matched nothing and this checker printed "0 in 0 docs ok" for two whole measurements --
        # the layer split was checked by NOTHING while the report said ok. A pattern that has drifted
        # away from the documents must be as loud as a contradiction: a measurement nobody can find is
        # not a measurement that agrees.
        vacuous = len(found) == 0
        ok = (len(values) <= 1) and not vacuous
        if verbose:
            verdict = ("*** PATTERN DRIFT: matched nothing ***" if vacuous
                       else "ok" if ok else "*** CONTRADICTION: %s ***" % values)
            print("%-34s %-22s %s"
                  % (label, "%d in %d docs" % (len(found), len({f[0] for f in found})), verdict))
        if not ok:
            bad += 1
            if verbose and not vacuous:
                for d, v, pos in found:
                    ln = read(d).count("\n", 0, pos) + 1
                    print("      %-24s line %-5d value %s" % (d, ln, v))

    if verbose:
        print()
    for label, pat in TUPLES:
        found = []
        for d in docs:
            t = read(d)
            for m in re.finditer(pat, t):
                found.append((d, m.groups(), m.start()))
        values = sorted({f[1] for f in found})
        vacuous = len(found) == 0
        ok = (len(values) <= 1) and not vacuous
        if verbose:
            verdict = ("*** PATTERN DRIFT: matched nothing ***" if vacuous
                       else "ok" if ok else "*** CONTRADICTION: %s ***" % values)
            print("%-34s %-22s %s"
                  % (label, "%d in %d docs" % (len(found), len({f[0] for f in found})), verdict))
        if not ok:
            bad += 1
            if verbose and not vacuous:
                for d, v, pos in found:
                    ln = read(d).count("\n", 0, pos) + 1
                    print("      %-24s line %-5d value %s" % (d, ln, "/".join(v)))
    return bad


def _write(d, name, content):
    with io.open(os.path.join(d, name), "w", encoding="utf-8") as f:
        f.write(content)


def _scratch():
    """A writable scratch directory. `tempfile` is denied by the sandbox on this host."""
    d = os.path.join(HERE, ".selftest-scratch")
    if os.path.isdir(d):
        import shutil
        shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d, exist_ok=True)
    return d


def _cleanup(d):
    import shutil
    shutil.rmtree(d, ignore_errors=True)


#: A document fragment that satisfies EVERY pattern in PAIRS and TUPLES. The self-test needs this
#: because a pattern that matches nothing is now a failure, so a partial fixture would report drift
#: for reasons unrelated to what the test is checking.
def _complete(module=774, layer="18 / 55 / 92 / 605", thms="8,000"):
    return ("| Lean 模块 | %d | audit |\n"
            "| 定理 / 引理 | %s | audit |\n"
            "| 层文件数 Core/Lift/Geo/Lib | %s | audit |\n"
            "N4 撇号违规 **3**\n"
            "撇号名   **3**\n"
            "超 60 声明的文件：2 个\n"
            "注册了 **56 项**\n" % (module, thms, layer))


def self_test():
    """Four cases: agreement passes; scalar contradiction, transposition and PATTERN DRIFT all fail."""
    failures = []
    tmp = _scratch()
    try:
        # 0. agreement must pass, or the checker is useless
        _write(tmp, "a.md", _complete())
        _write(tmp, "b.md", _complete())
        if check(tmp, verbose=False) != 0:
            failures.append("agreeing documents were reported as contradicting")

        # 1. a scalar contradiction: two docs disagree on the module count
        _write(tmp, "a.md", _complete(module=774))
        _write(tmp, "b.md", _complete(module=773))
        if check(tmp, verbose=False) == 0:
            failures.append("a scalar contradiction was not caught")

        # 2. a transposition inside the layer split: every number plausible, the order wrong
        _write(tmp, "a.md", _complete(layer="17 / 49 / 85 / 605"))
        _write(tmp, "b.md", _complete(layer="17 / 79 / 83 / 605"))
        if check(tmp, verbose=False) == 0:
            failures.append("a transposition inside the layer split was not caught")

        # 3. PATTERN DRIFT: the documents agree with each other but the row is GONE, so the
        #    measurement silently tests nothing. This is the case that made two whole checks dead
        #    while the report said "ok" -- it must now fail.
        _write(tmp, "a.md", "| Lean 模块 | 774 | audit |\n")
        _write(tmp, "b.md", "| Lean 模块 | 774 | audit |\n")
        if check(tmp, verbose=False) == 0:
            failures.append("a vanished measurement (pattern drift) was not caught")
    finally:
        _cleanup(tmp)

    if failures:
        for f in failures:
            print("SELF-TEST FAILED: %s" % f)
        return 2
    print("SELF-TEST: agreement passes; scalar contradiction, transposition and pattern drift all caught")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    bad = check(LAKE)
    print()
    if bad:
        print("DOCUMENT CONSISTENCY: %d contradiction(s)" % bad)
        sys.exit(1)
    print("DOCUMENT CONSISTENCY: every repeated measurement agrees")
