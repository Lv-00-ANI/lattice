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
    ("N4 apostrophes in the kernel",
     [r"N4 撇号 \| \*\*(\d+)\*\*",
      r"撇号名 \| \*\*(\d+)\*\*"]),
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
    # had been transposed and nothing compared this row across documents. The pattern captures the
    # whole four-or-more-element sequence so a transposition inside it is visible.
    ("layer split Core/Lift/Geo/Lib",
     [r"17\s*/\s*(\d+)\s*/\s*(\d+)\s*/\s*605"]),
]

# Measurements that capture SEVERAL numbers at once: the tuple must be identical everywhere.
# Same idea as PAIRS, but the comparison is on the whole tuple rather than one captured group.
TUPLES = [
    ("layer split (ordered)", r"17\s*/\s*(\d+)\s*/\s*(\d+)\s*/\s*(\d+)"),
]

def check(docs_dir, verbose=True):
    """Return the number of contradictions found in the .md files of `docs_dir`."""
    docs = [f for f in os.listdir(docs_dir) if f.endswith(".md")]
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
        ok = len(values) <= 1
        if verbose:
            print("%-34s %-22s %s"
                  % (label, "%d in %d docs" % (len(found), len({f[0] for f in found})),
                     "ok" if ok else "*** CONTRADICTION: %s ***" % values))
        if not ok:
            bad += 1
            if verbose:
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
        ok = len(values) <= 1
        if verbose:
            print("%-34s %-22s %s"
                  % (label, "%d in %d docs" % (len(found), len({f[0] for f in found})),
                     "ok" if ok else "*** CONTRADICTION: %s ***" % values))
        if not ok:
            bad += 1
            if verbose:
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


def self_test():
    """Plant one scalar contradiction and one transposition; both must be reported."""
    failures = []
    tmp = _scratch()
    try:
        # 1. a scalar contradiction: two docs disagree on the module count
        _write(tmp, "a.md", "| Lean 模块 | 774 | audit |\n")
        _write(tmp, "b.md", "| Lean 模块 | 773 | audit |\n")
        if check(tmp, verbose=False) == 0:
            failures.append("a scalar contradiction was not caught")

        # 2. a transposition inside the layer split: every number plausible, the order wrong
        _write(tmp, "a.md", "层文件数 17 / 49 / 85 / 605\n")
        _write(tmp, "b.md", "层文件数 17 / 79 / 83 / 605\n")
        if check(tmp, verbose=False) == 0:
            failures.append("a transposition inside the layer split was not caught")

        # 3. agreement must pass, or the checker is useless
        _write(tmp, "a.md", "层文件数 17 / 49 / 85 / 605\n| Lean 模块 | 774 |\n")
        _write(tmp, "b.md", "层文件数 17 / 49 / 85 / 605\n| Lean 模块 | 774 |\n")
        if check(tmp, verbose=False) != 0:
            failures.append("agreeing documents were reported as contradicting")
    finally:
        _cleanup(tmp)

    if failures:
        for f in failures:
            print("SELF-TEST FAILED: %s" % f)
        return 2
    print("SELF-TEST: scalar contradictions and transpositions both caught; agreement passes")
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
