"""A guard that catches DOCUMENT SELF-CONTRADICTION: the same measurement stated twice with
different numbers.

The three contradictions fixed this round (apostrophes 60 vs 3, oversized files 8 vs 10, registry
42 vs 43) all had one cause: a measurement was written down in two places and only one place was
updated. Individual numbers being right is not enough; the DOCUMENT must be internally consistent.

This checker looks for a small set of measurements that the documents state more than once and
verifies the copies agree. It is deliberately narrow: a general "find contradictions" checker is
not possible, but "these specific numbers must appear with one value" is.
"""
import io
import os
import re
import sys

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
]

docs = [f for f in os.listdir(LAKE) if f.endswith(".md")]
bad = 0
print("%-34s %-22s %s" % ("measurement", "occurrences", "verdict"))
print("-" * 78)
for label, pats in PAIRS:
    found = []
    for d in docs:
        t = io.open(os.path.join(LAKE, d), encoding="utf-8", errors="replace").read()
        for pat in pats:
            for m in re.finditer(pat, t):
                found.append((d, m.group(1), m.start()))
    values = sorted({f[1] for f in found})
    ok = len(values) <= 1
    print("%-34s %-22s %s" % (label, "%d in %d docs" % (len(found), len({f[0] for f in found})),
                              "ok" if ok else "*** CONTRADICTION: %s ***" % values))
    if not ok:
        bad += 1
        for d, v, pos in found:
            line = io.open(os.path.join(LAKE, d), encoding="utf-8", errors="replace").read()
            ln = line.count("\n", 0, pos) + 1
            print("      %-24s line %-5d value %s" % (d, ln, v))

print()
if bad:
    print("DOCUMENT CONSISTENCY: %d contradiction(s)" % bad)
    sys.exit(1)
print("DOCUMENT CONSISTENCY: every repeated measurement agrees")
