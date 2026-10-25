# -*- coding: utf-8 -*-
"""验证空壳扫描器本身有效：用已知有问题的 Cv00 exec_stmt 做阳性对照。

如果一个扫描器报「0 个问题」，必须先证明它能抓到已知的问题，
否则「0」可能只是「没扫到」。这是本项目反复强调的反应性测试原则。
"""
import io
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ZERO, "gov", "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

WILD = re.compile(r"^\s*\|\s*_\s*(?::[^=]*)?=>\s*(.+)$", re.M)
NOOP = re.compile(r"^\.\s*(normal|ok|success|pure|skip|nil|none|id)\b|"
                  r"\bpure\b|\bskip\b|\bnoop\b", re.I)

# 已知有问题的文件（LvFormal 的 Cv00）
CANDIDATES = [
    os.path.join(ZERO, "Lattice", "LvFormal", "Theory", "Cv00Lang.lean"),
    os.path.join(ZERO, "Lattice", "LvFormal", "Theory", "Cv00Memory.lean"),
]

print("阳性对照：已知的 Cv00 exec_stmt 空壳")
print("=" * 60)
found_any = False
for p in CANDIDATES:
    if not os.path.exists(p):
        print("  不存在:", p)
        continue
    s = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
    hits = list(WILD.finditer(s))
    print("\n%s : 通配分支 %d 处" % (os.path.basename(p), len(hits)))
    for m in hits[:12]:
        rhs = m.group(1).strip()
        line = s[:m.start()].count("\n") + 1
        kind = "A_noop" if NOOP.search(rhs) else "other"
        if kind == "A_noop":
            found_any = True
        print("   L%-5d [%-7s] %s" % (line, kind, rhs[:70]))

print()
print("=" * 60)
print("阳性对照结果:", "✅ 扫描器能抓到 A 类空壳" if found_any else "❌ 扫描器抓不到，需修正")
