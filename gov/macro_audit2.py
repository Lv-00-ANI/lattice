# -*- coding: utf-8 -*-
"""宏观认知 v2：工作区已变化，重新完整测量。

## 与上一轮的区别

上一轮 Geo 是 12 个文件，现在是 28 个。新增的 Semantic / Engine / Pipeline /
Compile / Extract / Loop / Invariant / Synthesis / Initialise / Rules / QualityBridge
恰好对应目标里的缺口 G5（符号引擎）与 G3（闭环）。

所以必须重新测，不能引用上一轮的结论。

## 输出

1. 每个文件的定理清单
2. 目标九分句的重新判定
3. 关键定义的实际形态（Engine / Semantic / Pipeline）
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

THM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)
DEF = re.compile(r"^\s*(?:noncomputable\s+)?(?:def|abbrev|structure|inductive)\s+([A-Za-z0-9_']+)")


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def scan_dir(d):
    total_t = total_d = total_l = 0
    rows = []
    for f in sorted(os.listdir(d)):
        if not f.endswith(".lean"):
            continue
        p = os.path.join(d, f)
        s = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
        thms = THM.findall(s)
        defs = DEF.findall(s)
        n_l = s.count("\n") + 1
        total_t += len(thms)
        total_d += len(defs)
        total_l += n_l
        rows.append((f, n_l, thms, defs))
    return rows, total_t, total_d, total_l


def main():
    geo = os.path.join(ZERO, "Lattice", "Geo")
    rows, tt, td, tl = scan_dir(geo)

    print("=" * 80)
    print("Lattice/Geo/ 全量清单   （%d 个文件, %d 行, %d 定理, %d 定义）" % (len(rows), tl, tt, td))
    print("=" * 80)
    for f, n_l, thms, defs in rows:
        print("\n%-28s %4d 行  定理%-2d 定义%-2d" % (asc(f), n_l, len(thms), len(defs)))
        if defs:
            print("   定义: %s" % asc(", ".join(defs[:8]))[:110])
        if thms:
            print("   定理: %s" % asc(", ".join(thms[:8]))[:110])
    return 0


if __name__ == "__main__":
    sys.exit(main())
