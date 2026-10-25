# -*- coding: utf-8 -*-
"""检查 Geo 与 Lib/Penalty 这两个新目录的内容与接入状态。

## 要回答

1. 它们各自定义了什么（定理清单）
2. 它们是否被根聚合器 import（若否，则未接入构建，门禁 I7 会说它们没有 olean）
3. 它们与目标的对应关系
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

THM = re.compile(r"^\s*(?:theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)
DEF = re.compile(r"^\s*(?:noncomputable\s+)?(?:def|abbrev|structure|inductive)\s+([A-Za-z0-9_']+)")


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def scan_dir(rel_dir):
    d = os.path.join(ZERO, rel_dir)
    if not os.path.isdir(d):
        print("  (不存在)")
        return
    total_t = total_d = 0
    for f in sorted(os.listdir(d)):
        if not f.endswith(".lean"):
            continue
        p = os.path.join(d, f)
        s = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
        thms = THM.findall(s)
        defs = DEF.findall(s)
        total_t += len(thms)
        total_d += len(defs)
        print("  %-24s %4d 行  定理%-3d 定义%-3d" % (asc(f), s.count("\n") + 1, len(thms), len(defs)))
        if thms:
            print("      定理: %s" % asc(", ".join(thms[:6])))
        if defs:
            print("      定义: %s" % asc(", ".join(defs[:6])))
    print("  --- 合计: 定理 %d, 定义 %d ---" % (total_t, total_d))


def main():
    print("=" * 78)
    print("Lattice/Geo/")
    print("=" * 78)
    scan_dir(os.path.join("Lattice", "Geo"))

    print()
    print("=" * 78)
    print("Lattice/Lib/Penalty/")
    print("=" * 78)
    scan_dir(os.path.join("Lattice", "Lib", "Penalty"))

    print()
    print("=" * 78)
    print("根聚合器接入检查")
    print("=" * 78)
    for root in ("Lattice.lean", "Lattice/Core.lean", "Lattice/Lib.lean", "Lattice/Lift.lean"):
        p = os.path.join(ZERO, root)
        if not os.path.exists(p):
            continue
        s = io.open(p, encoding="utf-8").read()
        imps = re.findall(r"^import\s+(\S+)", s, re.M)
        print("\n  %s (%d 个 import)" % (asc(root), len(imps)))
        for i in imps:
            print("     ", asc(i))
        geo = [i for i in imps if ".Geo" in i]
        pen = [i for i in imps if "Lib.Penalty" in i]
        if root == "Lattice.lean":
            print("     -> Geo 接入:", "是" if geo else "**否**")
            print("     -> Lib.Penalty 接入:", "是" if pen else "**否**")
    return 0


if __name__ == "__main__":
    sys.exit(main())
