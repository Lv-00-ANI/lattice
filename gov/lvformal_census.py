#!/usr/bin/env python3
"""独立核实 lvFormal 三副本的 sorry / axiom 普查。

子代理报告 `formal` 0 处 sorry、`lv-merged` 44 处。这是选型的决定性判据，
必须自己测一遍——尤其是"剥离注释"这一步，历史上本项目出过两次误判
（把注释块里的 axiom 当成真的）。

用法：
    python gov/lvformal_census.py <副本目录>
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

SORRY = re.compile(r"\bsorry\b")
ADMIT = re.compile(r"\badmit\b")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_']+)", re.M)
OPAQUE = re.compile(r"^\s*opaque\s+([A-Za-z0-9_']+)", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    if len(sys.argv) < 2:
        print("用法: python gov/lvformal_census.py <副本目录>")
        return 2
    root = sys.argv[1]
    tot = {"files": 0, "lines": 0, "sorry": 0, "admit": 0, "axiom": 0, "opaque": 0}
    offenders = []

    for base, dirs, fs in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            raw = io.open(p, "rb").read().decode("utf-8", "replace")
            src = strip_comments(raw)          # 关键：先剥离注释，与项目既有纪律一致
            n_s = len(SORRY.findall(src))
            n_a = len(ADMIT.findall(src))
            n_x = len(AXIOM.findall(src))
            n_o = len(OPAQUE.findall(src))
            tot["files"] += 1
            tot["lines"] += raw.count("\n") + 1
            tot["sorry"] += n_s
            tot["admit"] += n_a
            tot["axiom"] += n_x
            tot["opaque"] += n_o
            if n_s or n_a or n_x or n_o:
                rel = os.path.relpath(p, root).replace("\\", "/")
                offenders.append((rel, n_s, n_a, n_x, n_o))

    print("=" * 68)
    print("目标目录:", asc(root))
    print("=" * 68)
    print("  .lean 文件      :", tot["files"])
    print("  总行数          :", tot["lines"])
    print("  sorry           :", tot["sorry"])
    print("  admit           :", tot["admit"])
    print("  axiom           :", tot["axiom"])
    print("  opaque          :", tot["opaque"])
    print()
    if offenders:
        print("  --- 含问题的文件 ---")
        for rel, s, a, x, o in offenders:
            print("   %-52s sorry=%d admit=%d axiom=%d opaque=%d" % (asc(rel), s, a, x, o))
    else:
        print("  无任何问题的文件")
    return 0


if __name__ == "__main__":
    sys.exit(main())
