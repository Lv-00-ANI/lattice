# -*- coding: utf-8 -*-
"""核实分层是否真的把高价值文件分到了 Top 层。

干跑结果显示 L05-Top 只有 3 个文件，但依赖图表明第 8-10 层应有 47 个。
差距的原因是：子代理已把一部分文件移走，未移走的集合里 rank 分布不同。

本脚本用**当前实际存在的文件**重算 rank，并打印每层的文件名样本，
以便人工确认分层是否合理（而不是只信数字）。
"""
import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

IMPORT = re.compile(r"^import\s+Zero\.Legacy\.([A-Za-z0-9_']+)\s*$", re.M)
LAYOUT = [(range(0, 1), "L00-Base"), (range(1, 3), "L01-Atoms"), (range(3, 5), "L02-Struct"),
          (range(5, 8), "L03-Models"), (range(8, 10), "L04-Bridge"), (range(10, 99), "L05-Top")]


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def dir_of_rank(r):
    for rng, name in LAYOUT:
        if r in rng:
            return name
    return "L05-Top"


def main():
    legacy = os.path.join(ZERO, "Lattice", "Legacy")
    files = {}
    for base, _d, fs in os.walk(legacy):
        for f in fs:
            if f.endswith(".lean"):
                files[f[:-5]] = os.path.join(base, f)

    deps = {}
    for mod, p in files.items():
        s = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
        deps[mod] = [x for x in IMPORT.findall(s) if x in files]

    rank = {}

    def depth(m, seen=None):
        if m in rank:
            return rank[m]
        if seen is None:
            seen = set()
        if m in seen:
            return 0
        seen.add(m)
        d = deps.get(m, [])
        r = 0 if not d else 1 + max(depth(x, seen) for x in d)
        rank[m] = r
        return r

    sys.setrecursionlimit(20000)
    for m in files:
        depth(m)

    by_dir = {}
    for m, r in rank.items():
        by_dir.setdefault(dir_of_rank(r), []).append((r, m))

    print("=" * 74)
    print("当前实际文件的依赖分层（%d 个文件）" % len(files))
    print("=" * 74)
    for _rng, name in LAYOUT:
        items = sorted(by_dir.get(name, []), reverse=True)
        print("\n%s  —— %d 个文件" % (name, len(items)))
        show = items[:6] + ([("", "...")] if len(items) > 12 else []) + \
               ([items[-3]] if len(items) > 12 else [])
        for r, m in show[:12]:
            if m == "...":
                print("     ...")
            else:
                print("     rank %-2d  %s" % (r, asc(m)))

    print()
    print("=" * 74)
    print("最高的 3 个文件的实际依赖链")
    print("=" * 74)
    top = sorted(rank.items(), key=lambda kv: -kv[1])[:3]
    for m, r in top:
        print("\n%s (rank %d), imports: %s" % (asc(m), r, [asc(x) for x in deps[m][:4]]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
