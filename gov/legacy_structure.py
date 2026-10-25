# -*- coding: utf-8 -*-
"""查看旧库依赖图的关键结构：最高层文件、枢纽文件、孤岛主题。

控制台是 GBK，直接 print 中文会崩，所以统一转 ASCII 再输出。
"""
import io
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
G = os.path.join(ZERO, "gov", "legacy-graph.json")


def asc(s):
    return "".join(c if ord(c) < 128 else "?" for c in s)


def main():
    d = json.load(io.open(G, encoding="utf-8"))
    nodes, rank, indeg = d["nodes"], d["rank"], d["indegree"]

    print("=" * 70)
    print("A. 依赖最深的文件（第 8-10 层）")
    print("=" * 70)
    for r in sorted(set(rank.values()), reverse=True):
        if r < 8:
            continue
        ms = sorted(m for m in rank if rank[m] == r)
        print("\n-- layer %d (%d files) --" % (r, len(ms)))
        for m in ms:
            nd = nodes[m]
            print("   %-46s %4d lines, %3d decls" % (m, nd["n_lines"], nd["n_decls"]))

    print()
    print("=" * 70)
    print("B. 被依赖最多的枢纽文件（入度 top 15）")
    print("=" * 70)
    for m in sorted(indeg, key=lambda x: -indeg[x])[:15]:
        nd = nodes[m]
        print("   %-46s in=%3d  %4d lines" % (m, indeg[m], nd["n_lines"]))
        print("      topic: %s" % asc(nd["topic"])[:100])

    print()
    print("=" * 70)
    print("C. 孤岛文件的主题分布（124 个，抽样 20）")
    print("=" * 70)
    for m in d["islands"][:20]:
        print("   %-46s %s" % (m, asc(nodes[m]["topic"])[:70]))

    print()
    print("=" * 70)
    print("D. 规模分布")
    print("=" * 70)
    sizes = sorted(((n["n_lines"], m) for m, n in nodes.items()), reverse=True)
    print("   最大的 8 个文件:")
    for ln, m in sizes[:8]:
        print("      %-44s %5d lines" % (m, ln))
    print("   最小的 5 个文件:")
    for ln, m in sizes[-5:]:
        print("      %-44s %5d lines" % (m, ln))

    print()
    print("=" * 70)
    print("E. 超过 500 行预算的文件（zero 的预算）")
    print("=" * 70)
    over = [(ln, m) for ln, m in sizes if ln > 500]
    print("   数量:", len(over))
    for ln, m in over[:15]:
        print("      %-44s %5d lines" % (m, ln))
    return 0


if __name__ == "__main__":
    sys.exit(main())
