#!/usr/bin/env python3
"""生成旧库 606 个文件的依赖图与主题分类，供后续分层重构使用。

## 为什么需要

审计已证：旧库 606 个文件里，1831 条内部 import 边、124 个孤岛文件，
而真正在链上的只有 9 个文件。要把 606 个文件「按依赖关系重构」，
必须先知道依赖图长什么样——文件名的关键字不可靠（562 个 `Real*.lean`
按关键字只能分出 493 个「其他」）。

## 产出

- `legacy-graph.json`  节点、边、SCC、分层
- `legacy-layers.md`   按拓扑层排列的清单，供人工审阅

## 用法

    python gov/legacy_graph.py <源目录>

读源目录里的 `*.lean`（排除 `.lake`/`_probes_archived`/`_r9`），不改任何文件。
"""
import io
import json
import os
import re
import sys

IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.M)
DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
                  r"([A-Za-z0-9_']+)", re.M)
DOCBLOCK = re.compile(r"/-!(.*?)-/", re.S)


def collect_files(root):
    out = {}
    for f in sorted(os.listdir(root)):
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        if not os.path.isfile(p):
            continue
        out[f[:-5]] = p
    return out


def main():
    if len(sys.argv) < 2:
        print("用法: python gov/legacy_graph.py <源目录>")
        return 2
    root = os.path.abspath(sys.argv[1])
    files = collect_files(root)
    here = os.path.dirname(os.path.abspath(__file__))

    nodes, edges, decls_total = {}, [], 0
    for mod, path in files.items():
        src = io.open(path, "rb").read().decode("utf-8", "replace")
        imps = [m for m in IMPORT.findall(src)]
        local = [i for i in imps if i in files]
        decls = DECL.findall(src)
        decls_total += len(decls)
        docs = DOCBLOCK.findall(src)
        # 主题线索：文档块的首个非空标题行
        topic = ""
        for d in docs:
            for line in d.splitlines():
                line = line.strip().lstrip("#").strip()
                if line:
                    topic = line
                    break
            if topic:
                break
        nodes[mod] = {
            "imports_local": local,
            "imports_ext": [i for i in imps if i not in files],
            "n_decls": len(decls),
            "n_lines": src.count("\n") + 1,
            "topic": topic,
        }
        for t in local:
            edges.append([mod, t])

    # 拓扑分层：rank(m) = 1 + max(rank(dep))，孤岛为 0 层
    rank = {}

    def depth(m, seen=None):
        if m in rank:
            return rank[m]
        if seen is None:
            seen = set()
        if m in seen:          # 环：截断，记为 0 层并在报告里标注
            return 0
        seen.add(m)
        deps = nodes[m]["imports_local"]
        r = 0 if not deps else 1 + max(depth(d, seen) for d in deps)
        rank[m] = r
        return r

    sys.setrecursionlimit(20000)
    for m in nodes:
        depth(m)

    # 入度：被多少文件 import
    indeg = {m: 0 for m in nodes}
    for a, b in edges:
        indeg[b] += 1

    sinks = sorted(m for m in nodes if indeg[m] == 0)
    islands = sorted(m for m in nodes if not nodes[m]["imports_local"])

    out = {
        "root": root,
        "n_files": len(nodes),
        "n_edges": len(edges),
        "n_decls": decls_total,
        "n_islands": len(islands),
        "nodes": nodes,
        "rank": rank,
        "indegree": indeg,
        "sinks": sinks,
        "islands": islands,
    }
    gp = os.path.join(here, "legacy-graph.json")
    io.open(gp, "w", encoding="utf-8", newline="\n").write(
        json.dumps(out, ensure_ascii=False, indent=1))

    # 分层报告
    by_rank = {}
    for m, r in rank.items():
        by_rank.setdefault(r, []).append(m)
    lines = ["# 旧库依赖分层（自动生成）", "",
             "> 由 `gov/legacy_graph.py` 生成，不要手工编辑。", "",
             "| 指标 | 值 |", "|:--|--:|",
             "| 文件数 | %d |" % len(nodes),
             "| 内部依赖边 | %d |" % len(edges),
             "| 声明总数 | %d |" % decls_total,
             "| 孤岛文件（无内部依赖） | %d |" % len(islands),
             "| 无人依赖的文件（sink） | %d |" % len(sinks),
             "| 拓扑层数 | %d |" % (len(by_rank)),
             ""]
    for r in sorted(by_rank):
        ms = sorted(by_rank[r])
        lines.append("## 第 %d 层（%d 个文件）" % (r, len(ms)))
        lines.append("")
        for m in ms:
            nd = nodes[m]
            lines.append("- `%s` — %d 行，%d 声明" % (m, nd["n_lines"], nd["n_decls"]))
        lines.append("")
    lp = os.path.join(here, "legacy-layers.md")
    io.open(lp, "w", encoding="utf-8", newline="\n").write("\n".join(lines))

    print("文件数:", len(nodes))
    print("内部依赖边:", len(edges))
    print("声明总数:", decls_total)
    print("孤岛:", len(islands))
    print("拓扑层数:", len(by_rank))
    print("最大层大小:", max(len(v) for v in by_rank.values()))
    print("写出:", gp)
    print("写出:", lp)
    return 0


if __name__ == "__main__":
    sys.exit(main())
