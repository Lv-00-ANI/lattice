# -*- coding: utf-8 -*-
"""给孤岛分类器加第五类：「顶层结论」。

## 问题

`geo_compile_preserves`（T1 的载体）、`reversibility_depends_on_representation`
被归为「真孤岛」——但它们是**顶层定理**：没有人引用它们，
这正是顶层定理的特征（它们是端点，不是中间件）。

## 判据

顶层结论的特征：
1. 位于 `Compile.lean` / `Exact.lean` / `EndToEnd.lean` / `Loop*.lean` / `QualityBridge.lean`
   这类**结论文件**中
2. 或名字含 `preserves` / `converges` / `exact` / `equiv` / `sound` / `terminates`
3. 或被 `Zero/Proofs/*.md` 的靶定理章节点名（已有「设计文档引用」覆盖）

另加一类：「反例 / 边界记录」——位于 `Counterexample.lean` / `Check.lean` / `RepairQuality.lean`，
它们的存在意义是记录「什么行不通」。
"""
import io
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

LAYERS = {
    "Core": "Lattice/Core",
    "Lift": "Lattice/Lift",
    "Lib": "Lattice/Lib",
    "Geo": "Lattice/Geo",
    "Slots": "Lattice/Slots",
}

DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|@\[([^\]]*)\]\s*)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z0-9_']+)", re.M)
TOKEN = re.compile(r"[A-Za-z0-9_']+")

FEATURE_SUFFIX = ("_iff", "_eq", "_le", "_lt", "_ne", "_zero", "_one", "_nonneg", "_pos")

# 结论文件：这些文件里的定理是端点，不被引用是正常的
CONCLUSION_FILES = {"Compile.lean", "Exact.lean", "EndToEnd.lean", "L1L2.lean",
                    "Loop.lean", "LoopPerp.lean", "QualityBridge.lean", "PenaltyEmbedding.lean",
                    "SymbolToWeight.lean", "Extraction.lean"}

# 边界记录：这些文件的意义是记录反例与失败
BOUNDARY_FILES = {"Counterexample.lean", "Check.lean", "RepairQuality.lean", "Repair.lean"}

# 顶层结论的名字特征
CONCLUSION_NAMES = ("preserves", "converges", "exact", "equiv", "sound", "terminates",
                    "progress", "spectrum", "separates", "not_injective", "impossible")


def lean_files():
    for layer, rel in LAYERS.items():
        base = os.path.join(ZERO, *rel.split("/"))
        if not os.path.isdir(base):
            if os.path.isfile(base + ".lean"):
                yield layer, base + ".lean", rel.split("/")[-1] + ".lean"
            continue
        for root, dirs, fs in os.walk(base):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for f in sorted(fs):
                if f.endswith(".lean"):
                    p = os.path.join(root, f)
                    yield layer, p, os.path.relpath(p, base).replace("\\", "/")


def doc_text():
    out = []
    for d in ("Lattice/Proofs", "_archive"):
        base = os.path.join(ZERO, *d.split("/"))
        for root, dirs, fs in os.walk(base):
            for f in fs:
                if f.endswith(".md"):
                    try:
                        out.append(io.open(os.path.join(root, f), encoding="utf-8",
                                           errors="replace").read())
                    except OSError:
                        pass
    return "\n".join(out)


def main():
    texts = {}
    decls = []
    for layer, path, name in lean_files():
        src = strip_comments(io.open(path, "rb").read().decode("utf-8", "replace"))
        texts[(layer, name)] = src
        for attrs, kind, d in DECL.findall(src):
            decls.append((layer, name, kind, d, attrs))

    alltok = defaultdict(int)
    for src in texts.values():
        for t in set(TOKEN.findall(src)):
            alltok[t] += 1

    docs = doc_text()

    buckets = defaultdict(list)
    for layer, name, kind, d, attrs in decls:
        if kind not in ("theorem", "lemma") or alltok[d] > 1:
            continue
        base = name.split("/")[-1]
        if "simp" in attrs:
            buckets["simp 隐式消费"].append((layer, name, d))
        elif base in CONCLUSION_FILES:
            buckets["顶层结论（端点，不被引用是正常的）"].append((layer, name, d))
        elif base in BOUNDARY_FILES:
            buckets["边界记录（反例/失败）"].append((layer, name, d))
        elif d.endswith(FEATURE_SUFFIX):
            buckets["特征引理（面向使用者）"].append((layer, name, d))
        elif d in docs:
            buckets["设计文档引用"].append((layer, name, d))
        elif any(k in d for k in CONCLUSION_NAMES):
            buckets["顶层结论（端点，不被引用是正常的）"].append((layer, name, d))
        else:
            buckets["真孤岛"].append((layer, name, d))

    order = ["顶层结论（端点，不被引用是正常的）", "边界记录（反例/失败）",
             "simp 隐式消费", "特征引理（面向使用者）", "设计文档引用", "真孤岛"]

    total = sum(len(v) for v in buckets.values())
    print("=" * 74)
    print("无消费者定理分类（共 %d 条）" % total)
    print("=" * 74)
    for k in order:
        print("  %-38s %3d" % (k, len(buckets[k])))

    lines = ["# 无消费者定理的分类", "",
             "> 由 `gov/classify_orphans.py` 生成。", "",
             "审计器报「token 计数 = 1」，即整个项目里这个名字只在定义处出现。",
             "但**无消费者不等于无价值**。本文件按六类分拣。", "",
             "## 一、汇总", "",
             "| 类别 | 数量 | 说明 |", "|:--|--:|:--|"]
    DESC = {
        "顶层结论（端点，不被引用是正常的）": "四条靶定理及其直接推论，是链的**端点**而非中间件",
        "边界记录（反例/失败）": "意义在于记录「什么行不通」，不会被正面使用",
        "simp 隐式消费": "带 `@[simp]`，通过 simp 集被隐式使用",
        "特征引理（面向使用者）": "名字以 `_iff`/`_eq`/`_le` 结尾，面向 API 使用者",
        "设计文档引用": "在 `Zero/Proofs/` 或 `_archive/` 中被提及",
        "真孤岛": "无任何正当理由",
    }
    for k in order:
        lines.append("| %s | %d | %s |" % (k, len(buckets[k]), DESC[k]))
    lines += ["| 合计 | %d | |" % total, ""]

    for k in order:
        lines += ["## " + k, "", DESC[k], ""]
        if not buckets[k]:
            lines += ["（无）", ""]
            continue
        lines += ["| 层 | 文件 | 定理 |", "|:--|:--|:--|"]
        for layer, name, d in sorted(buckets[k]):
            lines.append("| %s | `%s` | `%s` |" % (layer, name, d))
        lines.append("")

    out = os.path.join(ZERO, "_archive", "ORPHANS.md")
    io.open(out, "w", encoding="utf-8", newline="\n").write("\n".join(lines))
    print()
    print("已写:", os.path.relpath(out, ZERO))
    return 0


if __name__ == "__main__":
    sys.exit(main())
