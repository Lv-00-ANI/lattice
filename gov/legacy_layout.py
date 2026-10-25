#!/usr/bin/env python3
"""A 阶段：把旧库 606 个文件按实测依赖层分配到目录，并生成可执行的搬迁计划。

## 设计要点

Lean 的模块名由**文件路径**决定：`Zero/Legacy/L03/X.lean` 的模块名是 `Zero.Legacy.L03.X`。
所以按层分目录，必须同步改写所有 `import Zero.Legacy.X` -> `import Zero.Legacy.LNN.X`。

## 为什么是 11 层而不是 3 个语义目录

按语义分类需要判断每个文件「是什么」，而 493 个文件按文件名分不出类（实测）。
按依赖分层不需要判断语义——它就是图论结果，且**保证 import 方向永远向下**，
这正好满足 zero 的分层纪律（I4 的精神：只允许向后依赖）。

## 产出的三层映射

依赖层（0-10）→ 目录名（可读的语义名）：

  L00-Base     第 0 层  仅依赖 Mathlib 的孤岛，无内部依赖
  L01-Atoms    第 1-2 层  基础定义（数值、编码、激活等）
  L02-Struct   第 3-4 层  结构层（约束、逻辑、张量形状）
  L03-Models   第 5-7 层  模型层（网络、训练、优化）
  L04-Bridge   第 8-9 层  桥接层（编译、提取、端到端）
  L05-Top      第 10 层  收束层（最终结论）

## 用法

    python gov/legacy_layout.py --plan      # 只打印计划，不动文件
    python gov/legacy_layout.py --apply     # 执行搬迁 + 改写 import
"""
import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
GRAPH = os.path.join(HERE, "legacy-graph.json")

# 依赖层 -> 目录
LAYOUT = [
    (range(0, 1), "L00-Base"),
    (range(1, 3), "L01-Atoms"),
    (range(3, 5), "L02-Struct"),
    (range(5, 8), "L03-Models"),
    (range(8, 10), "L04-Bridge"),
    (range(10, 99), "L05-Top"),
]

IMPORT_LEGACY = re.compile(r"^import\s+Zero\.Legacy\.([A-Za-z0-9_']+)\s*$", re.M)


def dir_of_rank(r):
    for rng, name in LAYOUT:
        if r in rng:
            return name
    return "L05-Top"


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    apply = "--apply" in sys.argv
    d = json.load(io.open(GRAPH, encoding="utf-8"))
    rank = d["rank"]

    legacy_dir = os.path.join(ZERO, "Lattice", "Legacy")
    present = {f[:-5] for f in os.listdir(legacy_dir) if f.endswith(".lean")} \
        if os.path.isdir(legacy_dir) else set()

    plan = {}          # module -> target dir
    for mod, r in rank.items():
        if mod in present:
            plan[mod] = dir_of_rank(r)

    by_dir = {}
    for mod, tgt in plan.items():
        by_dir.setdefault(tgt, []).append(mod)

    print("=" * 70)
    print("A 阶段搬迁计划%s" % (" (apply)" if apply else " (dry-run)"))
    print("=" * 70)
    for rng, name in LAYOUT:
        ms = sorted(by_dir.get(name, []))
        print("  %-12s %3d files   (rank %s)" % (name, len(ms), name[1:3].lstrip("0")))
    total = sum(len(v) for v in by_dir.values())
    print("  %-12s %3d files" % ("TOTAL", total))

    missing = [m for m in rank if m not in present]
    if missing:
        print("\n  注意: 图中 %d 个模块不在 Legacy 目录（可能已被隔离）" % len(missing))

    if not apply:
        print("\n干跑完成。用 --apply 执行。")
        return 0

    # --- 执行 ---
    moved = 0
    for mod, tgt in plan.items():
        src = os.path.join(legacy_dir, mod + ".lean")
        if not os.path.exists(src):
            continue
        dst_dir = os.path.join(legacy_dir, tgt)
        os.makedirs(dst_dir, exist_ok=True)
        dst = os.path.join(dst_dir, mod + ".lean")
        os.replace(src, dst)
        moved += 1
    print("\n已移动:", moved)

    # 重写 import：所有 Legacy 下的 .lean（含刚移动的）
    mod_to_dir = plan
    rewritten = 0
    for base, _dirs, fs in os.walk(legacy_dir):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            s = io.open(p, encoding="utf-8").read()

            def repl(m):
                name = m.group(1)
                tgt = mod_to_dir.get(name)
                if tgt is None:
                    return m.group(0)          # 指向已被隔离的模块，保持原样待后续处理
                return "import Zero.Legacy.%s.%s" % (tgt, name)

            new = IMPORT_LEGACY.sub(repl, s)
            if new != s:
                io.open(p, "w", encoding="utf-8", newline="\n").write(new)
                rewritten += 1
    print("已改写 import 的文件:", rewritten)
    return 0


if __name__ == "__main__":
    sys.exit(main())
