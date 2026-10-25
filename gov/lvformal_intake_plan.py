#!/usr/bin/env python3
"""判定 lvFormal 的接入方式，并测算两种方案的冲突面。

## 背景

`_harvest/lv00/formal/` 是**独立包**（有自己的 lakefile.toml、lean-toolchain）。
要接进 `zero/`，有两种做法，冲突面差别很大：

## 方案 P：path 依赖（不改动源码）

在 `zero/lakefile.toml` 加：
    [[require]]
    name = "lvFormal"
    path = "../_harvest/lv00/formal"

优点：一个文件都不用复制；lvFormal 保持独立可构建。
缺点：
  - 它的 lakefile 里有 `[[require]] mathlib git=... rev=v4.14.0`，
    会触发重新解析 → 很可能会去联网拉 mathlib（本项目的已知痛点）
  - 模块名仍是 `lvFormal.Theory.X`，不在 `Zero.*` 命名空间下

## 方案 C：复制源码进来（改路径）

把 `formal/lvFormal/Theory/*.lean` 复制进 `Zero/LvFormal/`，
改写 import，作为 `Zero.LvFormal.*` 模块。

优点：与 Legacy 一致，统一在 `Zero.*` 下；不引入第二个 mathlib 解析。
缺点：需要在 174 个文件里改 import。

## 本脚本做什么

只**测算**，不修改：
  - lvFormal 内部 import 的形态（是 `import lvFormal.X` 还是别的）
  - 有多少文件需要改写
  - 是否依赖 mathlib 之外的东西

用法：
    python gov/lvformal_intake_plan.py
"""
import io
import os
import re
import sys
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
SRC = os.path.abspath(os.path.join(ZERO, "..", "_harvest", "lv00", "formal"))

IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    if not os.path.isdir(SRC):
        print("源目录不存在:", SRC)
        return 1

    files = {}
    for base, dirs, fs in os.walk(SRC):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if f.endswith(".lean"):
                p = os.path.join(base, f)
                rel = os.path.relpath(p, SRC).replace("\\", "/")
                files[rel] = p

    print("=" * 70)
    print("lvFormal 源目录:", asc(SRC))
    print("=" * 70)
    print("  .lean 文件:", len(files))

    # 按顶层目录分
    top = collections.Counter(rel.split("/")[0] if "/" in rel else "(根)" for rel in files)
    print("\n  按顶层目录分布:")
    for k, v in top.most_common():
        print("    %-24s %3d" % (asc(k), v))

    # import 形态
    imports = collections.Counter()
    local_imports = []
    for rel, p in files.items():
        s = io.open(p, "rb").read().decode("utf-8", "replace")
        for m in IMPORT.findall(s):
            imports[m.split(".")[0]] += 1
            if m.startswith("lvFormal"):
                local_imports.append((rel, m))

    print("\n  import 的顶层模块分布（top 12）:")
    for k, v in imports.most_common(12):
        print("    %-26s %4d" % (asc(k), v))

    print("\n  指向 lvFormal 自身的 import 条数:", len(local_imports))
    if local_imports:
        print("  样例:")
        for rel, m in local_imports[:6]:
            print("    %-40s -> %s" % (asc(rel), asc(m)))

    # Theory 子目录（目标链所在）
    theory = [r for r in files if "/Theory/" in r or r.startswith("Theory/")]
    print("\n  Theory/ 下文件数:", len(theory))

    total_lines = 0
    for p in files.values():
        total_lines += io.open(p, "rb").read().decode("utf-8", "replace").count("\n") + 1
    print("  总行数:", total_lines)

    print()
    print("=" * 70)
    print("结论")
    print("=" * 70)
    print("  内部 import 形如 `import lvFormal.X` 时，复制进来需改写为 `import Zero.LvFormal.X`。")
    print("  改写量 = 上述 %d 条（每条约 1 行）。" % len(local_imports))
    print("  非 lvFormal 前缀的 import（如 Mathlib）保持不动。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
