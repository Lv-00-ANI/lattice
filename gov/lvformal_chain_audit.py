#!/usr/bin/env python3
"""目标链关键文件的干净度：lvLang → IR → Cv00 这 8 个文件里有多少逃逸。

## 为什么单独测

整体普查告诉我们 `formal` 有 68 处 admit，但分布在哪里才决定结论。
若这些 admit 全在几何/密码学主题（与目标无关），而编译链本身干净，
那么目标原文「既有已验证编译链」这句话对 **编译链部分** 仍然成立。

## 口径

先剥离注释再统计（复用 gov/tools/sorry_axiom_census.py），
因为本项目历史上两次把注释里的 axiom 当成真 axiom。

用法：
    python gov/lvformal_chain_audit.py
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

HARVEST = os.path.join(ZERO, "..", "_harvest", "lv00")

# 目标链的关键文件（按内容而非文件名找）
CHAIN = [
    "LvDSL.lean", "Ir.lean", "IR.lean", "Compiler.lean", "CompilerCorrectness.lean",
    "Codegen.lean", "CodegenCorrectness.lean", "Cv00Lang.lean", "Cv00Memory.lean",
    "Cv00.lean", "Semantics.lean", "TypeChecker.lean", "TypeSoundness.lean",
]

SORRY = re.compile(r"\bsorry\b")
ADMIT = re.compile(r"\badmit\b")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_']+)", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def find(root, name):
    hits = []
    for base, dirs, fs in os.walk(root):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        if name in fs:
            hits.append(os.path.join(base, name))
    return hits


def main():
    for copy in ("formal", "lv-merged"):
        root = os.path.join(HARVEST, copy)
        if not os.path.isdir(root):
            print("跳过（不存在）:", copy)
            continue
        print("=" * 74)
        print("副本:", copy)
        print("=" * 74)
        print("%-34s %6s %6s %6s %6s" % ("file", "lines", "sorry", "admit", "axiom"))
        print("-" * 74)
        total = [0, 0, 0]
        for name in CHAIN:
            for p in find(root, name):
                raw = io.open(p, "rb").read().decode("utf-8", "replace")
                src = strip_comments(raw)
                s = len(SORRY.findall(src))
                a = len(ADMIT.findall(src))
                x = len(AXIOM.findall(src))
                total[0] += s
                total[1] += a
                total[2] += x
                rel = os.path.relpath(p, root).replace("\\", "/")
                mark = "  <-- 有逃逸" if (s or a or x) else ""
                print("%-34s %6d %6d %6d %6d%s"
                      % (asc(rel[-34:]), raw.count("\n") + 1, s, a, x, mark))
        print("-" * 74)
        print("%-34s %6s %6d %6d %6d" % ("TOTAL", "", total[0], total[1], total[2]))
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
