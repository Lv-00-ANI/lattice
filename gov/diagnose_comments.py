#!/usr/bin/env python3
"""定位并报告注释损坏的确切位置（不改文件，先看清楚）。

I8 报告三个文件有问题：
- `CacheCoherenceTheory.lean`: 嵌套深度 3 未闭合
- `ConstraintModelTheory.lean`: 1 个 `-/` 无匹配开头
- `GeometrySymbolicsTheory.lean`: 嵌套深度 1 未闭合

## 先判断性质

这些是从 Lv-00 迁入的文件。损坏可能有两种来源：
1. **迁移时改 namespace 造成**（我们的 bug）
2. **源文件本来如此**（Lv-00 的问题）

必须对比源文件才能定。本脚本做这个对比。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
SRC = os.path.abspath(os.path.join(ZERO, "..", "_harvest", "lv00", "formal"))

BAD = [
    "Lattice/LvFormal/Theory/CacheCoherenceTheory.lean",
    "Lattice/LvFormal/Theory/ConstraintModelTheory.lean",
    "Lattice/LvFormal/Theory/GeometrySymbolicsTheory.lean",
]


def balance(src):
    depth = 0
    under = 0
    i = 0
    n = len(src)
    while i < n - 1:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i):
            if depth == 0:
                under += 1
            else:
                depth -= 1
            i += 2
        else:
            i += 1
    return depth, under


def main():
    print("=" * 74)
    print("注释平衡对比：迁移后 vs 源文件")
    print("=" * 74)
    for rel in BAD:
        cur = os.path.join(ZERO, rel)
        base = rel.replace("Lattice/LvFormal/", "lvFormal/")
        orig = os.path.join(SRC, base)
        print()
        print(rel.replace("/", os.sep))
        if os.path.exists(cur):
            d, u = balance(io.open(cur, "rb").read().decode("utf-8", "replace"))
            print("  迁移后: depth=%d underflow=%d" % (d, u))
        else:
            print("  迁移后: 文件不存在")
        if os.path.exists(orig):
            d, u = balance(io.open(orig, "rb").read().decode("utf-8", "replace"))
            print("  源文件: depth=%d underflow=%d" % (d, u))
            if d == 0 and u == 0:
                print("  => **源文件是好的，是迁移引入的损坏**")
            else:
                print("  => 源文件本来就有问题")
        else:
            print("  源文件: 不存在（无法对比）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
