# -*- coding: utf-8 -*-
"""最终的源文件可编译性验证：完全原样，只改 namespace 前缀，open 不动。

## 为什么这个实验是决定性的

在 `Zero/LvFormalProbe/` 里做的对照实验，结果与迁移后的错误**完全一致**：
```
Cv00Memory.lean:111:30  unsolved goals
Cv00Memory.lean:133:26  simp made no progress
... (6 条，行号与源文件原始行号一致)
```

行号 111/133/135/141/143/171 与源文件原始行号完全对应，
说明**我的迁移没有改动这些行的内容**，错误是源文件自带的。

## 本轮做什么

再做一个更强的对照：**完全不动 namespace**，只把 `import lvFormal.X` 换成相对可用的形式，
验证是否 namespace 改不改都一样失败。

方法是把三个文件放进同一个「自包含」命名空间下，用最小的改动让它们互相可见。
若还是同样错误，则无可辩驳地证明是源文件问题。
"""
import io
import os
import re
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
SRC = os.path.join(ZERO, "..", "_harvest", "lv00", "formal", "lvFormal")
DST = os.path.join(ZERO, "Lattice", "LvFormalProbe")
WANT = ["Theory/Cv00Memory.lean", "Theory/Cv00Lang.lean", "Theory/lvLang.lean"]

IMPORT_RE = re.compile(r"^(import\s+)lvFormal\.", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    if os.path.isdir(DST):
        shutil.rmtree(DST)

    print("=" * 76)
    print("实验：最小改动对照")
    print("=" * 76)
    print("规则: 只改 import 前缀 lvFormal. -> Zero.LvFormalProbe.")
    print("      namespace / end / open **全部保持原样**")
    print()

    for rel in WANT:
        src = os.path.join(SRC, rel)
        dst = os.path.join(DST, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(src, dst)
        s = io.open(dst, encoding="utf-8").read()
        s = IMPORT_RE.sub(r"\1Zero.LvFormalProbe.", s)
        io.open(dst, "w", encoding="utf-8", newline="\n").write(s)

        # 报告该文件的 namespace / open 原样
        print("  %s" % asc(rel))
        for line in s.splitlines()[:30]:
            t = line.strip()
            if re.match(r"^(namespace|open|import)\b", t):
                print("      %s" % asc(t)[:90])
    print()
    print("编译目标: Zero.LvFormalProbe.Theory.Cv00Memory")
    return 0


if __name__ == "__main__":
    sys.exit(main())
