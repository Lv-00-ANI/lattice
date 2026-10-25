# -*- coding: utf-8 -*-
"""把 formal/lvFormal/ 的 122 个文件复制到 Lattice/LvFormal/，并改 import。

## 关键决策（每条都有依据）

1. **保留内部相对结构**：`lvFormal/Theory/X.lean` -> `Zero/LvFormal/Theory/X.lean`，
   模块名 `Zero.LvFormal.Theory.X`。

2. **只改行首 import**：用 `^(import\s+)lvFormal\.` 锚定，避免动注释/文档块里的路径。

3. **改名后的模块路径必须与文件路径一致**：Lean 要求
   `Zero.LvFormal.Theory.X` <=> `Zero/LvFormal/Theory/X.lean`。

4. **不迁 `check_scratch.lean`**：它是散落测试文件（顶层声明 `Formula'`、`term_eval_test`），
   不是 lvFormal 库的一部分，且和 check 系列文件同类（源目录顶层有 40 个）。

5. **`Cache` 命名空间**：出现 1 次，位于某个文件中，属于 lvFormal 内部，保持原样。
"""
import io
import os
import re
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
SRC = os.path.join(ZERO, "..", "_harvest", "lv00", "formal", "lvFormal")
DST = os.path.join(ZERO, "Lattice", "LvFormal")

# 只改行首的 import 语句
IMPORT_RE = re.compile(r"^(import\s+)lvFormal\.", re.M)

# 不迁移的文件（散落测试，不属于库本体）
SKIP = {"check_scratch.lean"}


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    if not os.path.isdir(SRC):
        print("源不存在:", SRC)
        return 1

    copied = 0
    rewritten = 0
    total_imports = 0
    skipped = []

    for base, dirs, fs in os.walk(SRC):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            if f in SKIP:
                skipped.append(os.path.relpath(os.path.join(base, f), SRC))
                continue

            src = os.path.join(base, f)
            rel = os.path.relpath(src, SRC)
            dst = os.path.join(DST, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy2(src, dst)
            copied += 1

            s = io.open(dst, encoding="utf-8").read()
            n_hits = len(IMPORT_RE.findall(s))
            if n_hits:
                s2 = IMPORT_RE.sub(r"\1Zero.LvFormal.", s)
                io.open(dst, "w", encoding="utf-8", newline="\n").write(s2)
                rewritten += 1
                total_imports += n_hits

    print("复制文件:", copied)
    print("改写 import 的文件:", rewritten)
    print("改写 import 条数:", total_imports)
    if skipped:
        print("跳过:", [asc(x) for x in skipped])
    print("目标:", asc(DST))
    return 0


if __name__ == "__main__":
    sys.exit(main())
