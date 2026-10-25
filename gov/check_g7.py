# -*- coding: utf-8 -*-
"""验证 `G7-BREAKPOINTS.md` 第二节的每条复现命令都能跑出第一节的数字。

## 为什么

一份可复现清单，如果命令本身跑不通，比没有清单更糟：
读者会以为数字是编的。所以**命令必须自己先被验证**。
"""
import io
import os
import re
import sys

# The console on this platform may be GBK; `ℝ` and the box-drawing characters used in the
# report cannot be encoded there. Re-wrap stdout so the report is emitted as UTF-8 with
# unrepresentable characters replaced rather than aborting the check.
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

ZERO = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
ZERO = os.path.abspath(ZERO)


def read(rel):
    """Read a file with newlines normalised to LF, so line-anchored regexes behave."""
    s = io.open(os.path.join(ZERO, *rel.split("/")), encoding="utf-8",
                errors="replace").read()
    return s.replace("\r\n", "\n").replace("\r", "\n")


def main():
    ok = True

    # 断点 1：兜底数 **与** 构造子 case 数必须一起看
    comp = read("Lattice/Reference/LvFormal/Theory/Compiler.lean")
    n1 = comp.count("| _ => none")
    ncases = len(re.findall(r"\n  \| \.\w+ =>", comp))
    print("断点 1  compile_constraint 的 `| _ => none` 数量 =", n1, "（兜底，文档声称 12）")
    print("        构造子 case 数 =", ncases, "（文档声称 14）")
    print("        判读：兜底是参数个数不匹配时的保护，不是缺失分支"
          if ncases >= n1 else "        判读：存在真实缺失分支")
    ok &= (n1 == 12)
    ok &= (ncases == 14)

    # 断点 2：case 全部实现，但 .var 丢弃 y
    src2 = read("Lattice/Reference/LvFormal/Theory/IR.lean")
    line2 = [l.strip() for l in src2.splitlines() if ".var n" in l and "=>" in l]
    print("断点 2  eval_expr 的 .var 分支 =", line2[0] if line2 else "（未找到）")
    found2 = bool(line2) and "ptX" in line2[0]
    print("        是否只取 x 坐标（ptX）:", found2)
    # Count only the alternatives belonging to `eval_expr`: slice from its `def` to the next
    # `def`/`theorem`/`/-!` marker, so other match blocks in the same file are excluded.
    m2 = re.search(r"def eval_expr[^\n]*\n(.*?)(?=\n(?:def |theorem |noncomputable def |/-!))",
                   src2, re.S)
    n2cases = len([l for l in (m2.group(1) if m2 else "").splitlines()
                   if l.lstrip().startswith("| .") and "=>" in l])
    has_pty = "def ptY" in src2
    print("        实现 case", n2cases, "/ env 类型携带 y:", has_pty)
    print("        判读：实现完整但语义错——env 是 ℝ × ℝ，.var 却只取 ptX"
          if found2 and has_pty else "        判读：未证实语义错")
    ok &= found2

    # 断点 3
    n3 = read("Lattice/Reference/LvFormal/Theory/CompilerCorrectness.lean").count("Cv00")
    print("断点 3  CompilerCorrectness 中 `Cv00` 出现次数 =", n3, "（文档声称 0）")
    ok &= (n3 == 0)

    # 断点 4：exec_stmt 的实现分支 vs Cv00Stmt 的构造子
    mem = read("Lattice/Reference/LvFormal/Theory/Cv00Memory.lean")
    stmt_branches = len(re.findall(r"\n\s+\| \.\w+ \w* *=>", mem))
    lang = read("Lattice/Reference/LvFormal/Theory/Cv00Lang.lean")
    m = re.search(r"inductive Cv00Stmt where(.*?)\n\n", lang, re.S)
    nstmts = len(re.findall(r"\n  \| \w+", m.group(1))) if m else -1
    print("断点 4  exec_stmt 的实现分支 =", stmt_branches, "/ Cv00Stmt 构造子 =", nstmts)
    silent = nstmts - stmt_branches if nstmts > 0 else -1
    print("        判读：", (str(silent) + " 个构造子落入 `| _ => .normal`，静默跳过（真缺口）")
          if silent > 0 else "无静默跳过")

    # 断点 5：LvFormal 下与 Weight 的连接
    root = os.path.join(ZERO, "Lattice", "Reference", "LvFormal")
    hits = []
    for dirpath, _dirs, files in os.walk(root):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            try:
                s = io.open(p, encoding="utf-8", errors="replace").read()
            except OSError:
                continue
            if re.search(r"\bWeight\b", s):
                hits.append(os.path.relpath(p, root))
    print("断点 5  LvFormal 中提到 `Weight` 的文件数 =", len(hits),
          "（文档声称无连接）")
    ok &= (len(hits) == 0)

    print()
    print("=" * 60)
    print("复现结果:", "全部一致" if ok else "有出入，需修文档")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
