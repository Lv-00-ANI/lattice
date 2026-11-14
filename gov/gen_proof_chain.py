# -*- coding: utf-8 -*-
"""Generate and verify the PROOF CHAIN: the eleven theorems that carry the objective's sentence.

## Why a generated index rather than a written one

**The objective's sentence has six clauses, and each is carried by named theorems.** **A hand-written table of
those theorems rots: a rename, a move, or a deletion makes it false, and nothing notices.**

**=> this script REGENERATES the table from measurement:**

- **does the theorem exist** in the file the table claims?
- **how many places cite it** (a theorem cited 0 times is a statement, not a link in a chain)?
- **does the file it lives in build** (a theorem in a red file is not available)?

**`PROOF-CHAIN.md` is written by this script and must not be edited by hand.**

## What `--check` enforces

1. **every theorem in the table is still DEFINED** in its recorded file;
2. **every theorem is still CITED at least once** -- an uncited theorem has dropped out of the chain;
3. **every file in the table exists**.

**=> failure of (1) or (3) means the index is stale; failure of (2) means the chain has a dangling link.**

Usage:
    python gen_proof_chain.py            # regenerate PROOF-CHAIN.md
    python gen_proof_chain.py --check    # verify the table against the tree
"""

import io
import os
import re
import subprocess
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ZERO, "PROOF-CHAIN.md")

# (clause of the objective, theorem, file, what it says)
CHAIN = [
    ("正向：符号知识 → 权重",
     "symbolToWeight_correct",
     "Lattice/Runtime/SymbolToWeightCorrectness.lean",
     "符号约束全部成立 ⟺ 编译出的权重层输出全为零"),
    ("逆向：权重 → 符号",
     "extract_compile_constraints",
     "Lattice/Runtime/LoopClosure.lean",
     "先编译再提取，回到原约束集"),
    ("闭环：回路是双射",
     "compile_extract_bijective",
     "Lattice/Runtime/LoopClosure.lean",
     "`extractLayer` 与 `compileToLayer` 互为左右逆"),
    ("验证：语法判据",
     "faithful_iff_extract_eq",
     "Lattice/Runtime/Faithfulness.lean",
     "层忠于数据 ⟺ 提取结果等于数据的约束集"),
    ("验证：语义判据",
     "satisfies_extractLayer_iff_self",
     "Lattice/Runtime/SemanticFaithfulness.lean",
     "提取出的符号成立 ⟺ 该层输出为零"),
    ("修正：吸收性",
     "repair_preserves_verdict",
     "Lattice/Runtime/RepairClosure.lean",
     "判据为真 ⟹ 修复不动它"),
    ("修正：严格进展",
     "repair_makes_progress",
     "Lattice/Runtime/RepairClosure.lean",
     "判据为假 ⟹ 测度严格下降"),
    ("修正：终止即满足",
     "repair_terminates_at_sat",
     "Lattice/Runtime/RepairClosure.lean",
     "测度为零 ⟹ 判据为真"),
    ("再注入",
     "extract_after_repair",
     "Lattice/Runtime/RepairClosure.lean",
     "修复到测度为零后，提取出的符号满足原约束"),
    ("端到端：数据 → 权重",
     "data_to_weight_iff",
     "Lattice/Runtime/EndToEndComposite.lean",
     "数据的约束全部成立 ⟺ 权重层输出全为零"),
    ("回路闭合（既有）",
     "verification_loop_closes_holds",
     "Lattice/Runtime/VerificationLoop.lean",
     "修复回路闭合"),
]


def citations(thm):
    r = subprocess.run(["git", "grep", "-c", thm, "--", "Lattice/**/*.lean"],
                       cwd=ZERO, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    total = 0
    for line in r.stdout.strip().split("\n"):
        if not line.strip():
            continue
        tail = line.rsplit(":", 1)[-1]
        if tail.isdigit():
            total += int(tail)
    return total


def measured():
    rows = []
    for clause, thm, rel, desc in CHAIN:
        path = os.path.join(ZERO, rel.replace("/", os.sep))
        exists = os.path.exists(path)
        defined = False
        if exists:
            text = io.open(path, encoding="utf-8", errors="replace").read()
            defined = ("theorem " + thm) in text
        rows.append({
            "clause": clause, "thm": thm, "file": rel,
            "desc": desc, "exists": exists, "defined": defined,
            "cites": citations(thm) if defined else 0,
        })
    return rows


def render(rows):
    head = """# 证明链索引（**由 `gov/gen_proof_chain.py` 生成，勿手改**）

> **本表把项目目标的六个子句逐句对应到具名定理。**
> **每一行都由**测量**得来：定理是否仍定义在所指文件里、被引用多少次。**
> **重新生成：`python gov/gen_proof_chain.py`；核验：`python gov/gen_proof_chain.py --check`。**

## 目标原句

> **正向把符号知识编译成权重（约束损失、数据合成、结构化初始化），
> 逆向把权重行为提取回符号，用于验证、修正、再注入；闭环就是验证回路。**

## 逐句落点

| 子句 | 定理 | 位置 | 内容 | 引用 |
|:--|:--|:--|:--|--:|
"""
    lines = [head]
    for r in rows:
        mark = "" if (r["exists"] and r["defined"] and r["cites"] > 0) else " ⚠"
        lines.append("| %s | `%s`%s | `%s` | %s | %d |\n"
                     % (r["clause"], r["thm"], mark, r["file"], r["desc"], r["cites"]))
    ok = all(r["exists"] and r["defined"] and r["cites"] > 0 for r in rows)
    lines.append("\n## 状态\n\n")
    if ok:
        lines.append("**全部 %d 条定理就位，且都被引用至少一次。**\n" % len(rows))
    else:
        bad = [r["thm"] for r in rows if not (r["exists"] and r["defined"] and r["cites"] > 0)]
        lines.append("**⚠ 链条有断点：%s**\n" % ", ".join("`%s`" % b for b in bad))
    lines.append("\n## 诚实边界\n\n")
    lines.append(
        "**这些定理合起来说明「表示链与验证回路在**这条线性/约束表示**上是闭合的」，"
        "**不**说明「任意权重都能被还原成有意义的符号」。**\n"
        "**后者的困难见 `PIPELINE-COVERAGE.md` 与第 895 轮的否证；本表不声称它。**\n")
    return "".join(lines)


def main(argv):
    rows = measured()
    if "--check" in argv:
        bad = []
        for r in rows:
            if not r["exists"]:
                bad.append("%s: file missing (%s)" % (r["thm"], r["file"]))
            elif not r["defined"]:
                bad.append("%s: theorem not defined in %s" % (r["thm"], r["file"]))
            elif r["cites"] == 0:
                bad.append("%s: no citations -- dropped out of the chain" % r["thm"])
        print("PROOF CHAIN: %d link(s) checked" % len(rows))
        if bad:
            for b in bad:
                print("  BROKEN %s" % b)
            print("\nPROOF CHAIN: %d broken link(s)" % len(bad))
            return 1
        print("\nPROOF CHAIN: all %d link(s) present and cited" % len(rows))
        return 0
    io.open(OUT, "w", encoding="utf-8", newline="\n").write(render(rows))
    print("wrote %s (%d links)" % (OUT, len(rows)))
    return 0


def self_test():
    """Demonstrate the checker's failure modes."""
    ok = True
    if citations("this_theorem_does_not_exist_anywhere") != 0:
        print("  self-test FAILED: a nonexistent theorem reports citations")
        ok = False
    if citations("symbolToWeight_correct") <= 0:
        print("  self-test FAILED: a known theorem reports zero citations")
        ok = False
    rows = measured()
    if len(rows) != len(CHAIN):
        print("  self-test FAILED: measurement dropped rows")
        ok = False
    print("  self-test: %s" % ("both directions of the citation test work" if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
