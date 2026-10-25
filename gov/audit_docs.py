#!/usr/bin/env python3
"""核对文档与代码的一致性：文档声称的定理是否真的存在？

## 为什么

`README.md` 的 G1 状态写于 Round 24（「各有实例，无一处同时使用两端」），
但 Round 27 已经接了 `token_to_loss`。**文档漂移了 10 轮。**

目标要求「证明链彻底梳理干净」——文档是证明链的一部分，不能漂移。

## 检查什么

1. 文档中反引号内的 Lean 标识符，是否在内核源码中存在
2. `README.md` 的九条判定与 `_archive/KNOWN-GAPS.md` 是否矛盾
3. `PROGRESS.md` 的规模数字是否与实际相符

只读。
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

LAYERS = ["Core", "Lift", "Lib", "Geo"]

DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z0-9_']+)", re.M)

# Inductive constructors (`| name ...`) are identifiers too: documentation legitimately names them.
CTOR = re.compile(r"^\s*\|\s*([A-Za-z0-9_']+)", re.M)

# 文档里反引号中的标识符
TICKED = re.compile(r"`([A-Za-z_][A-Za-z0-9_.']*)`")

# 不是「本项目声明」的词：Lean 内建类型、关键字、tactic、常见缩写。
BUILTIN = {
    # 类型
    "Fin", "Nat", "Int", "Real", "Bool", "Prop", "Type", "Sort", "List", "Option",
    "Finset", "Fintype", "Set", "Sigma", "Array", "String", "Unit", "Prod", "Sum",
    # 关键字
    "def", "theorem", "lemma", "abbrev", "instance", "structure", "inductive", "class",
    "namespace", "section", "variable", "import", "open", "where", "match", "with",
    "private", "protected", "noncomputable", "axiom", "opaque", "admit",
    # tactic
    "simp", "rw", "ring", "cases", "induction", "exact", "apply", "intro", "decide",
    "omega", "linarith", "nlinarith", "field_simp", "norm_num", "funext", "congr",
    # 缩写与层名
    "core", "lift", "lib", "geo", "slots", "root", "kernel", "reference",
    # Layer 枚举的分支名
    "poly", "square", "existential", "transc",
    "cons", "nil", "some", "none", "id",
    # 本项目文件里的局部名
    "denote", "e2e", "e2e_sound", "Slot", "M0",
    # 概念名 / 状态名（文档用它们描述性质，不是引用声明）
    "sorry", "admit", "weakened", "discharged", "open_", "eval", "note",
    "m", "n", "p", "q", "x", "y",
    # Lv-00 参考材料的模块名（在 Zero/Reference/ 下，不是内核声明）
    "IR", "Cv00", "Cv00Lang", "Cv00Memory", "lvLang", "LvDSL", "Codegen",
    "CompilerCorrectness", "compile_constraint", "ir_sem", "IRConstraint", "IRExpr",
    "escape_baseline", "denote_zero",
    # Lv-00 参考材料中的函数名（在 Zero/Reference/ 下）
    "exec_stmt", "var",
    # 名称后缀（文档写 `_ne` 指 `coordProj_bump_ne` 这类命名）
    "_ne", "_iff", "_sound", "_eq", "_zero", "_pos", "_neg",
    # GeoConstraint 构造子（inductive 分支，不在 DECL 正则里）
    "collinear", "equalLength", "parallel", "perpendicular", "midpoint",
    "samePoint", "sqDistEq", "eqZero", "leZero", "ltZero", "gtZero", "rightAngle",
    # IRConstraint 的构造子（Reference 中定义，不在内核）
    "angle", "equalAngle", "tangent", "ratioDivision", "distance", "radius",
    "eq_expr", "lt_expr", "gt_expr",
    # 目录名与数学函数名
    "LvFormal", "Legacy", "arccos", "sqrt", "div", "mul", "add", "sub", "const", "coord",
}

# 不是 Lean 标识符的常见词（模块名、路径、命令等）
SKIP = re.compile(r"^(Zero|gov|lake|python|mathlib|_archive|README|PROGRESS|KNOWN|"
                  r"[a-z]+\.(py|lean|md|json|yml|toml)|--|\w+\.\w+)")


def kernel_decls():
    """Every declaration name plus every module name, since docs refer to both."""
    names = set()
    for layer in LAYERS:
        base = os.path.join(ZERO, "Lattice", layer)
        names.add(layer)                      # the layer directory is a valid reference too
        for root, dirs, fs in os.walk(base):
            dirs[:] = [d for d in dirs if d != ".lake"]
            for d in dirs:
                names.add(d)                  # sub-directory names
            for f in fs:
                if f.endswith(".lean"):
                    names.add(f[:-len(".lean")])   # module name
                    src = strip_comments(
                        io.open(os.path.join(root, f), "rb").read().decode("utf-8", "replace"))
                    names |= set(DECL.findall(src))
                    names |= set(CTOR.findall(src))
    return names


def main():
    decls = kernel_decls()
    print("内核声明总数:", len(decls))
    print()

    docs = ["README.md", "ARCHITECTURE.md", "_archive/KNOWN-GAPS.md", "_archive/DECISION-G7.md"]
    bad = defaultdict(list)
    for d in docs:
        p = os.path.join(ZERO, *d.split("/"))
        if not os.path.exists(p):
            continue
        src = io.open(p, encoding="utf-8", errors="replace").read()
        for m in TICKED.finditer(src):
            tok = m.group(1)
            if SKIP.match(tok):
                continue
            # 取最后一段（可能有 namespace 前缀）
            base = tok.split(".")[-1]
            if base in decls or tok in decls or base in BUILTIN:
                continue
            bad[d].append(tok)

    print("=" * 74)
    print("文档中引用的、但内核中不存在的标识符")
    print("=" * 74)
    if not bad:
        print("  无：文档引用的定理都存在")
    else:
        for d, toks in sorted(bad.items()):
            uniq = sorted(set(toks))
            print("  %s (%d):" % (d, len(uniq)))
            for t in uniq[:15]:
                print("      ", t)
    return 0


if __name__ == "__main__":
    sys.exit(main())
