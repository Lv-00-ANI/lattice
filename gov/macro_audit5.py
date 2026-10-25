# -*- coding: utf-8 -*-
"""修正重审：区分「定理证据」与「类型/接口证据」，并单独处理 LvFormal。

## 上一版的 bug

G6 期望的是类名（WeightSemantics/Compiler/...），但索引只收了 theorem/lemma，
所以全部判"缺"。
G7 期望 ir_sem/compile_constraint/exec_stmt，但它们在 Zero/LvFormal/ 下，
被排除列表过滤掉了。

## 本版

1. 索引同时收 theorem/lemma/def/class/structure/abbrev
2. LvFormal 单独索引，并标注「存在但无法编译」
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

ANY = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
                 r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
                 r"([A-Za-z0-9_']+)", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def index(exclude):
    idx = {}
    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d not in (".lake",) and d not in exclude]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")
            s = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
            for m in ANY.finditer(s):
                idx.setdefault(m.group(2), rel)
    return idx


def main():
    kern = index({"Legacy", "LegacyConflicted", "LvFormal"})
    lvf = index({"Legacy", "LegacyConflicted"}.__class__())  # 全量
    lvf_only = {k: v for k, v in lvf.items() if "/LvFormal/" in v}

    print("=" * 80)
    print("内核声明: %d    LvFormal 声明: %d" % (len(kern), len(lvf_only)))
    print("=" * 80)

    print("\n[G6] 全接口，不绑定厂商")
    for k in ("WeightSemantics", "Compiler", "Representation", "PenaltyEmbedding",
              "Repair", "Tokenizer", "Chain", "MLayer"):
        loc = kern.get(k)
        print("   %-24s %s" % (asc(k), asc(loc) if loc else "**缺**"))

    print("\n[G7] lvLang -> IR -> Cv00")
    for k in ("LvDSL", "IRExpr", "ir_sem", "IRConstraint", "compile_constraint",
              "exec_stmt", "Cv00Stmt", "Cv00Lang"):
        loc = lvf_only.get(k)
        note = ""
        if loc:
            note = "(在 LvFormal，无法编译)"
        print("   %-24s %s %s" % (asc(k), asc(loc) if loc else "**缺**", note))

    print("\n[补充] 上一版判缺但实际存在的")
    for k in ("encodeForm", "configOf_roundtrip", "evalPts_add"):
        loc = kern.get(k)
        print("   %-24s %s" % (asc(k), asc(loc) if loc else "**确实缺**"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
