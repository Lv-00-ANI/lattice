# -*- coding: utf-8 -*-
"""宏观认知：拿目标原文逐条对照当前代码，不看任何既有文档。

## 方法

对目标的每一句断言，找出它在代码里的对应物（或确认没有）。
判据分三档：
  PROVED   —— 有定理，且定理陈述与目标语义一致
  PARTIAL  —— 有代码/定理，但覆盖不全或前提强于目标
  ABSENT   —— 没有对应物

不引用 PROGRESS.md、ARCHITECTURE.md 的任何结论。全部从源码重新测量。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def kernel_files():
    """只扫 zero 内核，排除迁入的旧库。"""
    out = []
    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d not in (".lake", "Legacy", "LegacyConflicted", "LvFormal")]
        for f in sorted(fs):
            if f.endswith(".lean"):
                p = os.path.join(base, f)
                out.append((p, os.path.relpath(p, ZERO).replace("\\", "/")))
    top = os.path.join(ZERO, "Lattice.lean")
    if os.path.exists(top):
        out.append((top, "Lattice.lean"))
    return out


THM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)


def main():
    files = kernel_files()
    text = {rel: strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
            for p, rel in files}
    alltext = "\n".join(text.values())

    print("=" * 78)
    print("内核模块清单（%d 个文件）" % len(files))
    print("=" * 78)
    for rel in sorted(text):
        n_thm = len(THM.findall(text[rel]))
        n_lines = text[rel].count("\n") + 1
        print("  %-44s %4d 行  %3d 定理" % (asc(rel), n_lines, n_thm))

    print()
    print("=" * 78)
    print("目标断言 -> 代码对应物")
    print("=" * 78)

    # 目标里的关键词与期望的代码证据
    probe = [
        ("数据 ⇄ token", ["Tokenizer", "encodeForm", "decodeSym1", "Ladder"]),
        ("token ⇄ 符号", ["Encoded", "payload", "Token"]),
        ("符号 -> 权重（编译）", ["Compiler", "compileProgram"]),
        ("约束损失", ["PenaltyEmbedding", "sqPenalty", "PenaltyExact"]),
        ("逆向：权重 -> 符号（提取）", ["Representation", "extract"]),
        ("验证回路（修复）", ["Repair", "progress", "absorbs"]),
        ("符号引擎（不另设中间层）", ["LvDSL", "ir_sem", "eval_expr"]),
        ("可逆性：对象层双射", ["roundtrip", "Injective"]),
        ("可逆性：语义层不可逆", ["semantic_not_injective"]),
    ]
    for label, keys in probe:
        hits = [k for k in keys if re.search(r"\b" + re.escape(k) + r"\b", alltext)]
        missing = [k for k in keys if k not in hits]
        mark = "有" if len(hits) == len(keys) else ("部分" if hits else "**无**")
        print("  %-28s %-4s  命中: %s" % (asc(label), mark, ", ".join(hits) or "-"))
        if missing:
            print("  %-28s       缺: %s" % ("", ", ".join(missing)))

    print()
    print("=" * 78)
    print("四条靶定理：精确陈述")
    print("=" * 78)
    targets = [
        ("T1 编译保语义", ["compileProgram_sound", "compileProgram_models"]),
        ("T2 约束嵌入可靠", ["embedding_sound_at_minimiser", "program_sound_at_minimiser",
                       "sq_penalty_exact_finN", "sq_penalty_exact_matrix", "layer_penalty_exact"]),
        ("T3 提取等价", ["no_extractor_both_layers", "semantic_not_injective",
                     "extract_compile", "compile_injective"]),
        ("T4 回路收敛", ["progress", "preserves", "stable", "linear_converges"]),
    ]
    for label, names in targets:
        print("\n  --- %s ---" % asc(label))
        for nm in names:
            found = None
            for rel, t in text.items():
                m = re.search(r"^\s*(?:theorem|lemma)\s+" + re.escape(nm) + r"\b([^\n]*(?:\n(?![a-z]).*)*?)(?=:=|\bwhere\b)",
                              t, re.M)
                if re.search(r"^\s*(?:theorem|lemma)\s+" + re.escape(nm) + r"\b", t, re.M):
                    # 打印签名首行
                    mm = re.search(r"^\s*(?:theorem|lemma)\s+" + re.escape(nm) + r"\b.*$", t, re.M)
                    print("     %-38s %s" % (asc(nm), asc(rel)))
                    print("        %s" % asc(mm.group(0).strip())[:88])
                    found = True
                    break
            if not found:
                print("     %-38s **未找到**" % asc(nm))
    return 0


if __name__ == "__main__":
    sys.exit(main())
