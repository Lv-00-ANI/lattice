# -*- coding: utf-8 -*-
"""宏观认知 v3：把目标九分句逐条对照当前实测状态。

## 与上一轮的区别

上一轮（Round 33）测到 Geo 是 12 个文件、45 条定理。
本轮实测 Geo 已扩到 **28 个文件、3,668 行、168 条定理**。

新增的 Semantic / Engine / Pipeline / Compile / Extract / Loop / Invariant /
Synthesis / Initialise / Rules / QualityBridge 恰好覆盖上一轮判为缺口的
G5（符号引擎）与 G3（闭环）。

所以必须重新判定，不能引用上一轮结论。

## 判据

对每个分句给出：判定（达成/部分/未达成）+ 代码证据（定理名 + 文件）。
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


def kernel_index():
    """全内核（不含 Legacy/LvFormal）的 定理名 -> 文件 索引。"""
    idx = {}
    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d not in (".lake", "Legacy", "LegacyConflicted", "LvFormal")]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")
            s = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
            for m in re.finditer(r"^\s*(?:theorem|lemma)\s+([A-Za-z0-9_']+)", s, re.M):
                idx.setdefault(m.group(1), rel)
    return idx


# 目标九分句 -> 期望的代码证据
CLAIMS = [
    ("G1", "数据 <=> token <=> 符号 <=> 权重（四层往返）",
     ["token_to_weight", "token_to_loss", "decodeSym1_encodeSym1", "encodeForm"]),
    ("G2", "正向：符号知识编译成权重（约束损失）",
     ["geo_compile_preserves", "geoCompiler_compile", "compileProgram_sound"]),
    ("G3", "逆向：提取回符号，用于验证/修正/再注入",
     ["configOf_roundtrip", "reinject_sound", "reinject_entails", "synthesize_from_initialisation"]),
    ("G4", "闭环就是验证回路（收敛且不破坏语义）",
     ["loop_converges", "fixSamePoint_holds", "fixSamePoint_absorbs",
      "perp_loop_converges", "linear_converges", "geo_repair_progress"]),
    ("G5", "符号模型直接跑在符号引擎上，不另设中间层",
     ["derivation_sound", "step_sound", "basicRules_sound", "evalPts_add"]),
    ("G6", "不绑定厂商/框架（全接口）",
     ["WeightSemantics", "Compiler", "Representation", "PenaltyEmbedding"]),
    ("G7", "既有编译链 lvLang -> IR -> Cv00 延伸到权重",
     ["ir_sem", "compile_constraint", "exec_stmt"]),
    ("G8a", "T1 编译保语义", ["compileProgram_sound", "geo_compile_preserves"]),
    ("G8b", "T2 约束嵌入可靠", ["embedding_sound_at_minimiser", "geo_penalty_exact",
                          "sq_penalty_exact_finN", "sq_penalty_exact_matrix"]),
    ("G8c", "T3 提取等价", ["no_extractor_both_layers", "extract_compile",
                       "configOf_roundtrip"]),
    ("G8d", "T4 回路收敛不破坏语义", ["progress", "preserves", "loop_converges"]),
    ("G9", "可逆性分层：对象层双射 / 语义层不可逆",
     ["flatten_injective", "flatten_surjective", "semantic_not_injective",
      "no_extractor_both_layers"]),
]


def main():
    idx = kernel_index()
    print("=" * 80)
    print("内核定理总数: %d" % len(idx))
    print("=" * 80)
    for tag, desc, want in CLAIMS:
        found = [(w, idx[w]) for w in want if w in idx]
        missing = [w for w in want if w not in idx]
        if not missing:
            verdict = "达成"
        elif found:
            verdict = "部分"
        else:
            verdict = "未达成"
        print("\n[%s] %s" % (tag, asc(desc)))
        print("   判定: %s   (%d/%d 证据到位)" % (verdict, len(found), len(want)))
        for w, f in found:
            print("      OK   %-34s %s" % (asc(w), asc(f)))
        for w in missing:
            print("      缺   %s" % asc(w))
    return 0


if __name__ == "__main__":
    sys.exit(main())
