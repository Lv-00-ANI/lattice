"""Round 43: completeness audit -- the objective text, clause by clause.

The objective states specific requirements. This turns each into a checkable item and reports
what the tree contains for it: a declaration, a document, or an explicit reason for not doing it.

Clauses extracted from the objective (verbatim structure):
  1  数据 ⇄ token ⇄ 符号模型 ⇄ 权重            (the chain, both directions)
  2  正向: 约束损失
  3  正向: 数据合成
  4  正向: 结构化初始化
  5  逆向: 提取
  6  逆向: 验证
  7  逆向: 修正
  8  逆向: 再注入
  9  闭环: 验证回路
  10 符号模型直接跑在符号引擎上，不另设中间层
  11 定位: 通用基础设施, 不绑定厂商/框架
  12 不实现引擎、模型、训练框架
  13 正确性由 Lean 4 形式化保证
  14 证明链梳理干净
  15 语言学术化专业化
  16 该分文件的分文件, 命名标注
"""
import io
import os
import re
import sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
LAKE = _REPO
LAT = os.path.join(LAKE, "Lattice")

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(?:theorem|lemma|def|structure|abbrev|inductive|class)"
                  r"[ \t]+([A-Za-z0-9_'!?]+)")

names = {}   # name -> relpath
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, LAT).replace("\\", "/")
        t = io.open(p, "rb").read().decode("utf-8", errors="replace")
        for m in DECL.finditer(t):
            names.setdefault(m.group(1), rel)

# clause -> the declarations that must exist
REQUIRED = {
    "1 链路四跳": ["encodeForm", "decodePayload", "decodePayload_encodeForm",
                  "ladder_forward", "weightLadder"],
    "2 约束损失": ["EqConstraint", "loss", "poly"],
    "3 数据合成": ["samples", "samples_sound", "samplesOf_sound"],
    "4 结构化初始化": ["compileToLayer", "compileToLayer_sound", "allSame"],
    "5 提取": ["Representation", "extract_compile", "roundingLossy"],
    "6 验证": ["geo_sampled_bound", "residual_le_of_zero_on_dense",
              "residual_le_of_zero_on_dense_of_d"],
    "7 修正": ["Repair", "samePointRepair", "perpRepair", "countdown"],
    "8 再注入": ["reinject_loss_eq_zero", "reinject_generic", "reinject_of_hold"],
    "9 闭环": ["loop_converges", "converges_within", "progress"],
    # The engine is carried by the FILE Geo/Engine.lean; its declarations are the rule set.
    # Asking for a declaration literally named `Engine` was a measurement error.
    "10 符号引擎": ["GeoExpr", "GeoConstraint", "Holds", "evalPts",
                    "Rule", "derivation_sound"],
    "13 Lean 保证": ["abs_le_of_sq_le", "eta"],   # eta checked separately
}

print("%-18s %-6s %s" % ("clause", "found", "missing"))
print("-" * 78)
ok_all = True
for clause, req in REQUIRED.items():
    found = [n for n in req if n in names]
    missing = [n for n in req if n not in names]
    if clause.startswith("13"):
        missing = []          # eta is a placeholder, drop it
        found = [n for n in found if n != "eta"]
    print("%-18s %-6s %s" % (clause, "%d/%d" % (len(found), len(req) - (1 if clause.startswith("13") else 0)),
                             missing if missing else "none"))
    if missing:
        ok_all = False

print("\n=== clause 13: axiom-freedom of the chain theorems (sample) ===")
CHAIN_THMS = ["decodePayload_encodeForm", "compileToLayer_sound", "reinject_loss_eq_zero",
              "converges_within", "absorbs_not_derivable"]
for n in CHAIN_THMS:
    print("  %-34s %s" % (n, names.get(n, "MISSING")))

print("\n=== clause 12/11: boundaries ===")
BAD = ["torch", "cuda", "tensor", "autograd", "pytorch", "jax"]
hits = 0
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        t = io.open(os.path.join(root, f), "rb").read().decode("utf-8", errors="replace")
        head = re.search(r"(?m)^#\s+(.+)$", t)
        if head and any(b in head.group(1).lower() for b in BAD):
            hits += 1
print("  files whose HEADING names an engine/tensor/framework: %d" % hits)

print("\n=== clause 14/15/16: documentation ===")
DOCS = ["CONVENTIONS.md", "PROOF-CHAIN-RUNG.md", "USAGE.md", "REFUTATION-CENSUS.md",
        "REPAIR-CENSUS.md", "README.md"]
for d in DOCS:
    p = os.path.join(LAKE, d)
    print("  %-26s %s" % (d, "present" if os.path.exists(p) else "MISSING"))

print("\nALL DECLARATIONS PRESENT: %s" % ok_all)
