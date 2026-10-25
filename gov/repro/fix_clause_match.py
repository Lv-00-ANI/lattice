"""Fix the clause matching: headings are a MIX of English and Chinese.

`Geo/Reinjection.lean`'s heading is "再注入：修正之后，重新编译的惩罚在修正点为零", so an English
keyword search reports the reinjection clause as having ZERO files when it has one.

This is the third measurement defect of the same family in this project:
  1. searching declaration names for topics (missed Geo/Synthesis);
  2. keyword search inflating "repair" 10x with `fixed` hits;
  3. now: single-language keyword search over bilingual headings.

Add Chinese keys alongside the English ones.
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
LAT = _os.path.join(_REPO, "Lattice")

rows = []
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        rel = os.path.relpath(p, LAT).replace("\\", "/")
        t = io.open(p, "rb").read().decode("utf-8", errors="replace")
        thms = len(re.findall(r"(?m)^[ \t]*(?:noncomputable[ \t]+)?(?:theorem|lemma)[ \t]", t))
        m = re.search(r"(?m)^#\s+(.+)$", t)
        head = m.group(1).strip() if m else ""
        rows.append((rel, thms, head))

CLAUSES = {
    "L0<->L1 数据⇄token":       ["tokeniz", "标记化", "分词", "L0"],
    "L1<->L2 token⇄符号":       ["L1L2", "TokenSymbol", "Roundtrip", "往返", "token ⇄ 符号"],
    "L2->L3 符号→权重":          ["SymbolToWeight", "Compile", "Convert", "Compiler", "编译", "权重"],
    "L3->L2 提取":               ["Extract", "WeightToSymbol", "Semantic", "提取"],
    "约束损失":                   ["Loss", "Penalty", "Square", "Exterior", "损失", "惩罚"],
    "数据合成":                   ["Synthesis", "Invariant", "Initialise", "合成", "初始化"],
    "修正":                      ["Repair", "Loop", "ConjRepair", "修复", "修正"],
    "再注入":                     ["Reinject", "reinject", "再注入"],
    "闭环":                      ["Loop", "ClosedLoop", "Converge", "回路", "收敛"],
    "符号引擎":                   ["Engine", "Exec", "Rules", "Derive", "Eval", "引擎", "推理"],
    "验证":                      ["Verif", "Sampled", "Lipschitz", "Rho", "验证", "采样"],
}

print("=== goal clauses (bilingual headings) ===")
tot_ok = 0
for clause, keys in CLAUSES.items():
    hits = [r for r in rows if any(k.lower() in r[2].lower() for k in keys)]
    flag = "" if hits else "   <-- ZERO"
    print("  %-24s %2d files, %4d theorems%s" % (clause, len(hits), sum(h[1] for h in hits), flag))
    if not hits:
        tot_ok += 1
print("\nclauses with zero coverage: %d" % tot_ok)

# Chinese-titled files overall
n_cn = sum(1 for r in rows if re.search(r"[\u4e00-\u9fff]", r[2]))
print("files with a Chinese heading: %d of %d (%.0f%%)"
      % (n_cn, len(rows), 100.0 * n_cn / len(rows)))
