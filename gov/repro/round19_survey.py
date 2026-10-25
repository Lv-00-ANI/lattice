"""Round 19 macro measurement: what does the project still lack against its stated goal?

The goal, from the objective text:
  正向把符号知识编译成权重（约束损失、数据合成、结构化初始化）
  逆向把权重行为提取回符号，用于验证、修正、再注入
  闭环就是验证回路
  符号模型直接跑在符号引擎上
  定位通用基础设施，不实现引擎/模型/训练框架

Measure each of those five against the tree, not against memory.
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

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(theorem|lemma|def|structure|abbrev|inductive)[ \t]+"
                  r"([A-Za-z0-9_'!?]+)")


def index():
    """name -> (kind, file) for every declaration in the kernel (excl. Reference)."""
    idx = {}
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
                idx.setdefault(m.group(2), (m.group(1), rel))
    return idx


idx = index()
print("kernel declarations: %d" % len(idx))

# --- 1. 正向三件事 -----------------------------------------------------------
print("\n=== 正向：符号知识 -> 权重 ===")

def find(pattern, label):
    hits = [(n, k, f) for n, (k, f) in idx.items() if re.search(pattern, n)]
    print("  %-34s %d" % (label, len(hits)))
    for n, k, f in sorted(hits)[:4]:
        print("       %-40s %s" % (n, f))
    return hits

find(r"loss|Loss", "约束损失（loss 相关声明）")
find(r"synth|Synth|augment", "数据合成")
find(r"init|Init|structur", "结构化初始化")

# --- 2. 逆向三件事 -----------------------------------------------------------
print("\n=== 逆向：权重 -> 符号 ===")
find(r"extract|Extract", "提取")
find(r"verif|Verif|check|Check", "验证")
find(r"repair|Repair|fix|Fix", "修正")
find(r"reinject|reinject|reInject", "再注入")

# --- 3. 闭环 ----------------------------------------------------------------
print("\n=== 闭环 ===")
find(r"loop|Loop", "回路")
find(r"converge|Converge", "收敛")

# --- 4. 符号引擎 -------------------------------------------------------------
print("\n=== 符号引擎（不设中间层）===")
for name in ("GeoExpr", "GeoConstraint", "EqConstraint", "poly", "evalPts", "Holds"):
    hit = idx.get(name)
    print("  %-18s %s" % (name, ("%s in %s" % (hit[0], hit[1])) if hit else "*** MISSING ***"))

# --- 5. 不实现引擎/模型/训练框架 ----------------------------------------------
print("\n=== 边界：实现了不该实现的吗 ===")
for pat, label in ((r"torch|Torch", "torch"), (r"cuda|CUDA|gpu|GPU", "GPU"),
                   (r"tensor|Tensor", "tensor")):
    hits = [n for n in idx if re.search(pat, n)]
    print("  %-10s %d declarations" % (label, len(hits)))
