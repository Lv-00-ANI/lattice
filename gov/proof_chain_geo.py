#!/usr/bin/env python3
"""生成 `Zero/Geo/` 的证明链地图：每个模块的主要定理、依赖、以及它们如何连到四条靶定理。

## 为什么要单独做

`gov/chain.py` 扫全树（558 文件）会超时。而 `Zero/Geo/` 是本轮重建的核心，
需要一份**聚焦的**证明链说明，让读者能顺着一条线读完：
几何表达式 → 平方距离 → 约束 → 损失 → 可微 → 精确性。

## 产出

`gov/PROOF-CHAIN-GEO.md`
"""
import io
import artifact_guard
SYNCED = []
sync = artifact_guard.sync
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
# Round 246. This pointed at `Lattice/Geo`, which no longer exists: the whole layer moved to
# `Domains/` (99 modules), then split into `Domains/Constraints/` (28) and `Domains/Geometry/` (71).
# Round 265 (STAGE 0): `Domains/` was ARCHIVED -- the subtree now lives at
# `Lattice/Reference/Geometry/{Geometry,Constraints,LvFormal}`. `GEO` still names ONE root, and
# the walk below is recursive, so pointing it at the archive keeps every module in scope.
GEO = os.path.join(ZERO, "Lattice", "Reference", "Geometry")

# Round 246, second defect in this line: it matched `Zero.Geo.`, the old library's module prefix.
# The tree imports `Lattice.Geo.` (the namespace survived the move per §2.8) -- and the MODULE path
# is `Lattice.Domains[.Constraints|.Geometry].`. Both are accepted; the walk is recursive.
# Round 265: the archive path has FOUR segments (`Lattice.Reference.Geometry.<Sub>.<Mod>`),
# so the alternation gains an `Reference\.Geometry\.[A-Za-z]+` branch.
IMPORT = re.compile(r"^import\s+(?:Lattice|Zero)\.(?:Reference\.Geometry\.[A-Za-z]+|Geo|Domains)(?:\.[A-Za-z]+)?\.(\S+)", re.M)
THEOREM = re.compile(r"^theorem\s+([A-Za-z0-9_']+)", re.M)
DEFN = re.compile(r"^(?:noncomputable\s+)?(?:def|abbrev|structure|inductive)\s+([A-Za-z0-9_']+)", re.M)

# 每条靶定理在几何层里的落点
TARGETS = {
    "T1 编译保语义": [
        ("Lattice/LvFormal/Theory/CompilerCorrectness.lean", "compile_preserves_satisfiability"),
    ],
    "T2 约束嵌入可靠": [
        ("Lattice/Geo/Exact.lean", "geo_penalty_exact"),
        ("Lattice/Geo/Nondegenerate.lean", "perpResid_bump"),
        ("Lattice/Geo/Differentiable.lean", "hasFDerivAt_coord"),
        ("Lattice/Lib/Penalty/PolyExact.lean", "sq_eq_zero_of_localMin"),
    ],
    "T3 提取等价": [
        ("Lattice/Geo/Extract.lean", "configOf"),
        ("Lattice/Geo/Extract.lean", "perp_neg_iff"),
        ("Lattice/Geo/Flatten.lean", "flattenEquiv"),
    ],
    "T4 回路收敛": [
        ("Lattice/Geo/Repair.lean", "no_identity_repair"),
        ("Lattice/Core/Repair.lean", "progress"),
    ],
}


def main():
    files = []
    for root, _dirs, fs in os.walk(GEO):
        files.extend(os.path.join(root, f) for f in sorted(fs) if f.endswith(".lean"))
    files.sort()
    if not files:
        print("PROOF CHAIN (geo): no modules found -- refusing to emit an empty chain")
        return 1
    info = {}
    for f in files:
        p = f
        src = io.open(p, encoding="utf-8").read()
        _prefix = "Lattice.Domains." if (os.sep + "Domains" + os.sep) in f else "Lattice.Geo."
        mod = _prefix + os.path.basename(f)[:-5]
        info[mod] = {
            "file": f,
            "lines": src.count("\n") + 1,
            "deps": [d.replace("Lattice.Geo.", "") for d in IMPORT.findall(src)
                     if d != mod],
            "theorems": THEOREM.findall(src),
            "defs": DEFN.findall(src),
        }

    # 拓扑层
    rank = {}

    def depth(m, seen=None):
        if m in rank:
            return rank[m]
        if seen is None:
            seen = set()
        if m in seen:
            return 0
        seen.add(m)
        ds = ["Lattice.Geo." + d for d in info[m]["deps"] if ("Lattice.Geo." + d) in info]
        r = 0 if not ds else 1 + max(depth(x, seen) for x in ds)
        rank[m] = r
        return r

    sys.setrecursionlimit(10000)
    for m in info:
        depth(m)

    byrank = {}
    for m, r in rank.items():
        byrank.setdefault(r, []).append(m)

    lines = ["# `Zero/Geo/` 证明链地图", "",
             "> 由 `gov/proof_chain_geo.py` 生成。", "",
             "本层是重建的符号侧：把几何约束变成可以喂给权重层的平方损失。", "",
             "## 一、拓扑分层", "",
             "依赖严格向下，无环。自底向上读：", ""]

    LAYER_DESC = {
        0: "表达式基座",
        1: "距离与线性化",
        2: "约束与扰动代数",
        3: "损失构造",
        4: "微分与提取",
        5: "精确性",
    }
    for r in sorted(byrank):
        mods = sorted(byrank[r])
        desc = LAYER_DESC.get(r, "")
        lines.append("### L%d —— %s" % (r, desc))
        lines.append("")
        lines.append("| 模块 | 行数 | 定理 | 依赖 |")
        lines.append("|:--|--:|--:|:--|")
        for m in mods:
            d = info[m]
            lines.append("| `%s` | %d | %d | %s |"
                         % (m.replace("Lattice.Geo.", ""), d["lines"],
                            len(d["theorems"]),
                            ", ".join(d["deps"]) or "—"))
        lines.append("")

    lines += ["## 二、四条靶定理在几何层中的落点", ""]
    for t, items in TARGETS.items():
        lines.append("### " + t)
        lines.append("")
        lines.append("| 文件 | 声明 |")
        lines.append("|:--|:--|")
        for path, name in items:
            exists = os.path.exists(os.path.join(ZERO, path))
            mark = "" if exists else " **（缺失）**"
            lines.append("| `%s` | `%s`%s |" % (path, name, mark))
        lines.append("")

    lines += ["## 三、一条贯穿的读法", "",
              "1. **`Expr.lean`** 定义 `GeoExpr n`：以点的坐标为原子的多项式表达式。",
              "2. **`Dist.lean`** 把距离的平方 `sqDist` 定义为多项式，并证明 `dist = d ⟹ sqDist = d²`"
              "（`Real.sqrt_inj`），从而消去平方根。",
              "3. **`Constraint.lean`** 把几何约束按多项式层 / 平方层分开；"
              "超越层（角度）被**排除在类型之外**，而不是假装可代数化。",
              "4. **`Loss.lean`** 把等式约束变成平方损失 `f²`；"
              "`EqConstraint` 的类型只含可损失化的层。",
              "5. **`Flatten.lean`** 把配置压成有限向量，并证明**对象层双射**。",
              "6. **`Differentiable.lean`** 证明坐标为投影，从而残差可微。",
              "7. **`Perturb.lean` + `Nondegenerate.lean`** 用坐标扰动证明残差沿方向的线性响应，"
              "这是梯度非零的基础。",
              "8. **`Exact.lean`** 接上 `Zero/Lib/Penalty/PolyExact`："
              "非退化局部极小 ⟹ 约束成立。",
              "9. **`Extract.lean`** 是反方向：从权重向量读回配置与它所满足的约束；"
              "`perp_neg_iff` 是**语义层不可逆**的一个具体实例。", "",
              "## 四、刻意不做的事", "",
              "| 未做 | 理由 |",
              "|:--|:--|",
              "| 超越层（`angle` / `equalAngle`） | 含 `Real.cos`，不可能是多项式；"
              "排除在 `GeoConstraint` 之外 |",
              "| `eqZero`（`leZero` / `ltZero`）的损失 | 不等式不是任何东西的零点集，"
              "强行写成 `g²` 是掺假 |",
              "| `collinear` 的损失 | 陈述含存在量词，未消元前无法构造损失 |",
              "| 一般 `GeoExpr` 的可微性 | 需要按表达式结构归纳；两个承载几何内容的约束不需要它 |",
              ""]

    out = os.path.join(HERE, "PROOF-CHAIN-GEO.md")
    # **W0-3c: compare, do not overwrite.**
    SYNCED.append(("gov/PROOF-CHAIN-GEO.md", sync(out, "\n".join(lines), allow_write="--write" in sys.argv)))
    print("已写:", os.path.relpath(out, ZERO))
    rc = artifact_guard.require_synced(SYNCED, "PROOF-CHAIN-GEO")
    if rc:
        return rc
    print("模块:", len(info), " 层数:", len(byrank))
    return 0


if __name__ == "__main__":
    sys.exit(main())
