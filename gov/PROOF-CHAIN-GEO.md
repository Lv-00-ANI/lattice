# `Zero/Geo/` 证明链地图

> 由 `gov/proof_chain_geo.py` 生成。

本层是重建的符号侧：把几何约束变成可以喂给权重层的平方损失。

## 一、拓扑分层

依赖严格向下，无环。自底向上读：

### L0 —— 表达式基座

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `Lattice.Domains.AffineClass` | 134 | 9 | WeightSideLadder |
| `Lattice.Domains.ApproxEmbedding` | 106 | 1 | Loss |
| `Lattice.Domains.CExprCodegen` | 136 | 5 | ComputableExpr |
| `Lattice.Domains.ClauseComposition` | 171 | 6 | GeoSampledBound, RhoMetric, Reinjection, Synthesis |
| `Lattice.Domains.ClosedLoop` | 203 | 10 | Loop, SeqRepresentation, ConjRepair, Flatten |
| `Lattice.Domains.CodegenLadder` | 110 | 3 | CExprCodegen |
| `Lattice.Domains.Compile` | 98 | 2 | Loss, Constraint |
| `Lattice.Domains.ComputableExpr` | 249 | 7 | Expr |
| `Lattice.Domains.ConjRepair` | 157 | 3 | Loop, LoopPerp, RepairPerp |
| `Lattice.Domains.Constraint` | 161 | 4 | Expr, Dist |
| `Lattice.Domains.ConstraintDescent` | 524 | 21 | Constraint, PenaltyLoss, NetLoss |
| `Lattice.Domains.ConstraintSet` | 175 | 7 | Constraint |
| `Lattice.Domains.ConstraintTokenizer` | 420 | 12 | Expr |
| `Lattice.Domains.Constraints` | 43 | 0 | ComputableExpr, Constraint, ConstraintSet, ConstraintTokenizer, Differentiable, Dist, DistContinuous, DistLipschitz, EqConstraintListTokens, EqConstraintToken, EqConstraintTokenizer, EqConstraintTokens, Eval, Expr, ExprDeriv, Flatten, FlattenAgreement, Lipschitz, Loss, NetLoss, PenaltyLoss, Perturb, Pipeline, RealToken, RealTokenRoundtrip, SeqRepresentation, DistDerivative, ExprDerivative, PenaltyLossDerivative |
| `Lattice.Domains.Derivative` | 94 | 3 | Pipeline |
| `Lattice.Domains.Derive` | 71 | 2 | Engine |
| `Lattice.Domains.Differentiable` | 131 | 9 | Constraint, Flatten, Loss |
| `Lattice.Domains.Dist` | 135 | 9 | Expr |
| `Lattice.Domains.DistContinuous` | 47 | 1 | Dist |
| `Lattice.Domains.DistDerivative` | 119 | 5 | Dist |
| `Lattice.Domains.DistLipschitz` | 182 | 4 | Lipschitz, Dist |
| `Lattice.Domains.Engine` | 290 | 14 | Constraint |
| `Lattice.Domains.EqConstraintListTokens` | 199 | 7 | EqConstraintTokens |
| `Lattice.Domains.EqConstraintToken` | 275 | 8 | RealTokenRoundtrip, Loss |
| `Lattice.Domains.EqConstraintTokenizer` | 211 | 4 | ConstraintTokenizer, Loss |
| `Lattice.Domains.EqConstraintTokens` | 141 | 4 | EqConstraintToken |
| `Lattice.Domains.EqualLengthRepair` | 113 | 3 | RepairCoverage, Constraint |
| `Lattice.Domains.Eval` | 98 | 3 | Constraint, Dist |
| `Lattice.Domains.Exact` | 91 | 4 | Differentiable, Loss |
| `Lattice.Domains.Exec` | 132 | 6 | Shape, Derive |
| `Lattice.Domains.ExecutableCheck` | 189 | 4 | Constraint, ComputableExpr |
| `Lattice.Domains.ExecutableGeoCheck` | 237 | 7 | ExecutableCheck |
| `Lattice.Domains.Expr` | 136 | 1 | — |
| `Lattice.Domains.ExprDeriv` | 179 | 8 | Differentiable, Pipeline |
| `Lattice.Domains.ExprDerivative` | 229 | 8 | Expr |
| `Lattice.Domains.ExprLocalMin` | 74 | 3 | ExprDeriv, Derivative |
| `Lattice.Domains.Exterior` | 110 | 5 | Constraint, Square |
| `Lattice.Domains.ExteriorSmooth` | 150 | 9 | Differentiable, Exterior, ExprDeriv |
| `Lattice.Domains.Extract` | 101 | 2 | Flatten, Constraint, Loss, Perturb |
| `Lattice.Domains.Finite` | 106 | 1 | Expr, Flatten |
| `Lattice.Domains.Flatten` | 130 | 4 | Expr |
| `Lattice.Domains.FlattenAgreement` | 67 | 4 | Flatten, SeqRepresentation |
| `Lattice.Domains.FormDeriv` | 158 | 8 | ExprDeriv, Perturb |
| `Lattice.Domains.GeoLadder` | 199 | 4 | Loss, EqConstraintTokens, EqConstraintListTokens |
| `Lattice.Domains.GeoSampledBound` | 79 | 1 | Lipschitz, RhoMetric, PolyAssemble |
| `Lattice.Domains.Geometry` | 85 | 0 | ApproxEmbedding, CExprCodegen, ClauseComposition, ClosedLoop, CodegenLadder, Compile, ConjRepair, ConstraintDescent, Derivative, Derive, Engine, EqualLengthRepair, Exact, Exec, ExecutableCheck, ExecutableGeoCheck, ExprLocalMin, Exterior, ExteriorSmooth, Extract, Finite, FormDeriv, GeoLadder, GeoSampledBound, IRBridge, IRRepair, Initialise, Invariant, LadderInstance, LayerExact, Loop, LoopPerp, LoopRate, MissingRepairs, MultiSeedCoverage, Nondegenerate, NondegenerateInstance, ParallelRepair, PartialReinjection, PathContinuity, PenaltySmooth, Plucker, PolyAssemble, PolyConstants, PolyLipschitz, PolyNondegenerate, PolyRepair, PolySpecificRepair, QualityBridge, Reinjection, ReinjectionGeneral, Repair, RepairBridge, RepairCoverage, RepairPenalty, RepairPerp, RepairQuality, RhoMetric, Rules, Semantic, Shape, Square, Synthesis, SynthesisConnection, SynthesisCoverage, SynthesisMulti, Unconditional, Unified, WeightSideLadder, AffineClass |
| `Lattice.Domains.IRBridge` | 307 | 13 | LayerExact, Loss |
| `Lattice.Domains.IRRepair` | 86 | 3 | IRBridge, ConjRepair, LoopPerp |
| `Lattice.Domains.Initialise` | 125 | 9 | Constraint, Invariant |
| `Lattice.Domains.Invariant` | 189 | 12 | Constraint |
| `Lattice.Domains.LadderInstance` | 130 | 2 | Expr |
| `Lattice.Domains.LayerExact` | 127 | 3 | Plucker |
| `Lattice.Domains.Lipschitz` | 260 | 11 | Expr |
| `Lattice.Domains.Loop` | 209 | 10 | Constraint, Engine |
| `Lattice.Domains.LoopPerp` | 170 | 7 | RepairPerp |
| `Lattice.Domains.LoopRate` | 89 | 3 | Loop |
| `Lattice.Domains.Loss` | 199 | 10 | Expr, Dist, Constraint |
| `Lattice.Domains.MissingRepairs` | 145 | 4 | RepairPerp, Constraint |
| `Lattice.Domains.MultiSeedCoverage` | 165 | 5 | SynthesisCoverage, SynthesisMulti, Synthesis |
| `Lattice.Domains.NetLoss` | 268 | 7 | ConstraintSet, PenaltyLoss |
| `Lattice.Domains.Nondegenerate` | 307 | 13 | Differentiable, Perturb, Derivative |
| `Lattice.Domains.NondegenerateInstance` | 143 | 6 | Perturb, Nondegenerate |
| `Lattice.Domains.ParallelRepair` | 182 | 4 | RepairCoverage, Constraint |
| `Lattice.Domains.PartialReinjection` | 157 | 6 | Loss, Reinjection |
| `Lattice.Domains.PathContinuity` | 245 | 12 | DistContinuous, PolyNondegenerate |
| `Lattice.Domains.PenaltyLoss` | 912 | 36 | Constraint, Dist, Lipschitz, DistLipschitz, PolyLipschitz |
| `Lattice.Domains.PenaltyLossDerivative` | 143 | 9 | PenaltyLoss, DistDerivative, ExprDerivative |
| `Lattice.Domains.PenaltySmooth` | 105 | 4 | Differentiable, Square, ExprDeriv |
| `Lattice.Domains.Perturb` | 126 | 8 | Flatten |
| `Lattice.Domains.Pipeline` | 169 | 7 | Constraint, Expr, Loss |
| `Lattice.Domains.Plucker` | 105 | 2 | Exterior |
| `Lattice.Domains.PolyAssemble` | 128 | 4 | Lipschitz, DistLipschitz, PolyLipschitz, Loss |
| `Lattice.Domains.PolyConstants` | 159 | 5 | Lipschitz, DistLipschitz, PolyAssemble |
| `Lattice.Domains.PolyLipschitz` | 150 | 2 | Lipschitz, DistLipschitz, Loss |
| `Lattice.Domains.PolyNondegenerate` | 210 | 8 | Loss, ExprLocalMin, Dist, Derivative |
| `Lattice.Domains.PolyRepair` | 174 | 5 | RepairCoverage, Constraint |
| `Lattice.Domains.PolySpecificRepair` | 216 | 7 | Loss, Constraint |
| `Lattice.Domains.QualityBridge` | 76 | 3 | RepairQuality |
| `Lattice.Domains.RealToken` | 217 | 5 | Expr |
| `Lattice.Domains.RealTokenRoundtrip` | 243 | 7 | RealToken |
| `Lattice.Domains.Reinjection` | 121 | 3 | Loop, Loss, LoopRate |
| `Lattice.Domains.ReinjectionGeneral` | 134 | 5 | Reinjection, LoopPerp |
| `Lattice.Domains.Repair` | 90 | 4 | Loss, Constraint |
| `Lattice.Domains.RepairBridge` | 247 | 14 | Loop, Loss |
| `Lattice.Domains.RepairCoverage` | 142 | 4 | LoopPerp, Constraint, Dist, RepairPerp |
| `Lattice.Domains.RepairPenalty` | 79 | 4 | Loop, Loss, RepairBridge |
| `Lattice.Domains.RepairPerp` | 193 | 6 | Constraint |
| `Lattice.Domains.RepairQuality` | 151 | 9 | Loop, LoopPerp |
| `Lattice.Domains.RhoMetric` | 120 | 5 | Lipschitz |
| `Lattice.Domains.Rules` | 135 | 1 | Engine |
| `Lattice.Domains.Semantic` | 179 | 7 | Invariant, Extract |
| `Lattice.Domains.SeqRepresentation` | 102 | 4 | Expr |
| `Lattice.Domains.Shape` | 204 | 3 | Derive |
| `Lattice.Domains.Square` | 161 | 10 | Loss, Dist |
| `Lattice.Domains.Synthesis` | 215 | 8 | Invariant, Initialise |
| `Lattice.Domains.SynthesisConnection` | 158 | 7 | Synthesis, SynthesisMulti |
| `Lattice.Domains.SynthesisCoverage` | 150 | 5 | Synthesis, Constraint, Dist |
| `Lattice.Domains.SynthesisMulti` | 132 | 4 | Synthesis |
| `Lattice.Domains.Unconditional` | 117 | 7 | FormDeriv, Derivative |
| `Lattice.Domains.Unified` | 91 | 4 | Loop, LoopPerp |
| `Lattice.Domains.WeightSideLadder` | 298 | 9 | Constraint, GeoLadder |

## 二、四条靶定理在几何层中的落点

### T1 编译保语义

| 文件 | 声明 |
|:--|:--|
| `Lattice/LvFormal/Theory/CompilerCorrectness.lean` | `compile_preserves_satisfiability` **（缺失）** |

### T2 约束嵌入可靠

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Exact.lean` | `geo_penalty_exact` **（缺失）** |
| `Lattice/Geo/Nondegenerate.lean` | `perpResid_bump` **（缺失）** |
| `Lattice/Geo/Differentiable.lean` | `hasFDerivAt_coord` **（缺失）** |
| `Lattice/Lib/Penalty/PolyExact.lean` | `sq_eq_zero_of_localMin` |

### T3 提取等价

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Extract.lean` | `configOf` **（缺失）** |
| `Lattice/Geo/Extract.lean` | `perp_neg_iff` **（缺失）** |
| `Lattice/Geo/Flatten.lean` | `flattenEquiv` **（缺失）** |

### T4 回路收敛

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Repair.lean` | `no_identity_repair` **（缺失）** |
| `Lattice/Core/Repair.lean` | `progress` |

## 三、一条贯穿的读法

1. **`Expr.lean`** 定义 `GeoExpr n`：以点的坐标为原子的多项式表达式。
2. **`Dist.lean`** 把距离的平方 `sqDist` 定义为多项式，并证明 `dist = d ⟹ sqDist = d²`（`Real.sqrt_inj`），从而消去平方根。
3. **`Constraint.lean`** 把几何约束按多项式层 / 平方层分开；超越层（角度）被**排除在类型之外**，而不是假装可代数化。
4. **`Loss.lean`** 把等式约束变成平方损失 `f²`；`EqConstraint` 的类型只含可损失化的层。
5. **`Flatten.lean`** 把配置压成有限向量，并证明**对象层双射**。
6. **`Differentiable.lean`** 证明坐标为投影，从而残差可微。
7. **`Perturb.lean` + `Nondegenerate.lean`** 用坐标扰动证明残差沿方向的线性响应，这是梯度非零的基础。
8. **`Exact.lean`** 接上 `Zero/Lib/Penalty/PolyExact`：非退化局部极小 ⟹ 约束成立。
9. **`Extract.lean`** 是反方向：从权重向量读回配置与它所满足的约束；`perp_neg_iff` 是**语义层不可逆**的一个具体实例。

## 四、刻意不做的事

| 未做 | 理由 |
|:--|:--|
| 超越层（`angle` / `equalAngle`） | 含 `Real.cos`，不可能是多项式；排除在 `GeoConstraint` 之外 |
| `eqZero`（`leZero` / `ltZero`）的损失 | 不等式不是任何东西的零点集，强行写成 `g²` 是掺假 |
| `collinear` 的损失 | 陈述含存在量词，未消元前无法构造损失 |
| 一般 `GeoExpr` 的可微性 | 需要按表达式结构归纳；两个承载几何内容的约束不需要它 |
