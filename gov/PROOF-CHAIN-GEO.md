# `Zero/Geo/` 证明链地图

> 由 `gov/proof_chain_geo.py` 生成。

本层是重建的符号侧：把几何约束变成可以喂给权重层的平方损失。

## 一、拓扑分层

依赖严格向下，无环。自底向上读：

### L0 —— 表达式基座

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `Expr` | 136 | 1 | — |
| `Flatten` | 11 | 0 | — |
| `LossExtraction` | 11 | 0 | — |
| `NetLossDerivative` | 11 | 0 | — |
| `PenaltyLoss` | 11 | 0 | — |
| `SeqRepresentation` | 11 | 0 | — |

### L1 —— 距离与线性化

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `ComputableExpr` | 249 | 7 | Expr |
| `ConstraintTokenizer` | 420 | 12 | Expr |
| `Dist` | 135 | 9 | Expr |
| `ExprDerivative` | 229 | 8 | Expr |
| `Finite` | 106 | 1 | Expr, Flatten |
| `FlatLoss` | 527 | 19 | NetLossDerivative |
| `FlattenAgreement` | 67 | 4 | Flatten, SeqRepresentation |
| `LadderInstance` | 130 | 2 | Expr |
| `Lipschitz` | 260 | 11 | Expr |
| `Perturb` | 126 | 8 | Flatten |
| `RealToken` | 217 | 5 | Expr |

### L2 —— 约束与扰动代数

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `CExprCodegen` | 136 | 5 | ComputableExpr |
| `Constraint` | 161 | 4 | Expr, Dist |
| `DistContinuous` | 47 | 1 | Dist |
| `DistDerivative` | 119 | 5 | Dist |
| `DistLipschitz` | 182 | 4 | Lipschitz, Dist |
| `RealTokenRoundtrip` | 243 | 7 | RealToken |
| `RhoMetric` | 120 | 5 | Lipschitz |

### L3 —— 损失构造

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `CIC` | 231 | 9 | Constraint |
| `CodegenLadder` | 110 | 3 | CExprCodegen |
| `ConstraintSet` | 175 | 7 | Constraint |
| `Engine` | 290 | 14 | Constraint |
| `Eval` | 98 | 3 | Constraint, Dist |
| `ExecutableCheck` | 189 | 4 | Constraint, ComputableExpr |
| `Invariant` | 189 | 12 | Constraint |
| `Loss` | 199 | 10 | Expr, Dist, Constraint |
| `PenaltyLossDerivative` | 1288 | 44 | PenaltyLoss, DistDerivative, ExprDerivative |
| `RepairPerp` | 193 | 6 | Constraint |

### L4 —— 微分与提取

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `ApproxEmbedding` | 106 | 1 | Loss |
| `Compile` | 98 | 2 | Loss, Constraint |
| `Derive` | 71 | 2 | Engine |
| `Differentiable` | 131 | 9 | Constraint, Flatten, Loss |
| `EqConstraintToken` | 275 | 8 | RealTokenRoundtrip, Loss |
| `EqConstraintTokenizer` | 211 | 4 | ConstraintTokenizer, Loss |
| `ExecutableGeoCheck` | 237 | 7 | ExecutableCheck |
| `Extract` | 101 | 2 | Flatten, Constraint, Loss, Perturb |
| `Initialise` | 125 | 9 | Constraint, Invariant |
| `Loop` | 209 | 10 | Constraint, Engine |
| `LoopPerp` | 170 | 7 | RepairPerp |
| `MissingRepairs` | 145 | 4 | RepairPerp, Constraint |
| `NetLoss` | 268 | 7 | ConstraintSet, PenaltyLoss |
| `Pipeline` | 169 | 7 | Constraint, Expr, Loss |
| `PolyLipschitz` | 150 | 2 | Lipschitz, DistLipschitz, Loss |
| `PolySpecificRepair` | 216 | 7 | Loss, Constraint |
| `Repair` | 90 | 4 | Loss, Constraint |
| `Rules` | 135 | 1 | Engine |
| `Square` | 161 | 10 | Loss, Dist |
| `Tags` | 125 | 14 | CIC |

### L5 —— 精确性

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `ConjRepair` | 157 | 3 | Loop, LoopPerp, RepairPerp |
| `ConstraintDescent` | 524 | 21 | Constraint, PenaltyLoss, NetLoss |
| `Derivative` | 94 | 3 | Pipeline |
| `EqConstraintTokens` | 141 | 4 | EqConstraintToken |
| `Exact` | 91 | 4 | Differentiable, Loss |
| `ExprDeriv` | 179 | 8 | Differentiable, Pipeline |
| `Exterior` | 110 | 5 | Constraint, Square |
| `LoopRate` | 89 | 3 | Loop |
| `PolyAssemble` | 128 | 4 | Lipschitz, DistLipschitz, PolyLipschitz, Loss |
| `RepairBridge` | 247 | 14 | Loop, Loss |
| `RepairCoverage` | 142 | 4 | LoopPerp, Constraint, Dist, RepairPerp |
| `RepairQuality` | 151 | 9 | Loop, LoopPerp |
| `Semantic` | 179 | 7 | Invariant, Extract |
| `Shape` | 204 | 3 | Derive |
| `Synthesis` | 215 | 8 | Invariant, Initialise |
| `Unified` | 91 | 4 | Loop, LoopPerp |

### L6 —— 

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `ClosedLoop` | 203 | 10 | Loop, SeqRepresentation, ConjRepair, Flatten |
| `EqConstraintListTokens` | 199 | 7 | EqConstraintTokens |
| `EqualLengthRepair` | 113 | 3 | RepairCoverage, Constraint |
| `Exec` | 132 | 6 | Shape, Derive |
| `ExprLocalMin` | 74 | 3 | ExprDeriv, Derivative |
| `ExteriorSmooth` | 150 | 9 | Differentiable, Exterior, ExprDeriv |
| `FormDeriv` | 158 | 8 | ExprDeriv, Perturb |
| `GeoSampledBound` | 79 | 1 | Lipschitz, RhoMetric, PolyAssemble |
| `Nondegenerate` | 307 | 13 | Differentiable, Perturb, Derivative |
| `ParallelRepair` | 182 | 4 | RepairCoverage, Constraint |
| `PenaltySmooth` | 105 | 4 | Differentiable, Square, ExprDeriv |
| `Plucker` | 105 | 2 | Exterior |
| `PolyConstants` | 159 | 5 | Lipschitz, DistLipschitz, PolyAssemble |
| `PolyRepair` | 174 | 5 | RepairCoverage, Constraint |
| `QualityBridge` | 76 | 3 | RepairQuality |
| `Reinjection` | 121 | 3 | Loop, Loss, LoopRate |
| `SynthesisCoverage` | 150 | 5 | Synthesis, Constraint, Dist |
| `SynthesisMulti` | 132 | 4 | Synthesis |

### L7 —— 

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `ClauseComposition` | 171 | 6 | GeoSampledBound, RhoMetric, Reinjection, Synthesis |
| `ConstraintsRoot` | 46 | 0 | ComputableExpr, Constraint, ConstraintSet, ConstraintTokenizer, Differentiable, Dist, DistContinuous, DistLipschitz, EqConstraintListTokens, EqConstraintToken, EqConstraintTokenizer, EqConstraintTokens, Eval, Expr, ExprDeriv, Flatten, FlattenAgreement, Lipschitz, Loss, NetLoss, PenaltyLoss, Perturb, Pipeline, RealToken, RealTokenRoundtrip, SeqRepresentation, DistDerivative, ExprDerivative, PenaltyLossDerivative, NetLossDerivative, FlatLoss, LossExtraction |
| `GeoLadder` | 199 | 4 | Loss, EqConstraintTokens, EqConstraintListTokens |
| `LayerExact` | 127 | 3 | Plucker |
| `MultiSeedCoverage` | 165 | 5 | SynthesisCoverage, SynthesisMulti, Synthesis |
| `NondegenerateInstance` | 143 | 6 | Perturb, Nondegenerate |
| `PartialReinjection` | 157 | 6 | Loss, Reinjection |
| `PolyNondegenerate` | 210 | 8 | Loss, ExprLocalMin, Dist, Derivative |
| `ReinjectionGeneral` | 134 | 5 | Reinjection, LoopPerp |
| `SynthesisConnection` | 203 | 9 | Synthesis, SynthesisMulti, SynthesisCoverage |
| `Unconditional` | 117 | 7 | FormDeriv, Derivative |

### L8 —— 

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `IRBridge` | 307 | 13 | LayerExact, Loss |
| `PathContinuity` | 245 | 12 | DistContinuous, PolyNondegenerate |
| `RepairPenalty` | 239 | 10 | PartialReinjection, MissingRepairs, RepairCoverage, ParallelRepair, Loop, Loss, RepairBridge |
| `WeightSideLadder` | 298 | 9 | Constraint, GeoLadder |

### L9 —— 

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `AffineClass` | 134 | 9 | WeightSideLadder |
| `IRRepair` | 86 | 3 | IRBridge, ConjRepair, LoopPerp |

### L10 —— 

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `GeometryRoot` | 85 | 0 | ApproxEmbedding, CExprCodegen, ClauseComposition, ClosedLoop, CodegenLadder, Compile, ConjRepair, ConstraintDescent, Derivative, Derive, Engine, EqualLengthRepair, Exact, Exec, ExecutableCheck, ExecutableGeoCheck, ExprLocalMin, Exterior, ExteriorSmooth, Extract, Finite, FormDeriv, GeoLadder, GeoSampledBound, IRBridge, IRRepair, Initialise, Invariant, LadderInstance, LayerExact, Loop, LoopPerp, LoopRate, MissingRepairs, MultiSeedCoverage, Nondegenerate, NondegenerateInstance, ParallelRepair, PartialReinjection, PathContinuity, PenaltySmooth, Plucker, PolyAssemble, PolyConstants, PolyLipschitz, PolyNondegenerate, PolyRepair, PolySpecificRepair, QualityBridge, Reinjection, ReinjectionGeneral, Repair, RepairBridge, RepairCoverage, RepairPenalty, RepairPerp, RepairQuality, RhoMetric, Rules, Semantic, Shape, Square, Synthesis, SynthesisConnection, SynthesisCoverage, SynthesisMulti, Unconditional, Unified, WeightSideLadder, AffineClass |

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
