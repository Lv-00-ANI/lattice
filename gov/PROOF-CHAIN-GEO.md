# `Zero/Geo/` 证明链地图

> 由 `gov/proof_chain_geo.py` 生成。

本层是重建的符号侧：把几何约束变成可以喂给权重层的平方损失。

## 一、拓扑分层

依赖严格向下，无环。自底向上读：

### L0 —— 表达式基座

| 模块 | 行数 | 定理 | 依赖 |
|:--|--:|--:|:--|
| `ApproxEmbedding` | 106 | 1 | — |
| `ClauseComposition` | 171 | 6 | — |
| `ClosedLoop` | 204 | 10 | — |
| `Compile` | 99 | 2 | — |
| `ComputableExpr` | 249 | 7 | — |
| `ConjRepair` | 157 | 3 | — |
| `Constraint` | 161 | 4 | — |
| `ConstraintSet` | 175 | 7 | — |
| `ConstraintTokenizer` | 423 | 13 | — |
| `Derivative` | 94 | 3 | — |
| `Derive` | 71 | 2 | — |
| `Differentiable` | 131 | 9 | — |
| `Dist` | 129 | 8 | — |
| `DistContinuous` | 53 | 2 | — |
| `DistLipschitz` | 151 | 3 | — |
| `Engine` | 147 | 6 | — |
| `EqConstraintToken` | 275 | 8 | — |
| `EqConstraintTokenizer` | 211 | 4 | — |
| `EqConstraintTokens` | 115 | 4 | — |
| `EqualLengthRepair` | 113 | 3 | — |
| `Eval` | 98 | 3 | — |
| `Exact` | 91 | 4 | — |
| `Exec` | 132 | 6 | — |
| `ExecutableCheck` | 180 | 7 | — |
| `Expr` | 136 | 1 | — |
| `ExprDeriv` | 179 | 8 | — |
| `ExprLocalMin` | 74 | 3 | — |
| `Exterior` | 110 | 5 | — |
| `ExteriorSmooth` | 150 | 9 | — |
| `Extract` | 101 | 2 | — |
| `Finite` | 106 | 1 | — |
| `Flatten` | 131 | 4 | — |
| `FlattenAgreement` | 67 | 4 | — |
| `FormDeriv` | 158 | 8 | — |
| `GeoLadder` | 173 | 4 | — |
| `GeoSampledBound` | 79 | 1 | — |
| `IRBridge` | 307 | 13 | — |
| `IRRepair` | 86 | 3 | — |
| `Initialise` | 125 | 9 | — |
| `Invariant` | 189 | 12 | — |
| `LadderInstance` | 130 | 2 | — |
| `LayerExact` | 127 | 3 | — |
| `Lipschitz` | 260 | 11 | — |
| `Loop` | 209 | 10 | — |
| `LoopPerp` | 164 | 7 | — |
| `LoopRate` | 89 | 3 | — |
| `Loss` | 194 | 10 | — |
| `MissingRepairs` | 145 | 4 | — |
| `MultiSeedCoverage` | 165 | 5 | — |
| `MultistepLoop` | 183 | 8 | — |
| `Nondegenerate` | 307 | 13 | — |
| `NondegenerateInstance` | 143 | 6 | — |
| `ParallelRepair` | 182 | 4 | — |
| `PartialReinjection` | 158 | 6 | — |
| `PathContinuity` | 245 | 12 | — |
| `PenaltySmooth` | 105 | 4 | — |
| `Perturb` | 126 | 8 | — |
| `Pipeline` | 170 | 7 | — |
| `Plucker` | 105 | 2 | — |
| `PolyAssemble` | 128 | 4 | — |
| `PolyConstants` | 159 | 5 | — |
| `PolyLipschitz` | 114 | 1 | — |
| `PolyNondegenerate` | 210 | 8 | — |
| `PolyRepair` | 174 | 5 | — |
| `PolySpecificRepair` | 166 | 4 | — |
| `QualityBridge` | 76 | 3 | — |
| `RealToken` | 217 | 5 | — |
| `RealTokenRoundtrip` | 243 | 7 | — |
| `Reinjection` | 121 | 3 | — |
| `ReinjectionGeneral` | 134 | 5 | — |
| `Repair` | 90 | 4 | — |
| `RepairBridge` | 247 | 14 | — |
| `RepairCoverage` | 148 | 5 | — |
| `RepairPenalty` | 79 | 4 | — |
| `RepairPerp` | 193 | 6 | — |
| `RepairQuality` | 151 | 9 | — |
| `RhoMetric` | 120 | 5 | — |
| `Rules` | 135 | 1 | — |
| `Semantic` | 179 | 7 | — |
| `SeqRepresentation` | 103 | 4 | — |
| `Shape` | 204 | 3 | — |
| `Square` | 161 | 10 | — |
| `Synthesis` | 140 | 6 | — |
| `SynthesisConnection` | 158 | 7 | — |
| `SynthesisCoverage` | 179 | 7 | — |
| `SynthesisMulti` | 132 | 4 | — |
| `TokenizeStrategy` | 518 | 5 | — |
| `TokenizerPattern` | 178 | 6 | — |
| `Unconditional` | 117 | 7 | — |
| `Unified` | 91 | 4 | — |

## 二、四条靶定理在几何层中的落点

### T1 编译保语义

| 文件 | 声明 |
|:--|:--|
| `Lattice/LvFormal/Theory/CompilerCorrectness.lean` | `compile_preserves_satisfiability` **（缺失）** |

### T2 约束嵌入可靠

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Exact.lean` | `geo_penalty_exact` |
| `Lattice/Geo/Nondegenerate.lean` | `perpResid_bump` |
| `Lattice/Geo/Differentiable.lean` | `hasFDerivAt_coord` |
| `Lattice/Lib/Penalty/PolyExact.lean` | `sq_eq_zero_of_localMin` |

### T3 提取等价

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Extract.lean` | `configOf` |
| `Lattice/Geo/Extract.lean` | `perp_neg_iff` |
| `Lattice/Geo/Flatten.lean` | `flattenEquiv` |

### T4 回路收敛

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Repair.lean` | `no_identity_repair` |
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
