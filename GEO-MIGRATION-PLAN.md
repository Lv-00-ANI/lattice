# Geo 层迁移分析（GEO-MIGRATION-PLAN）

> **性质：分析文件，不是迁移。** 本轮**没有移动任何 `Lattice/Geo/` 文件**——
> `Lattice/Geo/` 下唯一的改动是 21 个模块从 `Lift/` 搬进 `Runtime/` 后、它们的 import 行被改写
> （`Geo/ApproxEmbedding.lean` 从 `Lattice.Lift.EndToEndApproximation` 改为
> `Lattice.Runtime.EndToEndApproximation`），没有 rename。
>
> **依据**：`DIRECTORY-DESIGN.md` §2.4 / §2.6 / §2.8 / §9 / §10；`gov/gate.py` 的 `LAYER_OF` 与 rank 表。
> **数据**：`agent-tmp/geo_analysis.py`、`agent-tmp/geo_tables.py`（只读，可重跑；本文件 §2/§3 的表由它们生成）。
> 层名一律用 `gov/gate.py` 的 `LAYER_OF`（`core` / `slots` / `lift` / `runtime` / `lib` / `geo` / `audit` / `compose`）。

## 0. 结论

1. **结构上 Geo 可以整层搬。** 99 个模块只有内部边和**向下**边（`core` 22 条、`runtime` 18 条、`lib` 9 条、
   Mathlib 98 条），**0 条向上依赖**。这一点与 `Lift → Runtime` 相同，所以"整层改路径"不会触犯 I4。
2. **但 §10 的目标布局不是"整层改名"，是按概念多对多拆分。** 拆分把 183 条内部边的一部分变成跨目录边，
   并在 `Primitives/Train` 上直接撞 §2.6 —— **"有损"就在这里**（§6）。
3. **三个候选模块的裁决建议**（§5）：三者的**定义**（`penaltyLoss` / `netLoss` / `shiftLayer` / `linearConstraint`）
   与**事实**（下降、归零）现在同在 `Geo`；建议整体进 `Primitives/Train`（rank 4），
   **并把 §10 中 `PenaltyLoss` → `Kernel/Constraints` 那一行改掉**——因为 `PenaltyLoss` →
   `Dist` → `Lib.Linear.PenaltyVector` 把它钉在 rank > `lib`(3)，`Kernel`(rank 1) 在今天的 rank 表下是**上行**。
4. **§2.6 今天不构成阻塞，但一旦按 §5.8 把它们包成 `Primitive` 就构成阻塞**：Geo 里现有 **0 个
   `Primitive` 实例**（`grep '\bPrimitive\b' Lattice/Geo/*.lean` 只有 `ConstraintDescent.lean` 的 2 处注释），
   而 §2.6 约束的是 `Primitive` 之间的 import。详见 §5.3。

## 1. 实测事实

| 量 | 值 | 口径 |
|:--|--:|:--|
| Geo 模块数 | **99** | `Lattice/Geo/*.lean` |
| 代码行（含注释/空行） | **16,407** | `wc -l` 等价 |
| 声明（theorem/lemma/def/structure/…） | **868** | 与 `audit_counts.py` 的 `DECL` 同口径 |
| **Geo 内部边** | **183** | `import Lattice.Geo.X`，X ≠ 自身 |
| Geo → `core` | 22 条 / 17 个模块 | 见 §4 |
| Geo → `runtime` | 18 条 / 16 个模块 | 见 §4 |
| Geo → `lib` | **9 条 / 9 个模块** | 见 §4、§5.2 |
| Geo → `slots`/`lift`/`audit`/`compose`/`usage` | **0** | 实测 |
| Geo → Mathlib | 98 条 / 98 个模块 | 只有 `TokenizeStrategy` 一行 import 都没有 |
| **Geo → 上层（向上依赖）** | **0 条** | 这是"整层可搬"的全部依据 |
| 闭前缀个数 | **10** | §3 |
| Geo 的否证条数 | **6** | `REFUTATION-CENSUS.md` |
| Geo 的 PROOF-DEBT verdict | **107 条** | `agent-tmp/review/verdicts_*.jsonl`，共 1382 条 / 384 个文件 |

**外部 importer（7 个文件，+ 1 个聚合器）**。搬 Geo 的调用点改写面就是这 8 个文件：

| 文件 | 用到的 Geo 模块 |
|:--|:--|
| `Lattice/Geo.lean`（聚合器，99 个 import） | 全部 |
| `Lattice/Audit/Hypotheses.lean` | `Reinjection` |
| `Lattice/Compose/ForwardChain.lean` | `ConstraintDescent`（`netLoss_pos_of_ne`、`netLoss_zero_iff_holds`、`netLoss_step_half`、`netLoss_shiftLayer`） |
| `Lattice/Semantics/Annotations.lean` | `ConstraintSet`、`Constraint` |
| `Lattice/Semantics/CompileSound.lean` | `Constraint`、`ConstraintSet`、`WeightSideLadder` |
| `Lattice/Semantics/Merge.lean` | `ConstraintSet`、`Constraint` |
| `Lattice/Semantics/Stage1.lean` | `ConstraintSet`、`Constraint` |
| `Lattice/Usage/Examples.lean` | `ComputableExpr`、`ExecutableCheck`、`GeoSampledBound`、`Reinjection`、`Synthesis`、`PolyConstants` |

## 2. Geo 内部的 import 图（只在 Geo 内）

图是 DAG（`gov/audit_geo.py` 的环检测今天不生效，见 §5.4；本节的 DAG 结论来自 `agent-tmp/geo_analysis.py`
的闭前缀计算——如果存在环，Kahn 式前缀会留下不可达模块，实测留下 0 个）。

### A.1 每个前缀轮次的模块与 Geo 内部依赖

「内部依赖」只列 `Lattice.Geo.*` 的边；`—` 表示该模块在 Geo 内没有依赖。

**轮次 1（累计 5 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `Expr` | — |
| `MultistepLoop` | — |
| `TokenizeStrategy` | — |
| `TokenizerPattern` | — |
| `WeightDescent` | — |

**轮次 2（累计 13 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `ComputableExpr` | `Expr` |
| `ConstraintTokenizer` | `Expr` |
| `Dist` | `Expr` |
| `Flatten` | `Expr` |
| `LadderInstance` | `Expr` |
| `Lipschitz` | `Expr` |
| `RealToken` | `Expr` |
| `SeqRepresentation` | `Expr` |

**轮次 3（累计 22 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `CExprCodegen` | `ComputableExpr` |
| `Constraint` | `Dist`, `Expr` |
| `DistContinuous` | `Dist` |
| `DistLipschitz` | `Dist`, `Lipschitz` |
| `Finite` | `Expr`, `Flatten` |
| `FlattenAgreement` | `Flatten`, `SeqRepresentation` |
| `Perturb` | `Flatten` |
| `RealTokenRoundtrip` | `RealToken` |
| `RhoMetric` | `Lipschitz` |

**轮次 4（累计 31 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `CodegenLadder` | `CExprCodegen` |
| `ConstraintSet` | `Constraint` |
| `Engine` | `Constraint` |
| `Eval` | `Constraint`, `Dist` |
| `ExecutableCheck` | `ComputableExpr`, `Constraint` |
| `Invariant` | `Constraint` |
| `Loss` | `Constraint`, `Dist`, `Expr` |
| `PenaltyLoss` | `Constraint`, `Dist` |
| `RepairPerp` | `Constraint` |

**轮次 5（累计 50 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `ApproxEmbedding` | `Loss` |
| `Compile` | `Constraint`, `Loss` |
| `Derive` | `Engine` |
| `Differentiable` | `Constraint`, `Flatten`, `Loss` |
| `EqConstraintToken` | `Loss`, `RealTokenRoundtrip` |
| `EqConstraintTokenizer` | `ConstraintTokenizer`, `Loss` |
| `ExecutableGeoCheck` | `ExecutableCheck` |
| `Extract` | `Constraint`, `Flatten`, `Loss`, `Perturb` |
| `Initialise` | `Constraint`, `Invariant` |
| `Loop` | `Constraint`, `Engine` |
| `LoopPerp` | `RepairPerp` |
| `MissingRepairs` | `Constraint`, `RepairPerp` |
| `NetLoss` | `ConstraintSet`, `PenaltyLoss` |
| `Pipeline` | `Constraint`, `Expr`, `Loss` |
| `PolyLipschitz` | `DistLipschitz`, `Lipschitz`, `Loss` |
| `PolySpecificRepair` | `Constraint`, `Loss` |
| `Repair` | `Constraint`, `Loss` |
| `Rules` | `Engine` |
| `Square` | `Dist`, `Loss` |

**轮次 6（累计 66 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `ConjRepair` | `Loop`, `LoopPerp`, `RepairPerp` |
| `ConstraintDescent` | `Constraint`, `NetLoss`, `PenaltyLoss` |
| `Derivative` | `Pipeline` |
| `EqConstraintTokens` | `EqConstraintToken` |
| `Exact` | `Differentiable`, `Loss` |
| `ExprDeriv` | `Differentiable`, `Pipeline` |
| `Exterior` | `Constraint`, `Square` |
| `LoopRate` | `Loop` |
| `PolyAssemble` | `DistLipschitz`, `Lipschitz`, `Loss`, `PolyLipschitz` |
| `RepairBridge` | `Loop`, `Loss` |
| `RepairCoverage` | `Constraint`, `LoopPerp`, `RepairPerp` |
| `RepairQuality` | `Loop`, `LoopPerp` |
| `Semantic` | `Extract`, `Invariant` |
| `Shape` | `Derive` |
| `Synthesis` | `Initialise`, `Invariant` |
| `Unified` | `Loop`, `LoopPerp` |

**轮次 7（累计 85 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `ClosedLoop` | `ConjRepair`, `Flatten`, `Loop`, `SeqRepresentation` |
| `EqConstraintListTokens` | `EqConstraintTokens` |
| `EqualLengthRepair` | `Constraint`, `RepairCoverage` |
| `Exec` | `Derive`, `Shape` |
| `ExprLocalMin` | `Derivative`, `ExprDeriv` |
| `ExteriorSmooth` | `Differentiable`, `ExprDeriv`, `Exterior` |
| `FormDeriv` | `ExprDeriv`, `Perturb` |
| `GeoSampledBound` | `Lipschitz`, `PolyAssemble`, `RhoMetric` |
| `Nondegenerate` | `Derivative`, `Differentiable`, `Perturb` |
| `ParallelRepair` | `Constraint`, `RepairCoverage` |
| `PenaltySmooth` | `Differentiable`, `ExprDeriv`, `Square` |
| `Plucker` | `Exterior` |
| `PolyConstants` | `DistLipschitz`, `Lipschitz`, `PolyAssemble` |
| `PolyRepair` | `Constraint`, `RepairCoverage` |
| `QualityBridge` | `RepairQuality` |
| `Reinjection` | `Loop`, `LoopRate`, `Loss` |
| `RepairPenalty` | `Loop`, `Loss`, `RepairBridge` |
| `SynthesisCoverage` | `Constraint`, `Synthesis` |
| `SynthesisMulti` | `Synthesis` |

**轮次 8（累计 95 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `ClauseComposition` | `GeoSampledBound`, `Reinjection`, `RhoMetric`, `Synthesis` |
| `GeoLadder` | `EqConstraintListTokens`, `EqConstraintTokens`, `Loss` |
| `LayerExact` | `Plucker` |
| `MultiSeedCoverage` | `Synthesis`, `SynthesisCoverage`, `SynthesisMulti` |
| `NondegenerateInstance` | `Nondegenerate`, `Perturb` |
| `PartialReinjection` | `Loss`, `Reinjection` |
| `PolyNondegenerate` | `Derivative`, `Dist`, `ExprLocalMin`, `Loss` |
| `ReinjectionGeneral` | `LoopPerp`, `Reinjection` |
| `SynthesisConnection` | `Synthesis`, `SynthesisMulti` |
| `Unconditional` | `Derivative`, `FormDeriv` |

**轮次 9（累计 98 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `IRBridge` | `LayerExact`, `Loss` |
| `PathContinuity` | `DistContinuous`, `PolyNondegenerate` |
| `WeightSideLadder` | `Constraint`, `GeoLadder` |

**轮次 10（累计 99 个模块）**

| 模块 | Geo 内部依赖 |
|:--|:--|
| `IRRepair` | `ConjRepair`, `IRBridge`, `LoopPerp` |

### A.2 每个模块 import 的非 Geo 层

列是层；`mathlib` 是 Lean/Mathlib 本体，不是本库的层，单列出来是因为只有 1 个模块没有它。

| 模块 | 层（按 `gov/gate.py` 的 `LAYER_OF`） | Mathlib |
|:--|:--|:--|
| `ApproxEmbedding` | runtime: `EndToEndApproximation` | ✓ |
| `CExprCodegen` | runtime: `StackCodegen` | ✓ |
| `ClauseComposition` | core: `RepairMultistep`, `RepairConvergence`；runtime: `ChainComposition`, `WeightLadder` | ✓ |
| `ClosedLoop` | runtime: `Extraction` | ✓ |
| `CodegenLadder` | runtime: `EndToEnd` | ✓ |
| `Compile` | runtime: `SymbolToWeight` | ✓ |
| `ComputableExpr` | — | ✓ |
| `ConjRepair` | core: `Repair` | ✓ |
| `Constraint` | — | ✓ |
| `ConstraintDescent` | core: `Net` | ✓ |
| `ConstraintSet` | — | ✓ |
| `ConstraintTokenizer` | — | ✓ |
| `Derivative` | lib: `PolyExact` | ✓ |
| `Derive` | — | ✓ |
| `Differentiable` | — | ✓ |
| `Dist` | lib: `PenaltyVector` | ✓ |
| `DistContinuous` | — | ✓ |
| `DistLipschitz` | — | ✓ |
| `Engine` | core: `Logic` | ✓ |
| `EqConstraintListTokens` | — | ✓ |
| `EqConstraintToken` | — | ✓ |
| `EqConstraintTokenizer` | — | ✓ |
| `EqConstraintTokens` | runtime: `EndToEnd` | ✓ |
| `EqualLengthRepair` | — | ✓ |
| `Eval` | — | ✓ |
| `Exact` | lib: `PolyExact` | ✓ |
| `Exec` | — | ✓ |
| `ExecutableCheck` | — | ✓ |
| `ExecutableGeoCheck` | — | ✓ |
| `Expr` | core: `Syntax` | ✓ |
| `ExprDeriv` | — | ✓ |
| `ExprLocalMin` | — | ✓ |
| `Exterior` | — | ✓ |
| `ExteriorSmooth` | — | ✓ |
| `Extract` | — | ✓ |
| `Finite` | — | ✓ |
| `Flatten` | runtime: `Extraction` | ✓ |
| `FlattenAgreement` | — | ✓ |
| `FormDeriv` | — | ✓ |
| `GeoLadder` | runtime: `EndToEnd` | ✓ |
| `GeoSampledBound` | runtime: `GeoSampledBound` | ✓ |
| `IRBridge` | — | ✓ |
| `IRRepair` | — | ✓ |
| `Initialise` | — | ✓ |
| `Invariant` | lib: `PenaltyVector` | ✓ |
| `LadderInstance` | runtime: `EndToEnd`, `L1L2Roundtrip` | ✓ |
| `LayerExact` | — | ✓ |
| `Lipschitz` | — | ✓ |
| `Loop` | core: `Repair` | ✓ |
| `LoopPerp` | core: `Repair` | ✓ |
| `LoopRate` | core: `RepairConvergence` | ✓ |
| `Loss` | lib: `PenaltyVector` | ✓ |
| `MissingRepairs` | — | ✓ |
| `MultiSeedCoverage` | — | ✓ |
| `MultistepLoop` | core: `Repair`, `RepairConvergence` | ✓ |
| `NetLoss` | core: `Net` | ✓ |
| `Nondegenerate` | lib: `PolyExact` | ✓ |
| `NondegenerateInstance` | — | ✓ |
| `ParallelRepair` | — | ✓ |
| `PartialReinjection` | runtime: `ErrorCalculus` | ✓ |
| `PathContinuity` | — | ✓ |
| `PenaltyLoss` | — | ✓ |
| `PenaltySmooth` | — | ✓ |
| `Perturb` | — | ✓ |
| `Pipeline` | runtime: `L1L2` | ✓ |
| `Plucker` | — | ✓ |
| `PolyAssemble` | — | ✓ |
| `PolyConstants` | — | ✓ |
| `PolyLipschitz` | — | ✓ |
| `PolyNondegenerate` | — | ✓ |
| `PolyRepair` | — | ✓ |
| `PolySpecificRepair` | — | ✓ |
| `QualityBridge` | core: `Invariant`；lib: `Residual` | ✓ |
| `RealToken` | — | ✓ |
| `RealTokenRoundtrip` | — | ✓ |
| `Reinjection` | — | ✓ |
| `ReinjectionGeneral` | — | ✓ |
| `Repair` | core: `Repair` | ✓ |
| `RepairBridge` | core: `Repair`, `Invariant`, `Simulation`, `Idempotent` | ✓ |
| `RepairCoverage` | — | ✓ |
| `RepairPenalty` | — | ✓ |
| `RepairPerp` | core: `Repair`；lib: `PenaltyVector` | ✓ |
| `RepairQuality` | — | ✓ |
| `RhoMetric` | — | ✓ |
| `Rules` | — | ✓ |
| `Semantic` | — | ✓ |
| `SeqRepresentation` | runtime: `Extraction` | ✓ |
| `Shape` | — | ✓ |
| `Square` | — | ✓ |
| `Synthesis` | — | ✓ |
| `SynthesisConnection` | runtime: `EndToEnd` | ✓ |
| `SynthesisCoverage` | — | ✓ |
| `SynthesisMulti` | — | ✓ |
| `TokenizeStrategy` | — | **无** |
| `TokenizerPattern` | — | ✓ |
| `Unconditional` | — | ✓ |
| `Unified` | core: `Invariant`；lib: `Residual` | ✓ |
| `WeightDescent` | core: `Net` | ✓ |
| `WeightSideLadder` | core: `Net`；runtime: `EndToEnd` | ✓ |

## 3. 闭前缀

"闭前缀"的定义与 `Lift/` 搬迁时相同：集合 S，使 **S 内每个成员的所有 Geo 内部依赖也都在 S 里**。
只有闭集能作为一次搬动的单位——否则会出现"新路径 import 旧路径"，而那种状态**仍然编译**，
因为 `Geo/` 还在，错误不会浮出来。

| 轮次 | 本轮新增 | 累计规模 | 作为一批的增量 |
|--:|--:|--:|--:|
| 1 | 5 | 5 | 5 |
| 2 | 8 | 13 | 8 |
| 3 | 9 | 22 | 9 |
| 4 | 9 | 31 | 9 |
| 5 | 19 | 50 | 19 |
| 6 | 16 | 66 | 16 |
| 7 | 19 | 85 | 19 |
| 8 | 10 | 95 | 10 |
| 9 | 3 | 98 | 3 |
| 10 | 1 | 99 | 1 |

**推荐批次**（把"累计"当闭集用，3 批即可）：prefix 4（31 个）→ prefix 7（85 个，增量 54）→
prefix 10（99 个，增量 14）。批数少的意义是编译次数少；每次 `lake build Lattice` 在本机约 8–9 分钟
（本轮 15 个模块的搬迁实测 6515 个 target）。

## 4. 每个模块 import 的非 Geo 层

见 §2 的第二张表（逐模块列出 `core` / `runtime` / `lib` 的具体模块名，以及是否 import Mathlib）。
汇总：`core` 22 条边（17 个模块）、`runtime` 18 条（16 个模块）、`lib` **9 条（9 个模块）**。

**9 条 `Geo → lib` 边**（这是整个 Geo 迁移里唯一与 rank 表互相拉扯的东西）：

| Geo 模块 | import 的 Lib 模块 |
|:--|:--|
| `Derivative` | `Lattice.Lib.PolyExact` |
| `Dist` | `Lattice.Lib.Linear.PenaltyVector` |
| `Exact` | `Lattice.Lib.PolyExact` |
| `Invariant` | `Lattice.Lib.Linear.PenaltyVector` |
| `Loss` | `Lattice.Lib.Linear.PenaltyVector` |
| `Nondegenerate` | `Lattice.Lib.PolyExact` |
| `QualityBridge` | `Lattice.Lib.Residual` |
| `RepairPerp` | `Lattice.Lib.Linear.PenaltyVector` |
| `Unified` | `Lattice.Lib.Residual` |

`Dist` 只是**复用** `PenaltyVector.sqNorm`（`sqDist p q := sqNorm (diff p q)`），但那是定义级依赖，
不是可以"改个 import 就消失"的注释。第 228 轮把 `Lib` 钉在 rank 3 的全部理由（244 个 `Lib` 文件 import
`Lift`）依然成立，所以**不能靠把 `Lib` 降到 0 来解开这 9 条边**。

## 5. `NetLoss` / `PenaltyLoss` / `ConstraintDescent` 的裁决建议

### 5.1 §10 的原文自相矛盾

`DIRECTORY-DESIGN.md` §10 对这三个模块给了**两行不同的目标**：

| §10 的行 | 模块 | 目标 |
|:--|:--|:--|
| `Geo/Constraint`、`Expr`、`Loss`、`PenaltyLoss`、`ConstraintSet` | **`PenaltyLoss`** | `Kernel/Constraints` |
| `Geo/NetLoss`、`ConstraintDescent`、`WeightDescent` | `NetLoss`、`ConstraintDescent` | `Primitives/Train` |

也就是说：§10 把 `PenaltyLoss` 放在 `Kernel/Constraints`，把 `NetLoss`/`ConstraintDescent` 放在
`Primitives/Train`。而 `NetLoss` import `PenaltyLoss`、`ConstraintDescent` import 两者——
**§10 自己把一条依赖链拆到了两个层**，而且方向是 `Train` 在上、`Kernel` 在下（`Kernel` 1 < `Train` 4，合法），
所以只从"层级方向"看不出来；问题在**同一批模块被拆开**。

### 5.2 §2.6 必须对着实际依赖检查

§2.6 的原文：「`Primitives` 不互相 import……只 import `Kernel`/`Runtime`/`Domains`」。

实测这三者的 import（`agent-tmp/geo_tables.md` 的逐模块表）：

| 模块 | 行数 | import | 依赖链上的位置 |
|:--|--:|:--|:--|
| `PenaltyLoss` | 240 | Mathlib、`Geo.Constraint`、`Geo.Dist` | 定义 `penaltyLoss`（12 个构造子） |
| `NetLoss` | 134 | Mathlib、`Core.Net`、`Geo.ConstraintSet`、`Geo.PenaltyLoss` | 定义 `netLoss`（参数化损失） |
| `ConstraintDescent` | 378 | Mathlib、`Core.Net`、`Geo.Constraint`、`Geo.PenaltyLoss`、`Geo.NetLoss` | 步长/收敛/两步事实 |
| `WeightDescent` | 214 | Mathlib、`Core.Net` | 权重行上的下降（**Geo 内零依赖**） |

**关键事实**：`PenaltyLoss → Dist → Lattice.Lib.Linear.PenaltyVector`。`Dist` 在 rank 4，
`Lib` 在 rank 3；把 `PenaltyLoss` 放进 `Kernel`（§9 的 rank 1）会让
`PenaltyLoss → Dist` 成为**上行**（1 依赖 4），`Dist` 自己也不能下移（它 import `Lib`，而 `Lib` 在 3）。
所以 **`Kernel/Constraints` 这个目标在今天的 rank 表下不可达**，与 §10 的另一行冲突。

**§2.6 本身今天是成立的**：Geo 里 **0 个 `Primitive` 实例**（`ConstraintDescent.lean` 的 2 处 `Primitive`
都在注释里，讲的是第 228 轮把 capstone 搬去 `Compose` 的历史）。§2.6 约束的是 `Primitive` 之间，
而这三者现在是**定义 + 事实模块**，不是 `Primitive`。

**但一旦按 §5.8 把它们包成 `Primitive`，§2.6 立刻不成立**：`ConstraintDescent` 的 `Primitive` 会
import `NetLoss`/`PenaltyLoss` 的 `Primitive`（或它们的定义），而共享定义**不能下移到 `Kernel`**（§5.2 上一条）。
届时的出口只有两个，都有代价：

1. **合并成一个 `Primitives/Train` 文件**（例如 `trainLoss`）：§2.6 成立（一个文件没有"互相 import"），
   但 3 个模块 → 1 个，`PATH_MAP` 表达不了 3→1，PROOF-DEBT 的 107 条 Geo verdict 会失去 1:1 对应；
2. **修改 §2.6**，把它改成「`Primitive` 不 import 另一个 `Primitive`，但可以 import 同组的**定义模块**」，
   并把 `PenaltyLoss`/`NetLoss` 明确定位成"定义模块"、`ConstraintDescent`/`WeightDescent` 定位成"`Primitive`"。
   这条不损失模块边界，但**要改的是一条设计原则**，必须由设计文档的所有者裁决，不能由搬运顺手改。

### 5.3 建议（按代价从低到高）

| 方案 | 目标 | rank | §2.6 | I4 | 代价 |
|:--|:--|--:|:--|:--|:--|
| **A（推荐）** | 三者 + `WeightDescent` → `Primitives/Train`，作为**同组定义+事实** | 4 | **成立**（0 个 `Primitive`） | ✓（`Dist`/`Lib` 都在它下面） | 需改 §10 的 `PenaltyLoss` 行；`NetLoss`/`PenaltyLoss` 与 `ConstraintDescent` 同目录同层，**目录内 import 合法但 §2.6 的"包成 Primitive"要等 §5.2 的裁决** |
| B | `PenaltyLoss`/`NetLoss` → `Kernel/Constraints`，`ConstraintDescent` → `Primitives/Train` | 1 / 4 | ✓ | **✗** 9 条 Geo→Lib 边中的 `Loss`、以及 `PenaltyLoss→Dist` 全部上行 | 需把 `Lib` 降到 0（第 228 轮已否决，244 个文件） |
| C | 三者合并成一个 `Primitives/Train` 文件 | 4 | ✓ | ✓ | 有损：3→1，`PATH_MAP` 无法表达，定理归属改变 |
| D | 三者留在 `Geo`，只把 `WeightDescent` 搬去 `Train` | 4 | ✓ | ✓ | 不解决 §10 的目标；但 `WeightDescent` 是**唯一零 Geo 依赖**的候选（只 import `Core.Net`），可以现在就搬，且不产生任何跨目录边 |

**建议采 A，并把 `WeightDescent` 作为第一批无风险试点**（它只有一个外部 importer 也无：`Geo.lean`
聚合器；`Geo` 内无人 import 它——实测"Geo 内无人 import"名单里有 `WeightDescent`）。
A 的正文必须同时写清 §5.2 的第 2 条：**"三者今天不是 `Primitive`，所以 §2.6 成立；包成 `Primitive`
之前必须先裁决 `penaltyLoss`/`netLoss` 的定义放哪一层"**。把这句话写进 `DIRECTORY-DESIGN.md`，
比留在本文件里更不容易丢。

### 5.4 顺带发现：`gov/audit_geo.py` 今天是一条**死的**门禁

```python
IMPORT = re.compile(r"^import\s+(Zero\.Geo\.\S+)", re.M)   # 第 25 行
```

树里的 import 是 `Lattice.Geo.*`，`Zero.Geo.` **一个也匹配不到**。后果：

- `deps` 恒为空 → 第 2 节的"环检测"恒打印"无环"；
- 第 3 节的"拓扑层"恒把所有模块放在 `L0`；
- 它在 `verify_all.py` 的 `CHECKS` 里**不在 `REPORT_ONLY`**（被算作"能失败的门禁"），
  而 `main()` 恒 `return 0`。

所以"Geo 的依赖严格向下"这句话，**今天没有任何机器证据**。搬 Geo 之前应先修这条正则
（`Zero.Geo.` → `Lattice.Geo.`）；这是修守卫，不是放宽守卫。

## 6. 有损清单（**明确列出**）

1. **闭前缀是唯一安全的搬动单位**：183 条内部边、10 个闭前缀。§10 是"按概念"多对多的映射，
   按它一个概念一个概念地搬，会在中途造出"新路径 import 旧路径"的状态，而该状态**仍然编译**——
   这就是本轮 `Lift/` 必须按闭前缀搬的同一条理由。
2. **§2.6 的成立条件会被悄悄改掉**：今天成立（0 个 `Primitive`），包成 `Primitive` 后不成立。
   如果迁移只改路径、不裁决定义归属，§2.6 会从"成立"变成"名义上成立"，而守卫
   `check_primitive_independence.py`（P3 才建）届时会一次性暴露它。
3. **9 条 `Geo → lib` 边钉死 9 个模块的 rank**：`Derivative`/`Dist`/`Exact`/`Invariant`/`Loss`/
   `Nondegenerate`/`QualityBridge`/`RepairPerp`/`Unified` 不能进 rank < `lib`(3) 的目录。
   §10 已经把 `Loss` 映射到 `Kernel/Constraints`——**那一行照做会让 I4 立刻报红**。
4. **`PATH_MAP` 只能表达 1→1**：§10 的 `Geo/Repair*`、`Loop*`、`Reinjection*` 一行映射到
   **两个**目录（`Primitives/Repair` + `Domains/Geometry/Repairs`），`GeoSampledBound` 又是
   `Primitives/Verify`；拆分/合并都无法写进 `PATH_MAP`，Geo 的 **107 条 PROOF-DEBT verdict**
   会失去 join（`in_degree` 静默归 0，覆盖率表仍声称 100%）。
5. **namespace 不随路径改（§2.8）**：搬完后 `Lattice.Geo.*` 的声明会散在 6 个目录里，
   `grep 'Lattice.Geo'` 再也定位不到文件；删掉 `Lattice/Geo.lean` 后，"Geo 层"只剩 namespace 后缀。
   这不是缺陷（§2.8 明确接受），但**它是永久性的命名债**，必须进文档。
6. **新目录在 `LAYER_OF` 里没有 rank**：`gate.py` 只认 `Lattice/Core|Lift|Runtime|Lib|Slots|Geo|
   Semantics|Audit|Compose`；任何新目录（`Kernel/`、`Primitives/`、`Domains/`）今天都落到
   `top`(99) → `check_layering` **直接跳过**。第 227 轮 `Semantics` 就是这样漏掉 4 个模块 / 38 条定理的。
   搬之前必须给新目录加 rank（加规则，不是放宽规则）。
7. **`gov/audit_geo.py` 是死检查**（§5.4）：Geo 的"依赖向下"今天没有机器证据；搬完更不会有。
8. **`Lattice/Geo.lean` 聚合器**：它 import 全部 99 个模块；漏一个 → 该模块没有 olean → I7 红
   （第 239 轮 `Runtime` 的同一课）。删它则 `Lattice.lean` 的公开面要改，`Lattice.Geo` 不再是入口。
9. **计数与清册**：`REFUTATION-CENSUS` 的 `Geo 6` 要按新层重算（Geo 消失后这 6 条落到哪个层，
   取决于拆分方式）；层拆分（本轮之后是 `18 / 0 / 99 / 605`）要改；`audit_counts.py` 的
   `Geo/\s+(\d+)` 需要一行 `Geo/ 0` 或改模式——**改模式就是改守卫**，应优先保留那一行。
10. **一句裁决依据会变成假话**：`NetLoss.lean` 的模块说明写着「一个模块该在哪一层，由它 import 的
    最高层决定」，并记录它当初正因为 import 了 `Geo.PenaltyLoss` 才从 `Lift/` 被赶出来。
    按 §10 把 `PenaltyLoss` 放 `Kernel`、`NetLoss` 放 `Train` 会让这句话变成假话；按建议 A 则保留它。
    **这一处的取舍必须写进设计文档，而不是留给下一个搬运者。**

## 7. 若真要执行：前置修复与批次

**前置（先做，且每条都能独立验证）**：

1. 修 `gov/audit_geo.py` 的正则（`Zero.Geo.` → `Lattice.Geo.`），确认它报出 183 条内部边 + 0 个环；
2. 给目标目录加 `LAYER_OF` + rank（`Kernel` 不能是 1，除非 `Lib` 降到 0——见 §6.3）；
3. 写 `PATH_MAP`（1→1 的 99 条）；
4. 更新 `REFUTATION-CENSUS` 的 Geo 行与总层拆分；
5. 决定 `Lattice/Geo.lean` 的去留（删 = 改公开面；留 = 改 import 清单）。

**批次（按闭前缀，每批 `lake build` + `gate.py` + `verify_all.py`）**：

| 批次 | 闭前缀 | 模块数 | 新增 | 备注 |
|:--|--:|--:|--:|:--|
| G1 | prefix 4 | 31 | 31 | 先搬 `WeightDescent`（零依赖）也可以作为 G0 试点 |
| G2 | prefix 7 | 85 | 54 | 含 `GeoLadder`、`Reinjection`、`PolyAssemble` |
| G3 | prefix 10 | 99 | 14 | 含 `IRBridge`、`IRRepair`、`PathContinuity`、`WeightSideLadder` |

## 8. 本轮做了什么 / 没做什么

**做了**：读 `DIRECTORY-DESIGN.md` §2.4/§2.6/§2.8/§9/§10；用两个只读脚本算出 99 个模块的内部图、
10 个闭前缀、逐模块的非 Geo 依赖、9 条 `Geo → lib` 边；核对三方实际 import 后给出 §5 的建议；
逐条列出 §6 的有损项；记录 `gov/audit_geo.py` 的死正则。

**没做**：**没有移动任何 `Lattice/Geo/` 文件**；没有改任何 Geo 模块的 import（除了被 `Lift → Runtime`
搬迁强制改写的 1 处）；没有改 §2.6/§10 的文本（那是设计裁决，不是搬运）；没有给 `Kernel/Primitives/Domains`
加 rank。
