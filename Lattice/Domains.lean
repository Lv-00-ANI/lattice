import Lattice.Domains.ApproxEmbedding
import Lattice.Domains.CExprCodegen
import Lattice.Domains.ClauseComposition
import Lattice.Domains.ClosedLoop
import Lattice.Domains.CodegenLadder
import Lattice.Domains.Compile
import Lattice.Domains.ComputableExpr
import Lattice.Domains.ConjRepair
import Lattice.Domains.Constraint
import Lattice.Domains.ConstraintDescent
import Lattice.Domains.ConstraintSet
import Lattice.Domains.ConstraintTokenizer
import Lattice.Domains.Derivative
import Lattice.Domains.Derive
import Lattice.Domains.Differentiable
import Lattice.Domains.Dist
import Lattice.Domains.DistContinuous
import Lattice.Domains.DistLipschitz
import Lattice.Domains.Engine
import Lattice.Domains.EqConstraintListTokens
import Lattice.Domains.EqConstraintToken
import Lattice.Domains.EqConstraintTokenizer
import Lattice.Domains.EqConstraintTokens
import Lattice.Domains.EqualLengthRepair
import Lattice.Domains.Eval
import Lattice.Domains.Exact
import Lattice.Domains.Exec
import Lattice.Domains.ExecutableCheck
import Lattice.Domains.ExecutableGeoCheck
import Lattice.Domains.Expr
import Lattice.Domains.ExprDeriv
import Lattice.Domains.ExprLocalMin
import Lattice.Domains.Exterior
import Lattice.Domains.ExteriorSmooth
import Lattice.Domains.Extract
import Lattice.Domains.Finite
import Lattice.Domains.Flatten
import Lattice.Domains.FlattenAgreement
import Lattice.Domains.FormDeriv
import Lattice.Domains.GeoLadder
import Lattice.Domains.GeoSampledBound
import Lattice.Domains.IRBridge
import Lattice.Domains.IRRepair
import Lattice.Domains.Initialise
import Lattice.Domains.Invariant
import Lattice.Domains.LadderInstance
import Lattice.Domains.LayerExact
import Lattice.Domains.Lipschitz
import Lattice.Domains.Loop
import Lattice.Domains.LoopPerp
import Lattice.Domains.LoopRate
import Lattice.Domains.Loss
import Lattice.Domains.MissingRepairs
import Lattice.Domains.MultiSeedCoverage
import Lattice.Domains.MultistepLoop
import Lattice.Domains.NetLoss
import Lattice.Domains.Nondegenerate
import Lattice.Domains.NondegenerateInstance
import Lattice.Domains.ParallelRepair
import Lattice.Domains.PartialReinjection
import Lattice.Domains.PathContinuity
import Lattice.Domains.PenaltyLoss
import Lattice.Domains.PenaltySmooth
import Lattice.Domains.Perturb
import Lattice.Domains.Pipeline
import Lattice.Domains.Plucker
import Lattice.Domains.PolyAssemble
import Lattice.Domains.PolyConstants
import Lattice.Domains.PolyLipschitz
import Lattice.Domains.PolyNondegenerate
import Lattice.Domains.PolyRepair
import Lattice.Domains.PolySpecificRepair
import Lattice.Domains.QualityBridge
import Lattice.Domains.RealToken
import Lattice.Domains.RealTokenRoundtrip
import Lattice.Domains.Reinjection
import Lattice.Domains.ReinjectionGeneral
import Lattice.Domains.Repair
import Lattice.Domains.RepairBridge
import Lattice.Domains.RepairCoverage
import Lattice.Domains.RepairPenalty
import Lattice.Domains.RepairPerp
import Lattice.Domains.RepairQuality
import Lattice.Domains.RhoMetric
import Lattice.Domains.Rules
import Lattice.Domains.Semantic
import Lattice.Domains.SeqRepresentation
import Lattice.Domains.Shape
import Lattice.Domains.Square
import Lattice.Domains.Synthesis
import Lattice.Domains.SynthesisConnection
import Lattice.Domains.SynthesisCoverage
import Lattice.Domains.SynthesisMulti
import Lattice.Domains.TokenizeStrategy
import Lattice.Domains.TokenizerPattern
import Lattice.Domains.Unconditional
import Lattice.Domains.Unified
import Lattice.Domains.WeightDescent
import Lattice.Domains.WeightSideLadder

/-!
# `Lattice.Domains` —— 领域实例层（Geo 搬迁的第一站）

按 `DIRECTORY-DESIGN.md` §3，`Domains/` 放领域实例。它是 `Geo/` 的搬迁目标之一。

## 为什么是 rank 3（与 `lib` 同级）

第 242 轮**传递**测量（不是直接 import）：99 个 `Geo` 模块里

| 需要的 rank | 模块数 |
|--:|--:|
| 0 | 11 |
| 2 | 8 |
| **3** | **80** |

**80 个传递依赖 `Lib`**，所以它们只能落在 rank >= 3。
`Kernel`（rank 1）装不下——那正是 §10 的 `Kernel/Constraints` 行被推翻的原因。

## 为什么这一批是「rank 0」的 11 个

这 11 个在任何 rank 都合法，所以搬动**不可能**产生新的向上依赖。**先搬不可能错的。**

## 为什么暂时是平铺，而不是 `Domains/Geometry`

§10 把它们分到 `Domains/Geometry`、`Domains/Constraints`、`Primitives/*`，
但那个划分取决于 `GEO-MIGRATION-PLAN.md` §3 的三条路线（A/B/C）——**尚未裁决**。
平铺是**正确的中间态**；之后的子划分是同层内的 `git mv`。
-/