import Lattice.Domains.Geometry.ClosedLoop
import Lattice.Domains.Geometry.Compile
import Lattice.Domains.Geometry.ConjRepair
import Lattice.Domains.Constraints.Constraint
import Lattice.Domains.Geometry.Derivative
import Lattice.Domains.Geometry.Derive
import Lattice.Domains.Constraints.Differentiable
import Lattice.Domains.Constraints.Dist
import Lattice.Domains.Constraints.DistContinuous
import Lattice.Domains.Geometry.Engine
import Lattice.Domains.Constraints.Eval
import Lattice.Domains.Geometry.Exact
import Lattice.Domains.Geometry.Exec
import Lattice.Domains.Constraints.Expr
import Lattice.Domains.Constraints.ExprDeriv
import Lattice.Domains.Geometry.ExprLocalMin
import Lattice.Domains.Geometry.Exterior
import Lattice.Domains.Geometry.ExteriorSmooth
import Lattice.Domains.Geometry.Extract
import Lattice.Domains.Geometry.Finite
import Lattice.Domains.Constraints.Flatten
import Lattice.Domains.Constraints.FlattenAgreement
import Lattice.Domains.Geometry.FormDeriv
import Lattice.Domains.Geometry.IRBridge
import Lattice.Domains.Geometry.IRRepair
import Lattice.Domains.Geometry.Initialise
import Lattice.Domains.Geometry.Invariant
import Lattice.Domains.Geometry.LayerExact
import Lattice.Domains.Geometry.Loop
import Lattice.Domains.Geometry.LoopPerp
import Lattice.Domains.Constraints.Loss
import Lattice.Domains.Geometry.Nondegenerate
import Lattice.Domains.Geometry.PathContinuity
import Lattice.Domains.Geometry.PenaltySmooth
import Lattice.Domains.Constraints.Perturb
import Lattice.Domains.Constraints.Pipeline
import Lattice.Domains.Geometry.Plucker
import Lattice.Domains.Geometry.PolyNondegenerate
import Lattice.Domains.Geometry.QualityBridge
import Lattice.Domains.Geometry.Repair
import Lattice.Domains.Geometry.RepairBridge
import Lattice.Domains.Geometry.RepairPenalty
import Lattice.Domains.Geometry.RepairPerp
import Lattice.Domains.Geometry.RepairQuality
import Lattice.Domains.Geometry.Rules
import Lattice.Domains.Geometry.Semantic
import Lattice.Domains.Constraints.SeqRepresentation
import Lattice.Domains.Geometry.Shape
import Lattice.Domains.Geometry.Square
import Lattice.Domains.Geometry.Synthesis
import Lattice.Domains.Geometry.Unconditional
import Lattice.Domains.Geometry.Unified
import Lattice.Domains.Geometry.ApproxEmbedding
import Lattice.Domains.Constraints.Lipschitz
import Lattice.Domains.Constraints.DistLipschitz
import Lattice.Domains.Geometry.PolyLipschitz
import Lattice.Domains.Geometry.PolyAssemble
import Lattice.Domains.Geometry.RhoMetric
import Lattice.Domains.Geometry.GeoSampledBound
import Lattice.Domains.Geometry.LadderInstance
import Lattice.Domains.Geometry.PolyConstants
import Lattice.Domains.Geometry.LoopRate
import Lattice.Domains.Geometry.Reinjection
import Lattice.Domains.Geometry.SynthesisMulti
import Lattice.Domains.Geometry.ReinjectionGeneral
import Lattice.Domains.Geometry.ClauseComposition
import Lattice.Domains.Geometry.RepairCoverage
import Lattice.Domains.Geometry.PolyRepair
import Lattice.Domains.Constraints.ConstraintSet
import Lattice.Domains.Geometry.EqualLengthRepair
import Lattice.Domains.Geometry.PartialReinjection
import Lattice.Domains.Geometry.MultistepLoop
import Lattice.Domains.Geometry.SynthesisCoverage
import Lattice.Domains.Geometry.MissingRepairs
import Lattice.Domains.Geometry.ParallelRepair
import Lattice.Domains.Geometry.PolySpecificRepair
import Lattice.Domains.Constraints.ComputableExpr
import Lattice.Domains.Geometry.ExecutableCheck
import Lattice.Domains.Geometry.MultiSeedCoverage
import Lattice.Domains.Geometry.SynthesisConnection
import Lattice.Domains.Geometry.GeoLadder
import Lattice.Domains.Constraints.ConstraintTokenizer
import Lattice.Domains.Geometry.NondegenerateInstance
import Lattice.Domains.Constraints.TokenizeStrategy
import Lattice.Domains.Constraints.TokenizerPattern
import Lattice.Domains.Constraints.EqConstraintTokenizer
import Lattice.Domains.Constraints.RealToken
import Lattice.Domains.Constraints.RealTokenRoundtrip
import Lattice.Domains.Constraints.EqConstraintListTokens
import Lattice.Domains.Geometry.CExprCodegen
import Lattice.Domains.Geometry.CodegenLadder
import Lattice.Domains.Geometry.ExecutableGeoCheck
import Lattice.Domains.Geometry.WeightSideLadder
import Lattice.Domains.Constraints.PenaltyLoss
import Lattice.Domains.Constraints.NetLoss
import Lattice.Domains.Geometry.ConstraintDescent
import Lattice.Domains.Geometry.WeightDescent

/-!
# `Lattice.Geo` -- geometric constraints over `n`-dimensional points

This layer is the symbolic side of the chain the project set out to build:

```
几何约束 (lvLang/IR 的设计意图)
      │  用 Lattice.Geo.Expr / Constraint 重建
      ▼
  多项式约束
      │  Lattice.Geo.Loss：约束 → 平方损失 f²
      ▼
  平方损失
      │  Lattice.Lib.Penalty.PolyExact：局部极小 ⟹ 残差为零（需 ∇f ≠ 0）
      ▼
  权重（Lattice.Core.WeightNet / Lattice.Lib.Linear.PenaltyMatrix）
```

## Why it is a rebuild rather than an adaptation of Lv-00's `IR.lean`

`_archive/IR-DEFECTS.md` records the four defects that make adaptation uneconomic --
the most serious being that `IRExpr.var` evaluates to the `x` coordinate only, so the second component
of a point is unreachable from any expression.

This layer keeps what was good in Lv-00 (the fifteen geometric predicates, and in particular a
`saturates`-style semantics that covers every constructor) and fixes what was not:

* coordinates carry their **point index and axis**, so no component is unreachable;
* the carrier is `Fin n → ℝ`, matching `Lattice.Lib.Linear`, instead of the hardcoded `ℝ × ℝ`;
* `sqrt` and `div` are **absent from the expression layer** and the square root is eliminated once, in
  `Lattice.Geo.Dist`, where the side conditions it costs are stated rather than hidden.

## What is owed

**`GeoConstraint` 的 12 个构造子现在都有 penalty loss**（`Geo/PenaltyLoss.lean`，第 198 轮）。
本节此前写的是「`leZero`/`ltZero` 没有 penalty loss：不等式不是任何东西的零点集，
硬套 `g²` 会是虚构」——**那句话对「零集恰好等于解集」是对的，但结论下得太早**：
`(max e 0)²` 的零集是 `e ≤ 0`，**它恰好是 `leZero` 的解集**，所以 `leZero` 是精确可表示的。
只有**严格**不等式（`ltZero`/`gtZero`）因为解集是开集而只能松弛，**那条限制仍然成立**。
下面的原文保留，作为当时的判断记录：
and forcing a `g²` form onto it would be a fiction. `collinear` is polynomial but its statement carries
an existential, so it has no loss either until the existential is eliminated.
-/










