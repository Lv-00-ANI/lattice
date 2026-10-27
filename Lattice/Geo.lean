import Lattice.Geo.ClosedLoop
import Lattice.Geo.Compile
import Lattice.Geo.ConjRepair
import Lattice.Geo.Constraint
import Lattice.Geo.Derivative
import Lattice.Geo.Derive
import Lattice.Geo.Differentiable
import Lattice.Geo.Dist
import Lattice.Geo.DistContinuous
import Lattice.Geo.Engine
import Lattice.Geo.Eval
import Lattice.Geo.Exact
import Lattice.Geo.Exec
import Lattice.Geo.Expr
import Lattice.Geo.ExprDeriv
import Lattice.Geo.ExprLocalMin
import Lattice.Geo.Exterior
import Lattice.Geo.ExteriorSmooth
import Lattice.Geo.Extract
import Lattice.Geo.Finite
import Lattice.Geo.Flatten
import Lattice.Geo.FlattenAgreement
import Lattice.Geo.FormDeriv
import Lattice.Geo.IRBridge
import Lattice.Geo.IRRepair
import Lattice.Geo.Initialise
import Lattice.Geo.Invariant
import Lattice.Geo.LayerExact
import Lattice.Geo.Loop
import Lattice.Geo.LoopPerp
import Lattice.Geo.Loss
import Lattice.Geo.Nondegenerate
import Lattice.Geo.PathContinuity
import Lattice.Geo.PenaltySmooth
import Lattice.Geo.Perturb
import Lattice.Geo.Pipeline
import Lattice.Geo.Plucker
import Lattice.Geo.PolyNondegenerate
import Lattice.Geo.QualityBridge
import Lattice.Geo.Repair
import Lattice.Geo.RepairBridge
import Lattice.Geo.RepairPenalty
import Lattice.Geo.RepairPerp
import Lattice.Geo.RepairQuality
import Lattice.Geo.Rules
import Lattice.Geo.Semantic
import Lattice.Geo.SeqRepresentation
import Lattice.Geo.Shape
import Lattice.Geo.Square
import Lattice.Geo.Synthesis
import Lattice.Geo.Unconditional
import Lattice.Geo.Unified
import Lattice.Geo.ApproxEmbedding
import Lattice.Geo.Lipschitz
import Lattice.Geo.DistLipschitz
import Lattice.Geo.PolyLipschitz
import Lattice.Geo.PolyAssemble
import Lattice.Geo.RhoMetric
import Lattice.Geo.GeoSampledBound
import Lattice.Geo.LadderInstance
import Lattice.Geo.PolyConstants
import Lattice.Geo.LoopRate
import Lattice.Geo.Reinjection
import Lattice.Geo.SynthesisMulti
import Lattice.Geo.ReinjectionGeneral
import Lattice.Geo.ClauseComposition
import Lattice.Geo.RepairCoverage
import Lattice.Geo.PolyRepair
import Lattice.Geo.ConstraintSet
import Lattice.Geo.EqualLengthRepair
import Lattice.Geo.PartialReinjection
import Lattice.Geo.MultistepLoop
import Lattice.Geo.SynthesisCoverage
import Lattice.Geo.MissingRepairs
import Lattice.Geo.ParallelRepair
import Lattice.Geo.PolySpecificRepair
import Lattice.Geo.ComputableExpr
import Lattice.Geo.ExecutableCheck
import Lattice.Geo.MultiSeedCoverage
import Lattice.Geo.SynthesisConnection
import Lattice.Geo.GeoLadder
import Lattice.Geo.ConstraintTokenizer
import Lattice.Geo.NondegenerateInstance
import Lattice.Geo.TokenizeStrategy
import Lattice.Geo.TokenizerPattern
import Lattice.Geo.EqConstraintTokenizer
import Lattice.Geo.RealToken
import Lattice.Geo.RealTokenRoundtrip
import Lattice.Geo.EqConstraintListTokens
import Lattice.Geo.CExprCodegen
import Lattice.Geo.CodegenLadder
import Lattice.Geo.ExecutableGeoCheck
import Lattice.Geo.WeightSideLadder
import Lattice.Geo.PenaltyLoss
import Lattice.Geo.NetLoss
import Lattice.Geo.ConstraintDescent

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










