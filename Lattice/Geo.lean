import Lattice.Domains.ClosedLoop
import Lattice.Domains.Compile
import Lattice.Domains.ConjRepair
import Lattice.Domains.Constraint
import Lattice.Domains.Derivative
import Lattice.Domains.Derive
import Lattice.Domains.Differentiable
import Lattice.Domains.Dist
import Lattice.Domains.DistContinuous
import Lattice.Domains.Engine
import Lattice.Domains.Eval
import Lattice.Domains.Exact
import Lattice.Domains.Exec
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
import Lattice.Domains.IRBridge
import Lattice.Domains.IRRepair
import Lattice.Domains.Initialise
import Lattice.Domains.Invariant
import Lattice.Domains.LayerExact
import Lattice.Domains.Loop
import Lattice.Domains.LoopPerp
import Lattice.Domains.Loss
import Lattice.Domains.Nondegenerate
import Lattice.Domains.PathContinuity
import Lattice.Domains.PenaltySmooth
import Lattice.Domains.Perturb
import Lattice.Domains.Pipeline
import Lattice.Domains.Plucker
import Lattice.Domains.PolyNondegenerate
import Lattice.Domains.QualityBridge
import Lattice.Domains.Repair
import Lattice.Domains.RepairBridge
import Lattice.Domains.RepairPenalty
import Lattice.Domains.RepairPerp
import Lattice.Domains.RepairQuality
import Lattice.Domains.Rules
import Lattice.Domains.Semantic
import Lattice.Domains.SeqRepresentation
import Lattice.Domains.Shape
import Lattice.Domains.Square
import Lattice.Domains.Synthesis
import Lattice.Domains.Unconditional
import Lattice.Domains.Unified
import Lattice.Domains.ApproxEmbedding
import Lattice.Domains.Lipschitz
import Lattice.Domains.DistLipschitz
import Lattice.Domains.PolyLipschitz
import Lattice.Domains.PolyAssemble
import Lattice.Domains.RhoMetric
import Lattice.Domains.GeoSampledBound
import Lattice.Domains.LadderInstance
import Lattice.Domains.PolyConstants
import Lattice.Domains.LoopRate
import Lattice.Domains.Reinjection
import Lattice.Domains.SynthesisMulti
import Lattice.Domains.ReinjectionGeneral
import Lattice.Domains.ClauseComposition
import Lattice.Domains.RepairCoverage
import Lattice.Domains.PolyRepair
import Lattice.Domains.ConstraintSet
import Lattice.Domains.EqualLengthRepair
import Lattice.Domains.PartialReinjection
import Lattice.Domains.MultistepLoop
import Lattice.Domains.SynthesisCoverage
import Lattice.Domains.MissingRepairs
import Lattice.Domains.ParallelRepair
import Lattice.Domains.PolySpecificRepair
import Lattice.Domains.ComputableExpr
import Lattice.Domains.ExecutableCheck
import Lattice.Domains.MultiSeedCoverage
import Lattice.Domains.SynthesisConnection
import Lattice.Domains.GeoLadder
import Lattice.Domains.ConstraintTokenizer
import Lattice.Domains.NondegenerateInstance
import Lattice.Domains.TokenizeStrategy
import Lattice.Domains.TokenizerPattern
import Lattice.Domains.EqConstraintTokenizer
import Lattice.Domains.RealToken
import Lattice.Domains.RealTokenRoundtrip
import Lattice.Domains.EqConstraintListTokens
import Lattice.Domains.CExprCodegen
import Lattice.Domains.CodegenLadder
import Lattice.Domains.ExecutableGeoCheck
import Lattice.Domains.WeightSideLadder
import Lattice.Domains.PenaltyLoss
import Lattice.Domains.NetLoss
import Lattice.Domains.ConstraintDescent
import Lattice.Domains.WeightDescent

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










