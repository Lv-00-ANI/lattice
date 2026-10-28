import Lattice.Domains.Geometry.ApproxEmbedding
import Lattice.Domains.Geometry.CExprCodegen
import Lattice.Domains.Geometry.ClauseComposition
import Lattice.Domains.Geometry.ClosedLoop
import Lattice.Domains.Geometry.CodegenLadder
import Lattice.Domains.Geometry.Compile
import Lattice.Domains.Geometry.ConjRepair
import Lattice.Domains.Geometry.ConstraintDescent
import Lattice.Domains.Geometry.Derivative
import Lattice.Domains.Geometry.Derive
import Lattice.Domains.Geometry.Engine
import Lattice.Domains.Geometry.EqualLengthRepair
import Lattice.Domains.Geometry.Exact
import Lattice.Domains.Geometry.Exec
import Lattice.Domains.Geometry.ExecutableCheck
import Lattice.Domains.Geometry.ExecutableGeoCheck
import Lattice.Domains.Geometry.ExprLocalMin
import Lattice.Domains.Geometry.Exterior
import Lattice.Domains.Geometry.ExteriorSmooth
import Lattice.Domains.Geometry.Extract
import Lattice.Domains.Geometry.Finite
import Lattice.Domains.Geometry.FormDeriv
import Lattice.Domains.Geometry.GeoLadder
import Lattice.Domains.Geometry.GeoSampledBound
import Lattice.Domains.Geometry.IRBridge
import Lattice.Domains.Geometry.IRRepair
import Lattice.Domains.Geometry.Initialise
import Lattice.Domains.Geometry.Invariant
import Lattice.Domains.Geometry.LadderInstance
import Lattice.Domains.Geometry.LayerExact
import Lattice.Domains.Geometry.Loop
import Lattice.Domains.Geometry.LoopPerp
import Lattice.Domains.Geometry.LoopRate
import Lattice.Domains.Geometry.MissingRepairs
import Lattice.Domains.Geometry.MultiSeedCoverage
import Lattice.Primitives.MultistepLoop
import Lattice.Domains.Geometry.Nondegenerate
import Lattice.Domains.Geometry.NondegenerateInstance
import Lattice.Domains.Geometry.ParallelRepair
import Lattice.Domains.Geometry.PartialReinjection
import Lattice.Domains.Geometry.PathContinuity
import Lattice.Domains.Geometry.PenaltySmooth
import Lattice.Domains.Geometry.Plucker
import Lattice.Domains.Geometry.PolyAssemble
import Lattice.Domains.Geometry.PolyConstants
import Lattice.Domains.Geometry.PolyLipschitz
import Lattice.Domains.Geometry.PolyNondegenerate
import Lattice.Domains.Geometry.PolyRepair
import Lattice.Domains.Geometry.PolySpecificRepair
import Lattice.Domains.Geometry.QualityBridge
import Lattice.Domains.Geometry.Reinjection
import Lattice.Domains.Geometry.ReinjectionGeneral
import Lattice.Domains.Geometry.Repair
import Lattice.Domains.Geometry.RepairBridge
import Lattice.Domains.Geometry.RepairCoverage
import Lattice.Domains.Geometry.RepairPenalty
import Lattice.Domains.Geometry.RepairPerp
import Lattice.Domains.Geometry.RepairQuality
import Lattice.Domains.Geometry.RhoMetric
import Lattice.Domains.Geometry.Rules
import Lattice.Domains.Geometry.Semantic
import Lattice.Domains.Geometry.Shape
import Lattice.Domains.Geometry.Square
import Lattice.Domains.Geometry.Synthesis
import Lattice.Domains.Geometry.SynthesisConnection
import Lattice.Domains.Geometry.SynthesisCoverage
import Lattice.Domains.Geometry.SynthesisMulti
import Lattice.Domains.Geometry.Unconditional
import Lattice.Domains.Geometry.Unified
import Lattice.Primitives.WeightDescent
import Lattice.Domains.Geometry.WeightSideLadder

/-!
# `Lattice.Domains.Geometry`

## 这一半是什么

几何实例、修复、循环与合成：`Domains` 的**上层**（71 个模块）。它 import `Constraints`，反向不成立。

## 边界（第 246 轮的子划分）

实测：本半对 `Constraints` 有 71 条边，而 `Constraints` 对本半为 **0**。所以这是一个真正的分层。
-/