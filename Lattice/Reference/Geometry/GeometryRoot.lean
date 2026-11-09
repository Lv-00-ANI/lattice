import Lattice.Reference.Geometry.Geometry.ApproxEmbedding
import Lattice.Reference.Geometry.Geometry.CExprCodegen
import Lattice.Reference.Geometry.Geometry.ClauseComposition
import Lattice.Reference.Geometry.Geometry.ClosedLoop
import Lattice.Reference.Geometry.Geometry.CodegenLadder
import Lattice.Reference.Geometry.Geometry.Compile
import Lattice.Reference.Geometry.Geometry.ConjRepair
import Lattice.Reference.Geometry.Geometry.ConstraintDescent
import Lattice.Reference.Geometry.Geometry.Derivative
import Lattice.Reference.Geometry.Geometry.Derive
import Lattice.Reference.Geometry.Geometry.Engine
import Lattice.Reference.Geometry.Geometry.EqualLengthRepair
import Lattice.Reference.Geometry.Geometry.Exact
import Lattice.Reference.Geometry.Geometry.Exec
import Lattice.Reference.Geometry.Geometry.ExecutableCheck
import Lattice.Reference.Geometry.Geometry.ExecutableGeoCheck
import Lattice.Reference.Geometry.Geometry.ExprLocalMin
import Lattice.Reference.Geometry.Geometry.Exterior
import Lattice.Reference.Geometry.Geometry.ExteriorSmooth
import Lattice.Reference.Geometry.Geometry.Extract
import Lattice.Reference.Geometry.Geometry.Finite
import Lattice.Reference.Geometry.Geometry.FormDeriv
import Lattice.Reference.Geometry.Geometry.GeoLadder
import Lattice.Reference.Geometry.Geometry.GeoSampledBound
import Lattice.Reference.Geometry.Geometry.IRBridge
import Lattice.Reference.Geometry.Geometry.IRRepair
import Lattice.Reference.Geometry.Geometry.Initialise
import Lattice.Reference.Geometry.Geometry.Invariant
import Lattice.Reference.Geometry.Geometry.LadderInstance
import Lattice.Reference.Geometry.Geometry.LayerExact
import Lattice.Reference.Geometry.Geometry.Loop
import Lattice.Reference.Geometry.Geometry.LoopPerp
import Lattice.Reference.Geometry.Geometry.LoopRate
import Lattice.Reference.Geometry.Geometry.MissingRepairs
import Lattice.Reference.Geometry.Geometry.MultiSeedCoverage
import Lattice.Primitives.MultistepLoop
import Lattice.Reference.Geometry.Geometry.Nondegenerate
import Lattice.Reference.Geometry.Geometry.NondegenerateInstance
import Lattice.Reference.Geometry.Geometry.ParallelRepair
import Lattice.Reference.Geometry.Geometry.PartialReinjection
import Lattice.Reference.Geometry.Geometry.PathContinuity
import Lattice.Reference.Geometry.Geometry.PenaltySmooth
import Lattice.Reference.Geometry.Geometry.Plucker
import Lattice.Reference.Geometry.Geometry.PolyAssemble
import Lattice.Reference.Geometry.Geometry.PolyConstants
import Lattice.Reference.Geometry.Geometry.PolyLipschitz
import Lattice.Reference.Geometry.Geometry.PolyNondegenerate
import Lattice.Reference.Geometry.Geometry.PolyRepair
import Lattice.Reference.Geometry.Geometry.PolySpecificRepair
import Lattice.Reference.Geometry.Geometry.QualityBridge
import Lattice.Reference.Geometry.Geometry.Reinjection
import Lattice.Reference.Geometry.Geometry.ReinjectionGeneral
import Lattice.Reference.Geometry.Geometry.Repair
import Lattice.Reference.Geometry.Geometry.RepairBridge
import Lattice.Reference.Geometry.Geometry.RepairCoverage
import Lattice.Reference.Geometry.Geometry.RepairPenalty
import Lattice.Reference.Geometry.Geometry.RepairPerp
import Lattice.Reference.Geometry.Geometry.RepairQuality
import Lattice.Reference.Geometry.Geometry.RhoMetric
import Lattice.Reference.Geometry.Geometry.Rules
import Lattice.Reference.Geometry.Geometry.Semantic
import Lattice.Reference.Geometry.Geometry.Shape
import Lattice.Reference.Geometry.Geometry.Square
import Lattice.Reference.Geometry.Geometry.Synthesis
import Lattice.Reference.Geometry.Geometry.SynthesisConnection
import Lattice.Reference.Geometry.Geometry.SynthesisCoverage
import Lattice.Reference.Geometry.Geometry.SynthesisMulti
import Lattice.Reference.Geometry.Geometry.Unconditional
import Lattice.Reference.Geometry.Geometry.Unified
import Lattice.Primitives.WeightDescent
import Lattice.Reference.Geometry.Geometry.WeightSideLadder
import Lattice.Reference.Geometry.Geometry.AffineClass

/-!
# `Lattice.Domains.Geometry`

## 这一半是什么

几何实例、修复、循环与合成：`Domains` 的**上层**（71 个模块）。它 import `Constraints`，反向不成立。

## 边界（第 246 轮的子划分）

实测：本半对 `Constraints` 有 71 条边，而 `Constraints` 对本半为 **0**。所以这是一个真正的分层。
-/
