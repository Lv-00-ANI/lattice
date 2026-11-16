import Lattice.Lib.Fiber.FiberBridge
import Lattice.Lib.Chain.RealLv00SolverConflictDetection
import Lattice.Lib.Chain.L1BridgeHomomorphism
import Lattice.Lib.Quantization.RealCompressionStepDischarged
import Lattice.Lib.Compiler.FloatMulBoundDischarged
import Lattice.Lib.Architectures
import Lattice.Lib.Attention
import Lattice.Lib.Chain
import Lattice.Lib.Compiler
import Lattice.Lib.Concentration
import Lattice.Lib.Convex
import Lattice.Lib.Editing
import Lattice.Lib.FCA
import Lattice.Lib.InfoTheory
import Lattice.Lib.LearningTheory
import Lattice.Lib.Lift
import Lattice.Lib.Linear
import Lattice.Lib.LinearAlgebra
import Lattice.Lib.Meta
import Lattice.Lib.Optim
import Lattice.Lib.Penalty
import Lattice.Lib.Quantization
import Lattice.Lib.FloatStackRefinement
import Lattice.Lib.Architectures.RealTransformerEval
import Lattice.Lib.Penalty.QuadraticNotLipschitz
import Lattice.Lib.Penalty.QuadraticLocallyLipschitz
import Lattice.Lib.Compiler.Expressiveness
import Lattice.Lib.Compiler.ReluClosure
import Lattice.Lib.Compiler.CarrierClosure
import Lattice.Lib.Compiler.CarrierCoverage
import Lattice.Lib.Compiler.CarrierReproduction
import Lattice.Lib.Compiler.DataSynthesis
import Lattice.Lib.Compiler.CarrierAlgebra
import Lattice.Lib.Compiler.CarrierReversible
import Lattice.Lib.Compiler.CarrierInstantiation
import Lattice.Lib.Compiler.ReluLemmas
import Lattice.Lib.Compiler.ReversibilityLimit
import Lattice.Lib.Compiler.NoIntermediateLayer
import Lattice.Lib.Compiler.ReversibilityCriterion
import Lattice.Lib.Compiler.ReversibilityInstances
import Lattice.Lib.Compiler.LowerBound
import Lattice.Lib.Compiler.LowerBoundGeneral
import Lattice.Lib.Compiler.PolynomialLowerBound
import Lattice.Lib.Compiler.CarrierApproximation
import Lattice.Lib.Compiler.NonlinearApproximation
import Lattice.Lib.Compiler.HopVerdict
import Lattice.Lib.Compiler.ConvergenceForm
import Lattice.Lib.Compiler.WeightSequence
import Lattice.Lib.Compiler.ConstraintSatisfaction
/-!
# Lattice.Lib -- harvested instances

A library here is an *instance*, not a new theory: it fixes the concrete carrier and shows that
the core interfaces are inhabited by something the project cares about. The module is
deliberately thin, because the point of a first instance is to test whether the interface
suffices, not to accumulate mathematics.

* Linear.Residual -- T4 instantiated on a one-variable linear constraint over the rationals
* Linear.Multivar -- the same at arbitrary arity, over any field
* Linear.Penalty -- the squared residual is exact: its minima are its solutions
* Linear.PenaltyVector -- the vector form: sum-of-squares algebra, exactness still owed
-/
