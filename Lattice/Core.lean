import Lattice.Core.IR.SpecUniqueness
import Lattice.Core.IR.CoverageMonotone
import Lattice.Core.IR.DeactivateGate
import Lattice.Core.IR.FinalSpec
import Lattice.Core.IR.CertSnapshot
import Lattice.Core.IR.UnloadEffect
import Lattice.Core.IR.MaximalScope
import Lattice.Core.IR.SlotBridge
import Lattice.Core.IR.FinSupport
import Lattice.Core.CIC.ShiftSubstOffset
import Lattice.Core.CIC.ShiftSubstOffsetProbe
import Lattice.Core.CIC.ParRedVShiftBeta
import Lattice.Core.CIC.ParSubstOneDim
import Lattice.Core.CIC.ShiftSubstJointBounded
import Lattice.Core.CIC.BoundedShift
import Lattice.Core.CIC.SubstBounded
import Lattice.Core.CIC.SubstAvoids
import Lattice.Core.CIC.ShiftSubstJointVar
import Lattice.Core.CIC.ShiftSubstJoint
import Lattice.Core.CIC.ShiftSubstFalse
import Lattice.Core.CIC.ShiftSubstFull
import Lattice.Core.CIC.ShiftSubstTotal
import Lattice.Core.CIC.ShiftSubstComplete
import Lattice.Core.CIC.ShiftSubstAbove
import Lattice.Core.CIC.ShiftSubstBinder
import Lattice.Core.CIC.ShiftSubstStable
import Lattice.Core.CIC.ShiftShiftMixed
import Lattice.Core.CIC.ShiftSubstAssembly
import Lattice.Core.CIC.ShiftSubstBoundary
import Lattice.Core.CIC.ShiftSubstLaw
import Lattice.Core.CIC.ShiftSubstCutoff
import Lattice.Core.CIC.ShiftSubstCommute
import Lattice.Core.CIC.ParallelReductionVarying
import Lattice.Core.CIC.ParSubstLemma
import Lattice.Core.CIC.TakahashiDev
import Lattice.Core.CIC.ParRedUEquivalence
import Lattice.Core.CIC.ParallelReductionComplete
import Lattice.Core.CIC.ParallelReductionZero
import Lattice.Core.CIC.ParRedSBridge
import Lattice.Core.CIC.ParallelReductionAligned
import Lattice.Core.CIC.ReducesCongruence
import Lattice.Core.CIC.ParallelReduction
import Lattice.Core.CIC.TypeUniqProof
import Lattice.Core.CIC.TypeUniqPrereq
import Lattice.Core.CIC.TypeUniqueness
import Lattice.Core.CIC.HasTypeW
import Lattice.Core.CIC.Conversion
import Lattice.Core.CIC.PiShapeBridge
import Lattice.Core.CIC.PiShapeRDomain
import Lattice.Core.CIC.PiShapeRDirection
import Lattice.Core.CIC.PiShapeR
import Lattice.Core.CIC.ProgressComplete
import Lattice.Core.CIC.PiShape
import Lattice.Core.CIC.ProgressNoConsts
import Lattice.Core.CIC.ProgressEnv
import Lattice.Core.CIC.Progress
import Lattice.Core.CIC.CanonicalForm
import Lattice.Core.CIC.HasTypeHeadForm
import Lattice.Core.CIC.HeadForm
import Lattice.Core.CIC.Spine
import Lattice.Core.CIC.NeutralClosed
import Lattice.Core.CIC.HasType
import Lattice.Core.CIC.Neutrality
import Lattice.Core.CIC.ProgressFalse
import Lattice.Core.CIC.ValueTriviality
import Lattice.Core.CIC.InstLiftShiftGeneral
import Lattice.Core.CIC.ShiftAsInst
import Lattice.Core.CIC.InstShiftZero
import Lattice.Core.CIC.RouteCObstruction
import Lattice.Core.CIC.SubstSizeBound
import Lattice.Core.CIC.NormalizationAssembly
import Lattice.Core.CIC.NormalFormWF
import Lattice.Core.CIC.NormalFormFailure
import Lattice.Core.CIC.TermSize
import Lattice.Core.CIC.InstLiftSixOfSeven
import Lattice.Core.CIC.InstLiftCutoff
import Lattice.Core.CIC.InstShiftObstruction
import Lattice.Core.CIC.SubstCompParallel
import Lattice.Core.CIC.BinderCommutationFalse
import Lattice.Core.CIC.ShiftCommGeneral
import Lattice.Core.Data
import Lattice.Core.Check
import Lattice.Core.Idempotent
import Lattice.Core.Invariant
import Lattice.Core.Logic
import Lattice.Core.Net
import Lattice.Core.Repair
import Lattice.Core.RepairWF
import Lattice.Core.Semantics
import Lattice.Core.Simulation
import Lattice.Core.Syntax
import Lattice.Core.VariableNet
import Lattice.Core.Weight
import Lattice.Core.WeightNet
import Lattice.Core.RepairConvergence
import Lattice.Core.RepairAtomicity
import Lattice.Core.RepairMultistep
import Lattice.Core.OneStepBridge
import Lattice.Core.Activation
import Lattice.Core.StackParams
import Lattice.Core.StackDerivative
import Lattice.Core.AnalysisHelper
import Lattice.Core.NonlinearLayer
import Lattice.Core.VariableActLayer
import Lattice.Core.VariableDerivative
import Lattice.Core.ModelArtifact
import Lattice.Core.ModelArtifactInstances
import Lattice.Core.CIC.Syntax
import Lattice.Core.CIC.Typing
import Lattice.Core.CIC.Substitution
import Lattice.Core.CIC.Reduction
import Lattice.Core.ArchParams
import Lattice.Core.ArchWeights
import Lattice.Core.ArchAssemble
import Lattice.Core.ArchChain
import Lattice.Core.ArchChainEval
import Lattice.Core.CastLemmas
import Lattice.Core.ChainCastAct
import Lattice.Core.ChainEvalFinal
import Lattice.Core.CIC.SubstitutionShift
import Lattice.Core.CIC.ShiftComm
import Lattice.Core.CIC.ReductionOriented
import Lattice.Core.CIC.Normalization
import Lattice.Core.CIC.ShiftNonComm
import Lattice.Core.CIC.SubstTable
import Lattice.Core.CIC.SubstComp
import Lattice.Core.CIC.ParallelSubst
import Lattice.Core.CIC.SubstBridge
import Lattice.Core.CIC.ParallelSubstCutoff
import Lattice.Core.CIC.LiftAtCutoff
import Lattice.Core.CIC.LiftShiftTotal
import Lattice.Core.CIC.Value
import Lattice.Core.CIC.Compile
import Lattice.Core.CIC.PairBounds
import Lattice.Core.IR.Basic
import Lattice.Core.IR.Relations
import Lattice.Core.IR.Compile
import Lattice.Core.IR.Skeleton
import Lattice.Core.IR.Parse
import Lattice.Core.IR.Depends
import Lattice.Core.IR.Chain
import Lattice.Core.IR.Unique
import Lattice.Core.IR.Obligations
import Lattice.Core.IR.T4Repair
import Lattice.Core.IR.Modulus
import Lattice.Core.IR.ArchGraph
import Lattice.Core.IR.Lifecycle
import Lattice.Core.IR.Confluence
import Lattice.Core.PluginComplete
import Lattice.Core.CIC.SubstShiftAnalysis
import Lattice.Core.IR.Materialize
import Lattice.Core.IR.IsIR
import Lattice.Core.IR.Canonical
import Lattice.Core.IR.Penalty
import Lattice.Core.IR.Semantics
import Lattice.Core.IR.Decode
import Lattice.Core.IR.DecodeRelations
import Lattice.Core.IR.Extract


/-!
# `Lattice.Core` -- the authoritative semantics of LATTICE

This is the only place in the project where a *representation* is defined.
Anything that claims to be a symbol, a weight, or a layer must be an instance of
something declared here.

## Why three layers and not one

The legacy tree (`lattice/lean`) had no shared base, so the same concept was
reinvented per file: `Expr` in 4 files, `eval` in 4 files, measured with a fixed
census (`gov/tools`, M3). The fix is not "be more careful"; it is to make a second
definition of `Expr` a *compile-time* impossibility.

* `Syntax`    -- what programs *are* (inductive data)
* `Semantics` -- what programs *mean* (an interface, so it can be swapped)
* `Logic`     -- what programs *entail* (satisfaction, consequence)

The split matters because the project's central difficulty is a bridge between two
semantics, and a bridge needs both ends to be interfaces rather than concrete types.
-/

