import Lattice.Runtime.SymbolToWeight
import Lattice.Runtime.PenaltyEmbedding
import Lattice.Lift.ApproxExact
import Lattice.Runtime.VerificationSoundness
import Lattice.Lift.EndToEndApproximation
import Lattice.Runtime.Extraction
import Lattice.Runtime.L1L2
import Lattice.Runtime.EndToEnd
import Lattice.Lift.GeoSampledBound
import Lattice.Runtime.L1L2Roundtrip
import Lattice.Runtime.NonIdenticalEncoding
import Lattice.Lift.EncodingAbstraction
import Lattice.Runtime.LossyRepresentation
import Lattice.Runtime.CompilerScheme
import Lattice.Lift.RoundingBackend
import Lattice.Lift.WeightLadder
import Lattice.Lift.ChainComposition
import Lattice.Runtime.VerifierRate
import Lattice.Lift.ApproximationBridge
import Lattice.Lift.WeightLadderN
import Lattice.Lift.TokenAlphabet
import Lattice.Lift.IntRoundtrip
import Lattice.Lift.NondegenerateInstance
import Lattice.Runtime.ErrorCalculus
import Lattice.Runtime.RepresentationFamilies
import Lattice.Lift.ApproxExtraction
import Lattice.Runtime.RatRepresentation
import Lattice.Runtime.GridDensity
import Lattice.Lift.MultiLayerLadder
import Lattice.Runtime.StackCodegen
import Lattice.Lift.ApproxLadder
import Lattice.Lift.ExtractionStrength
import Lattice.Lift.WeightLadderFullWidth
import Lattice.Lift.WeightLadderInverse
import Lattice.Lift.WeightSymbolRepresentation
import Lattice.Lift.ActivationLadder
import Lattice.Lift.WeightLadderFullWidthInstance
import Lattice.Lift.RectangularWeightEncoding
import Lattice.Lift.RectangularRepresentation
import Lattice.Lift.LayerQuantization
import Lattice.Lift.LayerQuantizationBits
import Lattice.Lift.SaturationQuantization
import Lattice.Lift.QuantErrorPropagation
import Lattice.Runtime.ProgramAST
import Lattice.Lift.StackError

/-!
# Lattice.Lift -- the representation ladder

Each module here is one rung of data <-> token <-> symbol <-> weight, and each
correctness theorem has the shape of a forward simulation (Lattice.Core.Simulation),
so that consecutive rungs compose via sim_comp.

* SymbolToWeight -- T1: compilation preserves meaning (**done**)
* PenaltyEmbedding -- T2: constraint embedding is sound (**conditional only**)
* Extraction -- T3: extraction equivalence and the reversibility boundary (**done**)

T2's boundary has to be stated wherever it is named, because its unconditional form is
FALSE and has been refuted in-tree: `PenaltyEmbedding.sound_not_exact` exhibits an
embedding whose zero-loss layer holds vacuously while every local minimiser violates the
constraint. What `embedding_sound_at_minimiser` proves is the conditional statement
"IF the embedding is exact THEN a local minimiser satisfies the constraint" -- and the
embedding being exact is exactly what no general argument delivers. See README §3.3.
-/
