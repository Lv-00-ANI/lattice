import Lattice.Lift.SymbolToWeight
import Lattice.Lift.PenaltyEmbedding
import Lattice.Lift.ApproxExact
import Lattice.Lift.VerificationSoundness
import Lattice.Lift.Extraction
import Lattice.Lift.L1L2
import Lattice.Lift.EndToEnd

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
