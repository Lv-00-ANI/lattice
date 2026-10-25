import Lattice.Lift.SymbolToWeight
import Lattice.Lift.PenaltyEmbedding
import Lattice.Lift.Extraction
import Lattice.Lift.L1L2
import Lattice.Lift.EndToEnd

/-!
# Lattice.Lift -- the representation ladder

Each module here is one rung of data <-> token <-> symbol <-> weight, and each
correctness theorem has the shape of a forward simulation (Lattice.Core.Simulation),
so that consecutive rungs compose via sim_comp.

* SymbolToWeight -- T1: compilation preserves meaning (**done**)
* PenaltyEmbedding -- T2: constraint embedding is sound (**done**)
* Extraction -- T3: extraction equivalence and the reversibility boundary (**done**)
-/
