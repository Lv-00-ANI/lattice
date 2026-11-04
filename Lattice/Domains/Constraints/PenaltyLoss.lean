/-
# Facade: this file now only re-exports the `Domains.Constraints.Penalty` plugin's proofs

**The proofs MOVED to `Lattice/Plugins/Domains/Constraints/Penalty/PenaltyLoss.lean`.**

**Kept rather than deleted because other files import it by this path; a facade containing a
PROOF would leave the obligation's real home ambiguous. This one contains only an `import`.**
-/

import Lattice.Plugins.Domains.Constraints.Penalty.PenaltyLoss
