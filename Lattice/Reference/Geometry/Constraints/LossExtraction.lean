/-
# Facade: this file now only re-exports the `Domains.Constraints.Tokens` plugin's proofs

**The proofs MOVED to `Lattice/Plugins/Domains/Constraints/Tokens/LossExtraction.lean`.**

**Kept rather than deleted because other files import it by this path; a facade containing a
PROOF would leave the obligation's real home ambiguous. This one contains only an `import`.**
-/

import Lattice.Plugins.Domains.Constraints.Tokens.LossExtraction
