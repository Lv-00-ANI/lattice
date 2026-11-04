/-
# Facade: this file now only re-exports the `Extractors.ChainSlot` plugin's proofs

**The proofs MOVED to `Lattice/Plugins/Extractors/ChainSlot/VariableDerivative.lean`.**

**This file carried 4,867 lines -- the whole variable-derivative extraction line.**
**Kept rather than deleted because three files import it by this path; a facade containing a
PROOF would leave the obligation's real home ambiguous. This one contains only an `import`.**
-/

import Lattice.Plugins.Extractors.ChainSlot.VariableDerivative
