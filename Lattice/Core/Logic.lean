/-
# Facade: this file now only re-exports the `Core.Constraint` plugin's proofs

**The proofs MOVED to `Lattice/Plugins/Core/Constraint/Proofs.lean`.**

**`Migrated` requires an obligation's `file` to sit under the plugin's own directory**, so the
manifest now names the new path and this file is no longer the home of any proof.
**Kept rather than deleted because other files import it by this path; a facade containing a
PROOF would leave the obligation's real home ambiguous. This one contains only an `import`.**
-/

import Lattice.Plugins.Core.Constraint.Proofs
