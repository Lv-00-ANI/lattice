/-
# Facade: this file now only re-exports the `Norm` carrier's proofs

**The proofs MOVED to `Lattice/Plugins/Architectures/Norm/Proofs.lean`.**

**`Migrated` requires an obligation's `file` to sit under the plugin's own directory**, so the manifest
now names the new path and this file is no longer the home of any proof.
**It is kept, rather than deleted, because four files import it by this path**
(`Lib/Architectures.lean`, `Lib/Optim/RealSeamBridges.lean`, `Lib/Optim/RealSeamBridges2.lean`, and the
plugin itself).
**=> deleting it would force edits to four importers for no benefit; a facade keeps the old path working
while making the new one authoritative.**

**A facade that contains a PROOF would defeat the purpose**: it would leave the obligation's real home
ambiguous. **This one contains only imports.** -/

import Lattice.Plugins.Architectures.Norm.Proofs
