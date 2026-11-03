/-
# Facade: this file now only re-exports the `GNN` carrier's proofs

**The proofs MOVED to `Lattice/Plugins/Architectures/GNN/Proofs.lean`.**

**`Migrated` requires an obligation's `file` to sit under the plugin's own directory**, so the manifest
now names the new path and this file is no longer the home of any proof.
**Kept rather than deleted because three files import it by this path.**
**A facade containing a PROOF would defeat the purpose** -- **it would leave the obligation's real home
ambiguous. This one contains only an `import`.** -/

import Lattice.Plugins.Architectures.GNN.Proofs
