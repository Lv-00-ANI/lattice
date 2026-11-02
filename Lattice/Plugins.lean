/-
# LATTICE Plugins

Aggregator for the plugin framework.

## Layering

`Manifest` fixes the vocabulary; `Registry` builds the registry on top of it.
Nothing here imports the rest of `Lattice`: the framework is a *meta* layer whose job is
to describe proofs that live elsewhere, so the dependency arrow runs plugin -> framework
only in the sense of `Plugin.lean` files naming the framework's types, never the reverse.
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
