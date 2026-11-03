/-
# Compose Plugins

The composition algebra -- the layer whose properties are about how plugins COMBINE rather than
about any single carrier. Currently:

* `Compose` -- sequential and parallel composition of `Primitive`s, with the unit and associativity
  laws that supply the registry's `recovery`, `spatial` and `confluence` witnesses.
-/

import Lattice.Plugins.Compose.Manifest
import Lattice.Plugins.Compose.Plugin
