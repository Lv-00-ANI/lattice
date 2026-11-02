/-
# Architecture Carrier Plugins

The four architecture carriers of P6. Currently:

* `GNN`  -- the graph-network carrier, the registry's first `equivariance` and `invariants` witness.
* `Norm` -- the normalisation carrier, the registry's first `idempotence` witness.

`Conv` and `DAG` follow.
-/

import Lattice.Plugins.Architectures.GNN.Manifest
import Lattice.Plugins.Architectures.GNN.Plugin
import Lattice.Plugins.Architectures.Norm.Manifest
import Lattice.Plugins.Architectures.Norm.Plugin
