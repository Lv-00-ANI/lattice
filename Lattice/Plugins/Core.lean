/-
# Core Plugins

Aggregator for the kernel-layer plugins. Currently:

* `Constraint` -- the constraint logic: `Satisfies` / `Entails` / `Models`, the basis of T1.
* `Repair`     -- the repair loop, the T4 Repair carrier.
-/

import Lattice.Plugins.Core.Constraint.Manifest
import Lattice.Plugins.Core.Constraint.Plugin
import Lattice.Plugins.Core.Repair.Manifest
import Lattice.Plugins.Core.Repair.Plugin
