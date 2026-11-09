/-
# Domain Constraint Plugins

One plugin per concern inside `Domains/Constraints/`. Currently:

* `Penalty` -- the penalty-loss carrier (T2's object).
* `Tokens`  -- constraint tokenisation and the flattening bijection (T1 / T3).

`Penalty` is named after the carrier and `Tokens` after the concern, deliberately: the
directory holds two separable capabilities, and a single plugin named after the directory
would claim both without distinguishing them.
-/

import Lattice.Plugins.Domains.Constraints.Penalty.Manifest
import Lattice.Plugins.Domains.Constraints.Penalty.Plugin
import Lattice.Plugins.Domains.Constraints.Tokens.Manifest
import Lattice.Plugins.Domains.Constraints.Tokens.Plugin
import Lattice.Plugins.Domains.Constraints.Penalty.NetLossDerivative
import Lattice.Plugins.Domains.Constraints.Penalty.PenaltyLoss
import Lattice.Plugins.Domains.Constraints.Tokens.LossExtraction
