import Lattice.Core.Check
import Lattice.Core.Idempotent
import Lattice.Core.Invariant
import Lattice.Core.Logic
import Lattice.Core.Net
import Lattice.Core.Repair
import Lattice.Core.RepairWF
import Lattice.Core.Semantics
import Lattice.Core.Simulation
import Lattice.Core.Syntax
import Lattice.Core.VariableNet
import Lattice.Core.Weight
import Lattice.Core.WeightNet
import Lattice.Core.RepairConvergence
import Lattice.Core.RepairAtomicity

/-!
# `Lattice.Core` -- the authoritative semantics of LATTICE

This is the only place in the project where a *representation* is defined.
Anything that claims to be a symbol, a weight, or a layer must be an instance of
something declared here.

## Why three layers and not one

The legacy tree (`lattice/lean`) had no shared base, so the same concept was
reinvented per file: `Expr` in 4 files, `eval` in 4 files, measured with a fixed
census (`gov/tools`, M3). The fix is not "be more careful"; it is to make a second
definition of `Expr` a *compile-time* impossibility.

* `Syntax`    -- what programs *are* (inductive data)
* `Semantics` -- what programs *mean* (an interface, so it can be swapped)
* `Logic`     -- what programs *entail* (satisfaction, consequence)

The split matters because the project's central difficulty is a bridge between two
semantics, and a bridge needs both ends to be interfaces rather than concrete types.
-/

