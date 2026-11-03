/-
# Target Plugins -- the nine targets T0 … T8

This is the layer that makes `ProofComplete` mean what the plan intends.

## What it contains

**`Expressible.lean`** -- **`ExpressibleSpec`, the subtype T0 was missing.** **A spec CARRIES the proof
that every member is expressible, so a function taking it cannot be handed an inexpressible one.**

**`Solver.lean`** -- **`SpecSolver`, the spec-to-parameters interface**, **with T0's four obligations as
FIELDS**, **plus the one family where the construction has a closed form (`samePoint`).**

**`MultiSolver.lean`** -- **the discovery that `SpecSolver`'s `∀ S` is TOO STRONG for a family-specific
construction**, **so `FamilySolver` is defined beside it and the `samePoint` family is solved over
lists of arbitrary length.**

**`ConstFamily.lean`** -- **the DEGENERATE-CONFIGURATION family: four constraint kinds
(`samePoint`, `midpoint`, `rightAngle`, `perpendicular`) solved by one constant configuration**,
**which is what a spec MIXING kinds needs.**

**`DegenerateSolver.lean`** -- **that family as an actual `FamilySolver` instance over lists**,
**plus a non-emptiness witness so the instance cannot be vacuous.**

**`Nondegenerate.lean`** -- **the CORRECTION of the exclusion list**: **`equalLength`, `sqDistEq` with a
vanishing radius, and `eqZero` with a vanishing expression DO belong to the family**, **and the family
is restated as a predicate (`ConstConfigOK`) rather than a closed list of constructors.**

**`Statements.lean`** -- **the nine targets as `Prop`s, with a proved/open ledger.**
-/

import Lattice.Plugins.Targets.Expressible
import Lattice.Plugins.Targets.Solver
import Lattice.Plugins.Targets.MultiSolver
import Lattice.Plugins.Targets.ConstFamily
import Lattice.Plugins.Targets.DegenerateSolver
import Lattice.Plugins.Targets.Nondegenerate
import Lattice.Plugins.Targets.Statements
