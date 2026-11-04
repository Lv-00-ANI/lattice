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

**`SolverBoundary.lean`** -- **the PROOF that `SpecSolver` is uninhabited**, **because one expressible
spec (`eqZero (const 1)`) has no model at all.** **This turns round 74's prose claim into a theorem.**

**`T2Min.lean`** -- **T2's MODULUS half**, **which the audit found absent from `ProofComplete`**:
**a local minimum of the expression penalty forces the violation to be exactly zero**, **conditional on
a non-vanishing derivative, with the counterexample that shows the condition is needed.**

**`T1Dependence.lean`** -- **T1's missing half**: **the audit found `compile_sound`'s conclusion does
not mention `R`, because `hR` pins `merged` completely.** **This file states the version where
`R.rejected`, `R.global` and `R.experts` actually participate: every UNREJECTED constraint holds.**

**`SemanticRep.lean`** -- **T1's GENERAL FORM.** **Round 83 said the gap was "a missing field"; working
it out showed the gap is the TYPE DESIGN (four independent type fields with no map between them).**
**`SemanticRepresentation` supplies the connection and `compile_sound_general` follows.**
-/

import Lattice.Plugins.Targets.Expressible
import Lattice.Plugins.Targets.Solver
import Lattice.Plugins.Targets.MultiSolver
import Lattice.Plugins.Targets.ConstFamily
import Lattice.Plugins.Targets.DegenerateSolver
import Lattice.Plugins.Targets.Nondegenerate
import Lattice.Plugins.Targets.SolverBoundary
import Lattice.Plugins.Targets.T2Min
import Lattice.Plugins.Targets.T1Dependence
import Lattice.Plugins.Targets.SemanticRep
import Lattice.Plugins.Targets.Statements
import Lattice.Plugins.Targets.Construction
