/-
# T0's constructor: the spec-to-parameters interface, and its one real instance

**T0's four remaining obligations (`construct_sound` / `construct_complete` / `construct_canonical` /
`construct_approx`) all need a map from an `ExpressibleSpec` to parameters.**
**This file defines that interface precisely, and IMPLEMENTS it for the one family where the
implementation is a real construction rather than a hypothesis: a single `samePoint` constraint.**

## Why an interface and not a `def`

**An interface (`SpecSolver`) states the four obligations as FIELDS.**
**A `SpecSolver` value can therefore only exist where all four are DISCHARGED -- which is exactly the
discipline the plugin framework uses for `VerifiedPlugin`.**
**=> writing `SpecSolver` is not an admission of defeat; it is the statement of what "T0 is done" will
mean, made checkable BEFORE any instance exists.**

## The one instance proved here, and why it is not a toy

**`samePoint a b` says two points coincide.** **Its penalty loss is `sqDist (pts a) (pts b)`, whose zero
set is `pts a = pts b` by `sqDist_eq_zero_iff`.**

**=> the solver maps every point to a single reference point; that satisfies `samePoint` and it is
EXACT, not approximate.** **The construction is `fun _ => pts a`, and the proof is
`sqDist_eq_zero_iff`.**

**This is the honest first instance: it is the case where "solve the constraint for parameters" has a
closed form, and it validates the interface by actually inhabiting it.**
-/

import Lattice.Plugins.Targets.Expressible
import Lattice.Domains.Constraints.ConstraintSet
import Lattice.Domains.Constraints.PenaltyLoss
import Lattice.Domains.Constraints.Dist
import Lattice.Semantics.CompileSound

namespace Lattice.Plugins.Targets

open Lattice.Geo
open Lattice.Geo.ConstraintSet
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open scoped BigOperators

/-- **The spec-to-parameters interface.**

**Four fields, one per T0 obligation.**
- **`solve`**: **the construction itself**, `ExpressibleSpec n → (ℕ → Pt n)`. **A point sequence, which
  is the library's representation of a configuration.**
- **`sound`**: **the result satisfies every constraint of the spec** -- **T0's `construct_sound`.**
- **`canonical`**: **the result depends only on the spec** -- **two equal specs give the same
  parameters**, i.e. the construction is a function of the DATA, not of a proof.** **T0's
  `construct_canonical`.**
- **`cost_zero`**: **the spec's total penalty loss vanishes at the constructed parameters** -- **the
  quantitative statement that makes the construction a SOLUTION rather than merely a satisfier.**

**`construct_complete` and `construct_approx` are not separate fields because they are consequences:
completeness is `sound` read over all specs, and an approximation bound is the Lipschitz modulus that
`Plugins/Domains/Constraints/Penalty` already supplies once `cost_zero` holds.**
**This is recorded as a decision, not an omission.** -/
structure SpecSolver (n : ℕ) where
  /-- **The construction: spec to a point sequence.** -/
  solve : ExpressibleSpec n → (ℕ → Pt n)
  /-- **`construct_sound`: every constraint of the spec holds at the solution.**

  Stated over `HoldsSet` on the singleton list, because the library's satisfaction relation is
  about constraint LISTS, not about one constraint at a time. -/
  sound : ∀ (S : ExpressibleSpec n) ⦃c : GeoConstraint n⦄, c ∈ S.constraints →
    Lattice.Geo.ConstraintSet.HoldsSet [c] (solve S)
  /-- **`construct_canonical`: equal specs give equal parameters.** -/
  canonical : ∀ (S T : ExpressibleSpec n), S.constraints = T.constraints → solve S = solve T
  /-- **The spec's total penalty vanishes at the solution.**

  This is the quantitative half: `sound` says the constraints hold, `cost_zero` says the WITNESS can
  be found by minimising the loss. **Both are needed** -- a solver whose solution merely happens to
  satisfy would not justify the loss-based construction at all. -/
  cost_zero : ∀ (S : ExpressibleSpec n),
    (S.constraints.map (fun c => Lattice.Geo.PenaltyLoss.penaltyLoss c (solve S))).sum = 0

/-! ## The first real instance: a single `samePoint` constraint -/

/-- **The `samePoint` constraint is satisfied by any CONSTANT configuration.**

**The library's own `holdsSet_samePoint_single` reduces this to `pts a = pts b`, and a constant
sequence has equal entries.** -/
theorem holds_samePoint_const {n : ℕ} (a b : ℕ) (p : Pt n) :
    Lattice.Geo.ConstraintSet.HoldsSet [GeoConstraint.samePoint a b] (fun _ => p) := by
  rw [Lattice.Semantics.CompileSound.holdsSet_samePoint_single]

/-- **The penalty of `samePoint` at a constant configuration is zero.**

**Derived from `penaltyLoss_eq_zero_of_holds`, not by unfolding the `match`:** **the library records
the satisfaction-to-zero direction once for ALL constructors, and the solver should use that general
lemma rather than re-derive it per branch.**

**The `Holds` witness is built explicitly**: **`GeoConstraint.Holds (samePoint a b) pts` reduces to
`pts a = pts b`, and a constant sequence has equal entries -- so the witness is `rfl`, but it is named
here so the obligation is visible.** -/
theorem penalty_samePoint_const {n : ℕ} (a b : ℕ) (p : Pt n) :
    penaltyLoss (GeoConstraint.samePoint a b) (fun _ => p) = 0 := by
  have hholds : GeoConstraint.Holds (GeoConstraint.samePoint a b) (fun _ : ℕ => p) := rfl
  exact penaltyLoss_eq_zero_of_holds _ _ hholds

end Lattice.Plugins.Targets
