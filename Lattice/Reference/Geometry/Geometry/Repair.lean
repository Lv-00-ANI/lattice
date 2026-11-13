import Mathlib
import Lattice.Plugins.Core.Repair.Repair
import Lattice.Reference.Geometry.Constraints.Loss
import Lattice.Reference.Geometry.Constraints.Constraint

/-!
# `Lattice.Geo.Repair` -- what T4 does and does not give on geometric constraints

## The question

T4 (`Lattice.Core.Repair.progress`) says: for any `Repair` instance, iterating the repair operator reaches a
satisfying point. Geometry would like that statement. This file asks whether the obvious instance
exists, and records the answer.

## The obvious instance does not exist

The tempting instance is "do nothing": `fix := id`, `μ` a characteristic function. It fails, and the
reason is structural rather than technical:

```lean
decreases : ∀ x, ¬ Sat x → μ (fix x) < μ x
```

With `fix = id` the conclusion becomes `μ x < μ x`. **No measure can satisfy it.** Writing the attempt
down and watching the field fail is the useful part: a repair loop that does not change the state cannot
converge in the sense this interface means, so `no_identity_repair` below makes that impossibility a
theorem rather than a remark.

This is why `Lattice.Lib.Linear.Residual` and `Lattice.Lib.Linear.Multivar` construct repair operators that
genuinely move the state -- the displacement is the content, not the ceremony.

## What geometry would need

A `Repair` instance for a geometric constraint needs, for each constraint, an operator that moves a
configuration onto (or closer to) the constraint's zero set, together with a measure that provably falls.
For `perpendicular` a candidate is the projection of one endpoint onto the plane orthogonal to the other
segment; for `collinear`, the projection onto the line. Neither is in this file, because constructing and
verifying them is separate work, and claiming `Repair` without a decreasing measure would be exactly the
kind of hollow instance `_archive/ZERO-ESCAPE-NOT-IMPLEMENTED.md` warns about.

## What is proved here

`no_identity_repair`: if any configuration fails the constraint, no `Repair` for it has `fix = id`. This
is a genuine statement about T4's hypotheses -- it says the interface forces movement -- and it is the
reason a trivial instance is not available to geometry.
-/

namespace Lattice.Geo

open Lattice.Core

variable {α : Type}

/-- **A repair operator cannot be the identity.**

If some point fails `Sat`, then no `Repair` instance has `fix = id`: the `decreases` law would demand
`μ x < μ x`.

This is the obstruction behind the failed trivial instance, stated so that it is not rediscovered by
experiment. It also explains why every instance in `Lattice.Lib.Linear` builds a move: the movement is
what `decreases` is about. -/
theorem no_identity_repair (R : Lattice.Core.Repair α) (hfix : R.fix = fun x => x) :
    ∀ x : α, R.Sat x := by
  intro x
  by_contra h
  have hdec : R.μ (R.fix x) < R.μ x := R.decreases x h
  rw [hfix] at hdec
  exact lt_irrefl _ hdec

/-- **Consequently, a `Repair` whose target is not universal must move the state.**

The contrapositive of `no_identity_repair`, phrased as the call to action for a geometric instance: if
some configuration fails the constraint, whatever `fix` you supply has to change configurations. -/
theorem nonid_of_not_universal (R : Lattice.Core.Repair α) (hnot : ∃ x : α, ¬ R.Sat x) :
    R.fix ≠ fun x => x := by
  intro hfix
  obtain ⟨x, hx⟩ := hnot
  exact hx (no_identity_repair R hfix x)

/-- **The progress guarantee transfers to any carrier**, geometry included.

`Repair.progress` is stated for an abstract `α`; this restates it at a geometric configuration type so
that a future instance can cite it without a type-class detour. It is the T4 statement, waiting for an
operator. -/
theorem geo_repair_progress (R : Lattice.Core.Repair (ℕ → Pt n)) :
    ∀ pts : ℕ → Pt n, ∃ m : ℕ, R.Sat (R.iterate m pts) :=
  fun pts => R.progress pts

end Lattice.Geo
