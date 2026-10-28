import Mathlib
import Lattice.Core.Invariant
import Lattice.Domains.Geometry.RepairQuality
import Lattice.Lib.Linear.Residual

/-!
# `Lattice.Geo.RepairQuality` at both ends -- the abstract layering instantiated

## What this file adds

`Lattice.Core.Invariant` states repair quality without assuming a carrier with points:
`Preserves P R` says a repair leaves a predicate alone, and `preserves_of_sat` says that at a *satisfying*
state this holds for **every** predicate, because the state does not move.

That statement is only worth having if it has inhabitants at both ends of the project's range. This file
supplies them:

* **geometry** -- `samePointRepair`, whose copying step destroys separation;
* **linear algebra** -- `Lattice.Lib.Linear.Residual.linearRepair`, whose metric step takes `x` to
  `x - t·a`.

## What is claimed, and what is not

Both operators are `Repair` inhabitants and both are conservative, so `preserves_of_sat` applies to each
verbatim -- that is the shared, framework-level fact. Where they differ is at *unsatisfying* states, and
`Lattice.Geo.RepairQuality.copy_not_separating` records the geometric difference in the concrete form.

An earlier revision of this file attempted an abstract refutation -- "the copying repair fails `Preserves` for
separation" -- and produced a proof with an unreachable branch and a placeholder. It is not attempted here:
`Preserves` is a statement that holds vacuously when the predicate is empty, so refuting it abstractly requires
a nonempty configuration space, and the concrete statement already says what matters. Recording the omission
is better than shipping a proof that typechecks by accident.
-/

namespace Lattice.Geo

open Lattice.Core

variable {n : ℕ}

/-- **The abstract layering applies to the geometric repair.**

At a satisfying state `samePointRepair` does not move, so it preserves every predicate whatsoever. This is
`Lattice.Core.Invariant.preserves_of_sat` instantiated, and it is the shared half of the quality scale: the
conservative layer is a theorem, not a convention. -/
theorem copy_preserves_at_sat (a b : ℕ) (pts : ℕ → Pt n)
    (h : (samePointRepair a b).Sat pts) (P : (ℕ → Pt n) → Prop) :
    P pts → P ((samePointRepair a b).fix pts) :=
  preserves_of_sat (samePointRepair a b) P pts h

/-- **The same instantiation at the projecting repair**, whose step is a rotation rather than a copy. -/
theorem project_preserves_at_sat (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n, (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) (h : (perpRepair a b c e hab hcb heb hv).Sat pts)
    (P : (ℕ → Pt n) → Prop) :
    P pts → P ((perpRepair a b c e hab hcb heb hv).fix pts) :=
  preserves_of_sat (perpRepair a b c e hab hcb heb hv) P pts h

end Lattice.Geo

namespace Lattice.Lib.Linear

open Lattice.Core

/-- **The abstract layering also applies to the linear repair.**

`linearRepair` is the linear side's inhabitant of `Repair`; at a satisfying state it preserves every
predicate. Together with the two geometric instances above, this shows the layering is not an artefact of the
geometry module -- which was the reason for moving it into the core. -/
theorem linear_repair_preserves_at_sat (a b : ℚ) (ha : a ≠ 0) (x : ℚ)
    (h : (linearRepair a b ha).Sat x) (P : ℚ → Prop) :
    P x → P ((linearRepair a b ha).fix x) :=
  preserves_of_sat (linearRepair a b ha) P x h

end Lattice.Lib.Linear
