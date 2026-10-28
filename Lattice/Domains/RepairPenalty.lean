import Mathlib
import Lattice.Domains.Loop
import Lattice.Domains.Loss
import Lattice.Domains.RepairBridge

/-!
# `Lattice.Geo.RepairPenalty` -- the loop's criterion *is* a penalty's zero set

## Why a separate file

Two files have to meet here and neither may import the other:

* `Lattice.Geo.Loop` defines `samePointRepair`, whose `Sat` is `Holds (.samePoint a b)`;
* `Lattice.Geo.Loss` defines `EqConstraint.loss` and proves `loss = 0 ↔ Holds (eqToGeo c)`.

`Loop` cannot import `Loss` (the penalty is downstream of the constraints the loop operates on), and `Loss`
cannot import `Loop` (that would put the repair machinery under the penalty layer). A third file that imports
both is the ordinary resolution: the join lives above the two things it joins, which is also where a reader
would look for it.

## What the join says

The objective's fourth target asks that the verification loop *not destroy semantics*, and the second says that
a constraint is embedded reliably when its penalty decides it. Put together: **a repair that stops is a repair
whose penalty has reached zero**. Neither theorem states that alone --

* `Repair.progress` says the loop reaches `Sat`;
* `loss_eq_zero_toGeo_samePoint` says `Sat` and "penalty zero" are the same condition;

and the composition is what lets a training procedure read a zero penalty as evidence about the symbolic side.

## Liveness note

Every theorem below is outside any comment and reachable from `Lattice.Geo`'s public surface; `gov/audit_liveness.py`
checks that mechanically, because a theorem written inside a docstring is one Lean never sees.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The `samePoint` repair's criterion is the `samePoint` penalty's zero set.**

`samePointRepair`'s `Sat` is `Holds (.samePoint a b)`, and `EqConstraint.loss` vanishes exactly on that
constraint through `eqToGeo`. Chaining the two is the T4-to-T2 join for the one repair the geometry layer ships. -/
theorem samePoint_penalty_iff_sat (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) pts = 0
      ↔ (samePointRepair a b).Sat pts := by
  rw [loss_eq_zero_toGeo_samePoint]
  rfl

/-- **The `samePoint` loop reaches a zero of the penalty.**

An instance of `Lattice.Core.Repair.repair_success_is_penalty_zero` at the geometry repair, with the equivalence
supplied by `samePoint_penalty_iff_sat`. The conclusion is about the penalty, not about `Sat`: this is the form a
caller who has been watching a loss curve can use. -/
theorem samePoint_loop_reaches_penalty_zero (a b : ℕ) (pts : ℕ → Pt n) :
    ∃ k : ℕ, EqConstraint.loss (.samePoint a b) ((samePointRepair a b).fix^[k] pts) = 0 :=
  Lattice.Core.Repair.repair_success_is_penalty_zero
    (samePointRepair a b)
    (fun p => EqConstraint.loss (.samePoint a b) p)
    (fun p => (samePoint_penalty_iff_sat a b p).symm) pts

/-- **A satisfying state has zero penalty**, the converse direction, stated because a caller may arrive holding
satisfaction and need the penalty form. -/
theorem samePoint_sat_implies_penalty_zero (a b : ℕ) (pts : ℕ → Pt n)
    (h : (samePointRepair a b).Sat pts) :
    EqConstraint.loss (.samePoint a b) pts = 0 :=
  (samePoint_penalty_iff_sat a b pts).mpr h

/-- **The join is not vacuous**: `repair_success_is_penalty_zero` needs a real equivalence, and this records that
the one above is an equivalence rather than a one-way implication. -/
theorem samePoint_penalty_zero_iff_sat_iff (a b : ℕ) :
    (∀ pts : ℕ → Pt n,
        EqConstraint.loss (.samePoint a b) pts = 0 ↔ (samePointRepair a b).Sat pts) :=
  fun pts => samePoint_penalty_iff_sat a b pts

end Lattice.Geo
