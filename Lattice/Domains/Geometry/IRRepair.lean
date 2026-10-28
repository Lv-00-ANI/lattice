import Mathlib
import Lattice.Domains.Geometry.IRBridge
import Lattice.Domains.Geometry.ConjRepair
import Lattice.Domains.Geometry.LoopPerp

/-!
# `Lattice.Geo.IRRepair` -- the repair predicate in the IR's own language

## The mismatch this file closes

`Lattice.Geo.ConjRepair.conjRepair` repairs a `samePoint` and a `perpendicular` together, and states its criterion as
`GeoConstraint.Holds (.perpendicular a b c e)`. `Lattice.Geo.IRBridge` states its nine exactness theorems about
`IRConstraintLite` and proves `compileIR_sound`, which relates the two vocabularies.

Until now nothing connected them, so a reader holding an IR constraint could not reach the repair machinery, and a
reader holding a repair could not tell what IR constraints it satisfies.

## What the bridge is, and what it is not

**It is a vocabulary translation**: the repair's criterion restated as `IRHolds pts (.perpendicular ...)`. That is
what makes `compileIR_*_exact` applicable to a repair's satisfying set.

**It is not an `IRConstraintLite → Repair` translation.** `IRBridge` supplies penalties, not repairs: for each
constructor it can say `penalty pts = 0` iff the constraint holds, but it has no `fix` to offer. So "any IR
constraint set is repairable" is **not** what this file proves and is not something the project has a basis for --
a repair has to be supplied per constraint kind, as `samePointRepair`, `perpRepair` and `conjRepair` do.

Recording that distinction matters because the two claims sound alike and only one is true. -/

namespace Lattice.Geo

variable {n : ℕ}

/-- **`conjRepair`'s criterion, in the IR's vocabulary.**

The first conjunct is a `samePoint`, which `IRConstraintLite` does not carry; the second is `IRHolds` on the
perpendicular constructor, which `compileIR` sends to itself. So this is the exact form in which `IRBridge`'s
theorems can be applied to a repair. -/
theorem conjRepair_sat_iff_ir
    (a b c e p q : ℕ)
    (hp : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n,
      (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).Sat pts
      ↔ pts p = pts q
        ∧ IRHolds pts (.perpendicular a b c e : IRConstraintLite n) := by
  show pts p = pts q ∧ GeoConstraint.Holds (.perpendicular a b c e) pts
     ↔ pts p = pts q ∧ IRHolds pts (.perpendicular a b c e : IRConstraintLite n)
  rw [compileIR_sound pts (.perpendicular a b c e : IRConstraintLite n)]
  rfl

/-- **The loop reaches a configuration where the IR constraint holds**, stated with the step count.

This is the T4-side conclusion in IR vocabulary: `conjRepair.progress` gives the step count, and
`conjRepair_sat_iff_ir` translates what was reached. A caller who started from an IR constraint can read the result
without knowing how the repair is implemented. -/
theorem conjRepair_reaches_ir
    (a b c e p q : ℕ)
    (hp : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n,
      (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    ∃ m : ℕ,
      (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).fix^[m] pts p
        = (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).fix^[m] pts q
      ∧ IRHolds
          ((conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).fix^[m] pts)
          (.perpendicular a b c e : IRConstraintLite n) := by
  obtain ⟨m, hm⟩ :=
    (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).progress pts
  exact ⟨m, (conjRepair_sat_iff_ir a b c e p q hp hqa hqb hqc hqe hab hcb heb hv _).mp hm⟩

/-- **The perpendicular penalty decides the IR constraint**, restated here so a reader of this file does not have to
open `IRBridge` to see what "exactness" means for the constructor the composite repair uses. -/
theorem perp_penalty_ir_exact
    (a b c e : ℕ) (pts : ℕ → Pt n) :
    (∑ i, GeoConstraint.seg pts a b i * GeoConstraint.seg pts c e i) = 0
      ↔ IRHolds pts (.perpendicular a b c e : IRConstraintLite n) := by
  rw [compileIR_sound pts (.perpendicular a b c e : IRConstraintLite n)]
  rfl

end Lattice.Geo
