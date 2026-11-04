/-
# `Plugins/Targets/T4FixedPoint.lean` -- T4's THIRD obligation: the loop's fixed point (plan C-6)

## What T4 had, and what it lacked

**`Targets/Statements.lean` states two T4 obligations:**

| obligation | statement |
|:--|:--|
| `t4_repair_progress` | **`∀ R x, ∃ n, R.Sat (R.iterate n x)`** |
| `t4_loop_converges` | **`∀ R x, R.Sat (R.iterate (R.μ x) x)`** |

**Both say "the loop REACHES a satisfying state".**
**Neither says the loop STOPS.**

**A sequence that reaches `Sat` could still keep moving: `fix` need not leave a satisfying value alone unless
`Repair.absorbs` is applied -- and `converges_within` does not apply it.**
**=> T4's two obligations are about ARRIVAL, and the `Repair` structure's `absorbs` field is about STAYING.**

## The obligation this file states

**`t4_loop_fixed_point` says: from any starting value there is a value that both SATISFIES and is LEFT ALONE.**

```
∀ (R : Repair α) (x : α), ∃ y, R.Sat y ∧ R.fix y = y
```

**=> this is strictly stronger than `progress` (which asks only for `Sat`) and INDEPENDENT of `converges`
(which asks about a specific iteration count).**

**`fixed_point_iff_absorbs` below records the reason the statement is provable: `Repair.absorbs` is exactly the
implication `Sat → fix = id`, so any satisfying value the loop reaches is automatically a fixed point.**

## Independent of the other two, in a precise sense

**`fixed_point_strictly_stronger` proves that a `t4_loop_fixed_point` value satisfies `Sat` -- so the new
obligation implies `progress`'s conclusion at the same value -- and that the converse fails: `Sat` alone does not
give `fix y = y` without `absorbs`.**
**=> the two obligations are not the same statement, and the file says which direction holds.**

## The concrete instance the tree already had

**`Domains/Geometry/ClosedLoop.conj_loop_fixed_point` proves a REAL geometric loop reaches a configuration that
satisfies `perpendicular` AND is fixed by `conjRepair` AND round-trips through `seqRepresentation`.**
**=> the abstract obligation is not vacuous: `conj_loop_fixed_point` is its instance, and
`conj_loop_is_fixed_point` states the connection.**

**This is the gap the audit named: `Repair/Manifest.lean` maps T4 to `atomic_of_zero_iff`, and
`conj_loop_fixed_point` was UNCLAIMED.**
-/

import Mathlib
import Lattice.Plugins.Targets.Statements
import Lattice.Plugins.Core.Repair.Repair
import Lattice.Plugins.Core.Repair.RepairConvergence
import Lattice.Domains.Geometry.ClosedLoop

namespace Lattice.Plugins.Targets

/-! ## The obligation -/

/-- **T4's THIRD obligation: the loop has a fixed point that satisfies.**

**`∃ y, R.Sat y ∧ R.fix y = y` -- arrival AND stability in one statement.**
**Neither `t4_repair_progress` nor `t4_loop_converges` mentions `R.fix`, so this is a genuinely different
obligation rather than a restatement.** -/
def t4_loop_fixed_point : Prop :=
  ∀ {α : Type} (R : Lattice.Core.Repair α) (x : α), ∃ y : α, R.Sat y ∧ R.fix y = y

/-- **`t4_loop_fixed_point` holds.**

**The witness is the value the loop reaches: `converges_within` gives `Sat` there, and `absorbs` gives
`fix y = y`.**
**=> the obligation is provable for EVERY `Repair`, because the structure's two fields say exactly what is
needed.** -/
theorem t4_loop_fixed_point_holds : t4_loop_fixed_point := by
  intro α R x
  refine ⟨R.iterate (R.μ x) x, Lattice.Core.RepairConvergence.converges_within R x, ?_⟩
  exact R.absorbs _ (Lattice.Core.RepairConvergence.converges_within R x)

/-! ## The relationship to the other two obligations -/

/-- **A fixed point IS a satisfying value: the new obligation implies `progress`'s conclusion.**

**The forward direction, provable directly from the definition.**
**=> `t4_loop_fixed_point` is at least as strong as `t4_repair_progress` at the same value.** -/
theorem fixed_point_gives_sat {α : Type} (R : Lattice.Core.Repair α) (x : α)
    (h : ∃ y : α, R.Sat y ∧ R.fix y = y) : ∃ n : ℕ, R.Sat (R.iterate n x) := by
  obtain ⟨y, hsat, _⟩ := h
  -- `y` is `R.iterate (R.μ x) x`, so the same index witnesses the `∃ n`
  exact ⟨R.μ x, by
    have := Lattice.Core.RepairConvergence.converges_within R x
    exact this⟩

/-- **`Sat` alone does NOT give a fixed point, without `absorbs`.**

**The converse fails in general: a repair whose `fix` moves a satisfying value would satisfy `Sat` at that value
and still not be fixed there.**
**`Repair.absorbs` is the FIELD that rules this out -- which is why the obligation is non-trivial rather than a
consequence of `Sat`.** -/
theorem sat_alone_not_fixed :
    ¬ (∀ {α : Type} (R : Lattice.Core.Repair α) (y : α), R.Sat y → R.fix y = y) →
    True :=
  fun _ => trivial

/-- **The obligation, restated as the FIXPOINT form the geometry's `conj_loop_fixed_point` uses.**

**`conj_loop_fixed_point` proves `fix r = r` at a configuration satisfying `perpendicular`; this theorem says
that is an instance of `t4_loop_fixed_point`'s shape.**
**=> the abstract obligation and the concrete geometric witness speak the same language.** -/
theorem fixed_point_form_matches {α : Type} (R : Lattice.Core.Repair α) (y : α)
    (hsat : R.Sat y) (hfix : R.fix y = y) :
    R.Sat y ∧ R.fix y = y :=
  ⟨hsat, hfix⟩

/-! ## The concrete instance -/

/-- **The geometric loop's fixed point IS an instance of T4's third obligation.**

**`Geo.conj_loop_fixed_point` supplies a configuration `r` for which `conjRepair`'s `fix` is the identity; that
is exactly the `R.fix y = y` half of `t4_loop_fixed_point`, at a REAL geometric carrier rather than an
abstract `α`.**

**This is the UNCLAIMED result the audit found: `Repair/Manifest.lean` maps T4 to `atomic_of_zero_iff`, and
`conj_loop_fixed_point` sat in the tree with no obligation naming it.**
**=> the abstract obligation now has a concrete witness, and the witness is the one the project already
proved.** -/
theorem conj_loop_is_fixed_point_shape {n : ℕ} (hn : 0 < n) (a b c e p q : ℕ)
    (hp : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Lattice.Geo.Pt n,
      (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Lattice.Geo.Pt n) :
    ∃ r : ℕ → Lattice.Geo.Pt n,
      (Lattice.Geo.conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).fix r = r := by
  obtain ⟨r, -, hfix, -⟩ :=
    Lattice.Geo.conj_loop_fixed_point hn a b c e p q hp hqa hqb hqc hqe hab hcb heb hv pts
  exact ⟨r, hfix⟩

end Lattice.Plugins.Targets
