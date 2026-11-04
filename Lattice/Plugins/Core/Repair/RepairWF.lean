/-
# The `Core.Repair` plugin's proofs -- MOVED from `Lattice/Core/RepairWF.lean`

**The DECLARATIONS do not change -- same names, same statements, same proofs, same
namespace.**
**The INTERNAL imports do: the five `Repair` files import each other, and those edges now name
the new modules so the dependency graph reports where the code actually lives.**
The old path is now a facade that imports this file and contains no proof.
-/

import Mathlib
import Lattice.Plugins.Core.Repair.Repair

/-!
# `Lattice.Core.RepairWF` -- T4 with an arbitrary well-founded measure

## Why a second file rather than a replacement

`Lattice.Core.Repair` fixes the measure to `Nat`, which covers natural-number arguments but not
lexicographic pairs, multiset cardinalities, or term sizes.

Generalising in place failed twice for one reason: the induction step tries to compare
`iterate k (fix y)` with `fix (iterate k y)`. Those are **different terms**, and no
`Nat.iterate` lemma equates them, because iterating from `fix y` walks the *tail* of the chain
from `y` while `fix (iterate k y)` attaches `fix` at the head.

The relation that does hold is `iterate k (fix y) = iterate (k+1) y`, proved below as
`iterate_shift` by induction on `k`. With it in hand the well-founded induction closes, and it
is obvious that no false identification of the two orders was used.

## Cost

`Sat` must be decidable (`dec`) only for the instance conversions; the progress theorem itself
does not use it. `Lattice.Core.Repair` requires no such assumption, so this file states the price
explicitly rather than hiding it.

## Why not `WellFounded.rank`

`WellFounded.rank` lands in `Ordinal` -- a well-founded relation's rank is not generally a
natural number (`0` is not in the image of `ε₀`), so there is no route from an arbitrary
`WellFounded` to a `Nat` measure. Pretending otherwise would be false.
-/

namespace Lattice.Core

universe u v

/-- A repair operator with a measure in an arbitrary well-founded order. -/
structure RepairWF (α : Type u) (β : Type v) where
  /-- Which points pass verification. -/
  Sat : α → Prop
  /-- Decidability of the target predicate. -/
  dec : DecidablePred Sat
  /-- One repair step. -/
  fix : α → α
  /-- The termination measure. -/
  μ : α → β
  /-- The well-founded comparison. -/
  lt : β → β → Prop
  /-- `lt` is well founded. -/
  wf : WellFounded lt
  /-- **Absorption.** A passing point is left alone. -/
  absorbs : ∀ x, Sat x → fix x = x
  /-- **Decrease.** A failing point strictly improves. -/
  decreases : ∀ x, ¬ Sat x → lt (μ (fix x)) (μ x)
  /-- **Atomicity.** Improvement cannot terminate off target. -/
  atomic : ∀ x, (∀ y, ¬ lt y (μ x)) → Sat x

namespace RepairWF

variable {α : Type u} {β : Type v} (R : RepairWF α β)

/-- The `n`-fold iterate. -/
def iterate (n : Nat) (x : α) : α := Nat.iterate R.fix n x

/-- One more step applies `fix` once more. Note that `fix` lands on the **outside**. -/
theorem iterate_succ (n : Nat) (x : α) :
    R.iterate (n + 1) x = R.fix (R.iterate n x) := by
  simp only [iterate, Function.iterate_succ_apply']

/-- **The shift lemma.** `k` steps from `fix y` is `k+1` steps from `y`.

This is the lemma whose absence sank two earlier attempts. It is proved by induction on `k`,
because the two sides differ in exactly one application of `fix` -- on the *inside* versus the
*outside* -- and `iterate_succ` only speaks about the outside. -/
theorem iterate_shift (k : Nat) (y : α) :
    R.iterate k (R.fix y) = R.iterate (k + 1) y := by
  induction k with
  | zero => rfl
  | succ j ihj =>
    rw [iterate_succ, ihj, ← iterate_succ]

/-- **Progress, generalised.** Every point reaches a passing state in finitely many steps.

Well-founded induction on the measure, with the motive over `α` only. The step applies the
hypothesis at `fix y` -- whose measure is strictly smaller -- and transports through
`iterate_shift`. -/
theorem progress_on_wf : ∀ x : α, ∃ n : Nat, R.Sat (R.iterate n x) := by
  intro x
  refine WellFounded.induction (C := fun z => ∀ y : α, R.μ y = z → ∃ k : Nat,
      R.Sat (R.iterate k y)) R.wf (R.μ x) ?_ x rfl
  intro z ih y hy
  by_cases hsat : R.Sat y
  · exact ⟨0, hsat⟩
  · have hlt : R.lt (R.μ (R.fix y)) z := hy ▸ R.decreases y hsat
    obtain ⟨k, hk⟩ := ih (R.μ (R.fix y)) hlt (R.fix y) rfl
    exact ⟨k + 1, by rw [← iterate_shift]; exact hk⟩

/-- **Preservation, generalised.** A passing point stays passing under any number of repairs. -/
theorem preserves_of_sat (x : α) (h : R.Sat x) (n : Nat) : R.Sat (R.iterate n x) := by
  have hid : R.iterate n x = x := by
    induction n with
    | zero => rfl
    | succ k ihk =>
      rw [iterate_succ, ihk]
      exact R.absorbs x h
  rw [hid]
  exact h

end RepairWF

/-! ## The `Nat`-measured version is an instance

The consistency check that keeps the two files from drifting: `Lattice.Core.Repair` is recovered
by choosing `lt := (· < ·)` on `Nat`, whose well-foundedness is `Nat.lt_wfRel`. -/

section Instance

variable {α : Type} (R : Repair α)

/-- A `Nat`-measured repair operator viewed as well-founded.

`Repair.atomic` says `μ x = 0 → Sat x`; the well-founded form needs "nothing is below the
minimum". The bridge is that no natural number lies below zero, so a minimal measure *is* zero. -/
noncomputable def Repair.toRepairWF [DecidablePred R.Sat] : RepairWF (α := α) (β := Nat) where
  Sat := R.Sat
  dec := inferInstance
  fix := R.fix
  μ := R.μ
  lt := (· < ·)
  wf := Nat.lt_wfRel.wf
  absorbs := R.absorbs
  decreases := fun x h => R.decreases x h
  atomic := by
    intro x hmin
    apply R.atomic x
    by_contra hne
    have hlt : R.μ x - 1 < R.μ x := by omega
    exact hmin _ hlt

end Instance

end Lattice.Core
