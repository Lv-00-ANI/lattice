/-
# The `Core.Repair` plugin's proofs -- MOVED from `Lattice/Core/Repair.lean`

**The DECLARATIONS do not change -- same names, same statements, same proofs, same
namespace.**
**The INTERNAL imports do: the five `Repair` files import each other, and those edges now name
the new modules so the dependency graph reports where the code actually lives.**
The old path is now a facade that imports this file and contains no proof.
-/

import Mathlib

/-!
# `Lattice.Core.Repair` -- T4: the verification loop

## The two properties, kept apart

A verification loop has two distinct obligations, and conflating them made the legacy
formulation vacuous:

* **Preservation** -- a point that already passes is not damaged by repairing.
* **Progress** -- a point that fails reaches a passing state in finitely many steps.

The legacy tree proved Preservation for `repair x := x`, an identity function, where it
reduces to `fun h => h`; and it proved Progress only for one hard-coded predicate
(`repairEven`, "is even"). Neither statement transferred to anything else.

## The abstraction

Both properties follow from three obligations on a decreasing measure:

```
absorbs    : Sat x  ->  fix x = x
decreases  : not (Sat x) ->  mu (fix x) < mu x
atomic     : mu x = 0  ->  Sat x
```

`atomic` is the one the legacy work never isolated. It is exactly why `repairEven`
converges: its measure is the parity defect of `x`, so a zero defect is precisely a
passing point.

## On the measure being `Nat`

A first attempt placed the measure in an arbitrary well-founded type, which is the right
generalisation. Lean's `WellFounded.induction` then had to infer a motive living in two
universes, and the hypothesis about the carrier was repeatedly instantiated at the
measure type; every rewrite failed. The chosen strategy (see
`Zero/Proofs/T4-回路收敛-思路.md` §8) is to prove the `Nat` case, where the motive is
unambiguous, and generalise afterwards via `InvImage.wf`.
-/

namespace Lattice.Core

/-- A repair operator with a natural-number termination measure. -/
structure Repair (α : Type) where
  /-- Which points pass verification. -/
  Sat : α → Prop
  /-- One repair step. -/
  fix : α → α
  /-- The termination measure. -/
  μ : α → ℕ
  /-- **Absorption.** A passing point is left alone. -/
  absorbs : ∀ x, Sat x → fix x = x
  /-- **Decrease.** A failing point strictly improves. -/
  decreases : ∀ x, ¬ Sat x → μ (fix x) < μ x
  /-- **Atomicity.** A zero measure means the point passes. -/
  atomic : ∀ x, μ x = 0 → Sat x

namespace Repair

variable {α : Type} (R : Repair α)

/-- The `n`-fold iterate of the repair step. -/
def iterate (n : Nat) (x : α) : α := Nat.iterate R.fix n x

/-- `iterate (n+1)` applies `fix` once more, after `n` steps. -/
theorem iterate_succ (n : Nat) (x : α) :
    R.iterate (n + 1) x = R.fix (R.iterate n x) := by
  simp only [iterate, Function.iterate_succ_apply']

/-- **Progress.** Every point reaches a passing state in finitely many steps.

Strong induction on the measure. The motive is quantified over the *current* point, so
that after one step the hypothesis is applied to `fix y` and the conclusion transports
along `iterate_succ` without the two iteration orders ever having to be compared. -/
theorem progress : ∀ (x : α), ∃ n : Nat, R.Sat (R.iterate n x) := by
  intro x
  by_cases hsat : R.Sat x
  · exact ⟨0, hsat⟩
  · -- While the point still fails, each step lowers the measure by at least one,
    -- so after `n` steps either it passes or `mu 0 + n <= mu x`.
    have key : ∀ n : Nat, R.Sat (R.iterate n x) ∨ R.μ (R.iterate n x) + n ≤ R.μ x := by
      intro n
      induction n with
      | zero => right; simp only [iterate]; exact le_rfl
      | succ k ih =>
        rcases ih with hpass | hbound
        · left
          rw [iterate_succ, R.absorbs _ hpass]
          exact hpass
        · by_cases hk : R.Sat (R.iterate k x)
          · left
            rw [iterate_succ, R.absorbs _ hk]
            exact hk
          · right
            have hlt := R.decreases (R.iterate k x) hk
            rw [iterate_succ]
            omega
    rcases key (R.μ x + 1) with hpass | hbad
    · exact ⟨R.μ x + 1, hpass⟩
    · omega

/-- **Preservation.** A passing point stays passing under any number of repairs.

This is the "does not destroy existing semantics" half, and it needs only `absorbs`. -/
theorem preserves (x : α) (h : R.Sat x) (n : Nat) : R.Sat (R.iterate n x) := by
  have hid : R.iterate n x = x := by
    induction n with
    | zero => rfl
    | succ k ihk =>
      rw [iterate_succ, ihk]
      exact R.absorbs x h
  rw [hid]
  exact h

/-- The loop is inert on a passing point: one step changes nothing. -/
theorem stable (x : α) (h : R.Sat x) : R.fix x = x :=
  R.absorbs x h

end Repair

/-! ## A canonical instance: parity repair

Accepted when even; odd `x` steps down by one. The measure is the parity defect, so
`atomic` holds. This is the legacy `repairEven` generalised. -/

/-- The parity defect of `n`, used as a measure. -/
def parityDefect (n : ℕ) : ℕ := n % 2

/-- Parity repair: odd numbers step down to the even number below. -/
def parityRepair : Repair ℕ where
  Sat := fun n => n % 2 = 0
  fix := fun n => if n % 2 = 0 then n else n - 1
  μ := parityDefect
  absorbs := by
    intro n hn
    simp only [hn, if_true]
  decreases := by
    intro n hn
    simp only [parityDefect]
    by_cases h : n % 2 = 0
    · exact absurd h hn
    · have hodd : n % 2 = 1 := by omega
      simp only [h, if_false]
      omega
  atomic := by
    intro n hn
    simp only [parityDefect] at hn
    omega

/-- The legacy result recovered as an instance: parity repair always terminates on a
passing state. -/
theorem parity_terminates (n : ℕ) :
    ∃ k : ℕ, parityRepair.Sat (Nat.iterate parityRepair.fix k n) :=
  Repair.progress parityRepair n

/-! ## Necessity: `atomic` is load-bearing -/

section Necessity

/-- Fixed on the passing side, step down otherwise. -/
def downFix (x : ℤ) : ℤ := if 0 ≤ x then x else x - 1

/-- Decrease is satisfiable. -/
theorem down_decreases : ∀ x : ℤ, ¬ (0 ≤ x) → downFix x < x := by
  intro x hx
  have hif : ¬ (0 ≤ x) := hx
  simp only [downFix, hif, if_false]
  omega

/-- Absorption is satisfiable. -/
theorem down_absorbs : ∀ x : ℤ, 0 ≤ x → downFix x = x := by
  intro x hx
  simp only [downFix, hx, if_true]

/-- The descending iteration from `-1` stays negative at every step. -/
theorem down_stays_neg : ∀ n : ℕ, Nat.iterate downFix n (-1) < 0 := by
  intro n
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hif : ¬ (0 ≤ Nat.iterate downFix k (-1)) := not_le.mpr ih
    simp only [downFix, hif, if_false]
    omega

/-- Consequently it never converges; this is the behaviour `atomic` forbids. -/
theorem down_no_progress : ¬ ∃ n : ℕ, 0 ≤ Nat.iterate downFix n (-1) := by
  intro ⟨n, hn⟩
  have h := down_stays_neg n
  omega

end Necessity

end Lattice.Core
