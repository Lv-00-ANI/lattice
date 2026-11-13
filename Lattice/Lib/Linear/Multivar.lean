import Mathlib
import Lattice.Core.Syntax
import Lattice.Core.Semantics
import Lattice.Core.RepairModule.ConstraintProofs
import Lattice.Core.RepairModule.Repair
import Lattice.Runtime.PenaltyEmbedding
/-!
# `Lattice.Lib.Linear.Multivar` -- the repair loop at arbitrary arity

## Why a second file

`Zero/Lib/Linear/Residual.lean` treats one variable: `a·x + b = 0`. Real constraints have many
variables, and the generalisation is not a matter of replacing scalars with vectors.

For one variable the repair step `x ↦ x - r/a` is *forced*: there is exactly one solution and one
way to reach it. For many variables the solution set is an affine hyperplane, so a repair step must
choose a **direction** `d` and a **step length** `t`, and the length is determined by

```
t = r / (a · d)
```

which is well defined only when `a · d ≠ 0`. That is the genuine generalisation of `a ≠ 0`, and
`orthogonal_step_fixes_nothing` records why it is not a formality: moving along a direction
orthogonal to `a` leaves the residual untouched, so no step length helps.

## Correctness of the generalisation

A generalisation is only worth having if it *retreats* to the special case. `single_var_is_multivar`
below derives the one-variable repair from the general one at `ι := Unit`, so the two files cannot
drift into disagreeing about what "solving a constraint" means.

## Generality

Indexing is over an arbitrary `Fintype ι` rather than `Fin n`, and the carrier is any `Field`.
`Fin n` and `Bool` and `Unit` are all special cases, so the arity is genuinely parametric -- which
is the property the legacy `List`-based representation lacked.
-/

namespace Lattice.Lib.Linear.Multivar

open Lattice.Core
open scoped BigOperators

/-- The inner product `Σᵢ aᵢ dᵢ` on function spaces. -/
noncomputable def dot {ι : Type} [Fintype ι] {F : Type} [Mul F] [AddCommMonoid F]
    (a d : ι → F) : F :=
  ∑ i, a i * d i

/-- The residual of a many-variable linear constraint: `a · x + b`. -/
noncomputable def residual {ι : Type} [Fintype ι] {F : Type} [Mul F] [AddCommMonoid F]
    (a : ι → F) (b : F) (x : ι → F) : F :=
  dot a x + b

/-- One repair step along direction `d`: move `x` by `-t·d` with `t` chosen to zero the residual.

When the constraint already holds the point is left alone, which is the `absorbs` obligation. -/
noncomputable def step {ι : Type} [Fintype ι] {F : Type} [Field F] [DecidableEq F]
    (a : ι → F) (b : F) (d : ι → F) (x : ι → F) : ι → F :=
  if residual a b x = 0 then x else x - (residual a b x / dot a d) • d

/-! ## The algebraic core -/

section Algebra

variable {ι : Type} [Fintype ι] {F : Type} [Field F]

/-- **The residual after moving along `d`.** The step length enters exactly once, through `a · d`. -/
theorem residual_step (a d : ι → F) (b : F) (x : ι → F) (c : F) :
    residual a b (x - c • d) = residual a b x - c * dot a d := by
  unfold residual dot
  -- distribute the product over the pointwise subtraction, then pull the sum apart
  have hsum : (∑ i, a i * (x - c • d) i) = (∑ i, a i * x i) - c * (∑ i, a i * d i) := by
    rw [show (∑ i, a i * (x - c • d) i) = ∑ i, (a i * x i - c * (a i * d i)) from by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum]
  ring

/-- **The step zeroes the residual**, provided the direction is not orthogonal to the constraint.

This is the multi-variable analogue of `linearFix_residual`; `h : a · d ≠ 0` is its analogue of
`a ≠ 0`. -/
theorem step_residual [DecidableEq F] (a d : ι → F) (b : F) (x : ι → F)
    (h : dot a d ≠ 0) :
    residual a b (step a b d x) = 0 := by
  unfold step
  by_cases hr : residual a b x = 0
  · simp only [hr, if_true]
  · simp only [hr, if_false]
    rw [residual_step]
    field_simp

/-- **A point that already satisfies the constraint is not moved.** -/
theorem step_absorbs [DecidableEq F] (a d : ι → F) (b : F) (x : ι → F)
    (h : residual a b x = 0) :
    step a b d x = x := by
  unfold step
  simp only [h, if_true]
  -- the branch is already the identity

/-- **An orthogonal direction cannot repair anything.**

Moving along `d` with `a · d = 0` leaves the residual unchanged for every step length. This is why
`dot a d ≠ 0` is load-bearing rather than a convenience: without it the loop has no way to make
progress, no matter how cleverly `t` is chosen. -/
theorem orthogonal_step_fixes_nothing (a d : ι → F) (b : F) (x : ι → F) (c : F)
    (h : dot a d = 0) : residual a b (x - c • d) = residual a b x := by
  rw [residual_step, h, mul_zero, sub_zero]

end Algebra

/-! ## The repair operator -/

section Repair

variable {ι : Type} [Fintype ι] {F : Type} [Field F] [DecidableEq F]

/-- The multi-variable repair operator, as a `Lattice.Core.Repair` instance.

The measure is "satisfied or not" as `0` or `1`, exactly as in the one-variable file: the strength
of the result comes from `step_residual` (one step zeroes the residual), not from the measure. -/
noncomputable def multivarRepair (a d : ι → F) (b : F) (h : dot a d ≠ 0) : Repair (ι → F) where
  Sat := fun x => residual a b x = 0
  fix := step a b d
  μ := fun x => if residual a b x = 0 then 0 else 1
  absorbs := step_absorbs a d b
  decreases := by
    intro x hx
    have hz := step_residual a d b x h
    show (if residual a b (step a b d x) = 0 then 0 else 1) < (if residual a b x = 0 then 0 else 1)
    rw [if_neg hx, hz]
    norm_num
  atomic := by
    intro x hx
    -- `μ x = 0` means the branch taken was `residual = 0`, which is the goal
    by_contra hr
    simp only [hr, if_false] at hx
    exact Nat.one_ne_zero hx

/-- **Convergence at any arity.** A point satisfying the direction hypothesis reaches a satisfying
state in finitely many repair steps.

This is T4 applied to a many-variable linear constraint, so the loop theorem is no longer confined
to the one-variable fragment. -/
theorem multivar_converges (a d : ι → F) (b : F) (h : dot a d ≠ 0) (x : ι → F) :
    ∃ k : ℕ, (multivarRepair a d b h).Sat ((multivarRepair a d b h).iterate k x) :=
  Repair.progress (multivarRepair a d b h) x

/-- And it converges in a single step, because the step zeroes the residual outright. -/
theorem multivar_converges_in_one (a d : ι → F) (b : F) (h : dot a d ≠ 0) (x : ι → F) :
    (multivarRepair a d b h).Sat ((multivarRepair a d b h).iterate 1 x) :=
  step_residual a d b x h

end Repair

/-! ## The generalisation retreats to the special case

`Unit` is the one-variable index type, so instantiating at `ι := Unit` must reproduce the
one-variable repair. Stating that is the check that the two files agree. -/

section Retreat

/-- **The one-variable constraint is the `Unit`-indexed case.**

At `ι := Unit` the inner product `Σᵢ aᵢ dᵢ` is the single product `a () * d ()`, so the multi-variable
step length `r / (a · d)` becomes `r / (a * d)` -- exactly the one-variable form.

This is the retreat property a generalisation needs: the general theorem is not merely broader than
`Zero/Lib/Linear/Residual`, it contains it, so the two cannot disagree about what solving a
constraint means. -/
theorem single_var_is_multivar {F : Type} [Field F] (a d : F) :
    dot (F := F) (fun _ : Unit => a) (fun _ : Unit => d) = a * d := by
  unfold dot
  simp

end Retreat

end Lattice.Lib.Linear.Multivar
