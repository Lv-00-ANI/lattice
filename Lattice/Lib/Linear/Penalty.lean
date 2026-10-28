import Mathlib
import Lattice.Core.Syntax
import Lattice.Runtime.PenaltyEmbedding
/-!
# `Lattice.Lib.Linear.Penalty` -- the squared-residual penalty is exact

## What is proved, and why it needed a specific penalty

`PenaltyExact` (`Lattice.Lift.PenaltyEmbedding`) says every local minimiser of the loss satisfies the
constraint. It is **false** for an arbitrary embedding -- `sound_not_exact` in that file exhibits a
constant positive loss, which is minimised everywhere and accepts nothing.

So the obligation `lift.embed.local_minimiser_exact` cannot be discharged for all embeddings. What
can be discharged is the case that matters: the squared residual `(a·x + b)²`. This file proves that
its minima are exactly the feasible points, when the slope is nonzero.

## The argument

Fermat's condition (`IsLocalMin.deriv_eq_zero`): at a local minimum of a differentiable real
function, the derivative vanishes. For `x ↦ (a·x + b)²` the derivative is `2·(a·x + b)·a`
(`HasDerivAt.pow` composed with the affine map), so

```
2·(a·x + b)·a = 0   and   a ≠ 0   ⟹   a·x + b = 0
```

The converse (`sq_penalty_localMin_iff` direction `←`) is the non-negativity argument already used
by `loss_zero_is_localMin`: a square is never negative, so a point where it vanishes is a minimum.

## Why the slope hypothesis is unavoidable

At `a = 0` the function is constant `b²`, so *every* point is a local minimum. If `b ≠ 0` the
constraint is unsatisfiable, so `PenaltyExact` fails; `zero_slope_not_exact` records that this is a
real failure rather than a technicality.

## Scope

One variable, over `ℝ`. The many-variable form needs `Aᵀ(Ax + b) = 0` together with a full-column-rank
condition to conclude `Ax + b = 0`, which is a genuinely different argument and is recorded as a slot.
-/

namespace Lattice.Lib.Linear.Penalty

open Lattice.Lift

/-- The squared-residual loss for a one-variable constraint over the reals.

Note that this is *the same function* the world sees in `Lattice.Lib.Linear.Residual.sqPenalty`, but
stated over `ℝ` rather than `ℚ`: differentiation needs `ℝ`, and the point of this file is Fermat's
condition, not the rational fragment. -/
noncomputable def sqLoss (a b : ℝ) : ℝ → ℝ := fun x => (a * x + b) ^ 2

/-- The derivative of `sqLoss` is `2·(a·x + b)·a`.

Established through `HasDerivAt.pow` so that no `simp` lemma about `deriv` has to be trusted. -/
theorem hasDerivAt_sqLoss (a b x : ℝ) :
    HasDerivAt (sqLoss a b) (2 * (a * x + b) * a) x := by
  have hinner : HasDerivAt (fun y : ℝ => a * y + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have h := hinner.pow 2
  -- `h : HasDerivAt (fun y => (a*y+b)^2) (2 * (a*x+b)^(2-1) * a) x`
  simpa [sqLoss, mul_assoc, mul_comm, mul_left_comm] using h

/-- **Fermat at a local minimum.** The derivative of `sqLoss` vanishes there. -/
theorem sqLoss_deriv_zero_of_localMin (a b x : ℝ) (h : IsLocalMin (sqLoss a b) x) :
    2 * (a * x + b) * a = 0 :=
  IsLocalMin.hasDerivAt_eq_zero h (hasDerivAt_sqLoss a b x)

/-- **At a local minimum, a nonzero slope forces the point to be feasible.**

This is the forward direction of `sq_penalty_localMin_iff` and the whole content of the slot: a
non-feasible point cannot be a minimum because there the loss has a nonzero derivative, so it must
be decreasing along one side. -/
theorem feasible_of_localMin (a b x : ℝ) (ha : a ≠ 0) (h : IsLocalMin (sqLoss a b) x) :
    a * x + b = 0 := by
  have hd := sqLoss_deriv_zero_of_localMin a b x h
  -- `mul_eq_zero` gives `2 * (a*x+b) = 0 ∨ a = 0`; the second is excluded by `ha`
  have h2 : 2 * (a * x + b) = 0 := by
    rcases mul_eq_zero.mp hd with h' | h'
    · exact h'
    · exact absurd h' ha
  linarith

/-- **The converse.** A feasible point is a local minimum, because the loss is a square: it is
non-negative everywhere and vanishes there. -/
theorem localMin_of_feasible (a b x : ℝ) (h : a * x + b = 0) : IsLocalMin (sqLoss a b) x := by
  apply isLocalMin_of_forall_le
  intro y
  show ((a * x + b : ℝ)) ^ 2 ≤ (a * y + b) ^ 2
  rw [h]
  norm_num
  exact sq_nonneg (a * y + b)

/-- **Local minima are exactly the feasible points**, for a nonzero slope. -/
theorem sq_penalty_localMin_iff (a b x : ℝ) (ha : a ≠ 0) :
    IsLocalMin (sqLoss a b) x ↔ a * x + b = 0 :=
  ⟨feasible_of_localMin a b x ha, localMin_of_feasible a b x⟩

/-! ## The slot, discharged for this penalty

`lift.embed.local_minimiser_exact` asks for a penalty whose minima are its solutions. For the squared
residual that is now a theorem, not an assumption. -/

/-- **`PenaltyExact` holds for the squared residual with nonzero slope.**

This instantiates the general obligation at a concrete penalty and proves it, which is what the slot
asked for. It does not claim that *all* penalties are exact -- `sound_not_exact` in
`Lattice.Lift.PenaltyEmbedding` shows the opposite. -/
theorem sq_penalty_exact (a b : ℝ) (ha : a ≠ 0) :
    ∀ x : ℝ, IsLocalMin (sqLoss a b) x → a * x + b = 0 :=
  fun x h => feasible_of_localMin a b x ha h

/-! ## Necessity: the slope hypothesis is load-bearing -/

/-- At zero slope the loss is constant `b²`, so every point is a local minimum. -/
theorem zero_slope_all_localMin (b x : ℝ) : IsLocalMin (sqLoss 0 b) x := by
  apply isLocalMin_of_forall_le
  intro y
  show ((0 : ℝ) * x + b) ^ 2 ≤ (0 * y + b) ^ 2
  simp only [zero_mul, zero_add]
  exact le_refl _

/-- **With zero slope and nonzero constant, no point is feasible.** -/
theorem zero_slope_no_feasible (b : ℝ) (hb : b ≠ 0) : ∀ x : ℝ, ¬ (0 * x + b = 0) := by
  intro x h
  simp only [zero_mul, zero_add] at h
  exact hb h

/-- **The slope hypothesis is not removable.** At `a = 0`, `b ≠ 0` every point is a local minimum
while no point is feasible, so `PenaltyExact` genuinely fails. This is the machine-checked reason
`sq_penalty_exact` carries `ha : a ≠ 0`. -/
theorem zero_slope_not_exact (b : ℝ) (hb : b ≠ 0) :
    ¬ ∀ x : ℝ, IsLocalMin (sqLoss 0 b) x → 0 * x + b = 0 := by
  intro h
  have hmin := zero_slope_all_localMin b 0
  have hf := h 0 hmin
  simp only [zero_mul, zero_add] at hf
  exact hb hf

end Lattice.Lib.Linear.Penalty
