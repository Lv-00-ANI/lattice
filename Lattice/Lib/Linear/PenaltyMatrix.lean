import Mathlib
import Lattice.Core.Syntax
import Lattice.Runtime.PenaltyEmbedding
import Lattice.Lib.Linear.PenaltyVector

/-!
# `Lattice.Lib.Linear.PenaltyMatrix` -- the penalty for a matrix constraint

## What changes from the diagonal case

For a diagonal constraint `rᵢ = aᵢxᵢ + bᵢ`, moving one coordinate changes exactly one residual, and the
perturbation argument at `Fin n` could cancel the untouched sum. For a matrix constraint

```
rₖ = Σᵢ A k i · x i + b k
```

every residual depends on every coordinate, so a coordinate step changes **all** of them and nothing
cancels. The argument has to be redone rather than generalised.

## The perturbation, for a matrix

Moving along a direction `d` by `t`:

```
rₖ(x - t·d) = rₖ(x) - t · (A d)ₖ
```

so, writing `s := A d`,

```
L(x - t·d) = Σₖ (rₖ - t sₖ)²
           = L(x) - 2t · (Σₖ rₖ sₖ) + t² · (Σₖ sₖ²)
```

**Choosing `s = r`** -- possible exactly when `A` is surjective, which is the coordinate-free form of
full row rank -- and `t = 1` gives

```
L(x - d) = L(x) - 2‖r‖² + ‖r‖² = L(x) - ‖r‖² < L(x)
```

One step, and the loss drops by exactly `‖r‖²`. That is sharper than the diagonal case, where the
decrease was only known up to a scale factor.

## The hypothesis

`A` is assumed **surjective**: `∀ r, ∃ d, A d = r`. For finite-dimensional real spaces this is
equivalent to full row rank, and it is the form the argument actually uses -- nothing about spans,
kernels or `LinearMap.rank` is needed, which keeps the file about the perturbation rather than about
linear algebra. The equivalence is recorded as a remark, not as a proved theorem, because proving it
would need `LinearMap.range` machinery that no consumer of this file needs.

## The scale, for the topological step

`x - s·d` for `s → 0` approaches `x`, and there the residual is `r - s·r = (1 - s)·r`, so the loss is
`Σₖ ((1-s) rₖ)² = (1-s)² ‖r‖²`, strictly below `L(x)` for every `s ∈ (0, 2)` other than `0`. This is the
same shape as the diagonal case, so the topological packaging is identical -- `dist_pi_lt_iff` and a
scale bounded by `min 1 (ε / (2(|d| + 1)))`.
-/

namespace Lattice.Lib.Linear.PenaltyMatrix

open Lattice.Lib.Linear.PenaltyVector
open Lattice.Lift

/-- A weight matrix `A : Fin m → Fin n → ℝ` viewed as a map on vectors. -/
noncomputable def AMul {m n : ℕ} (A : Fin m → Fin n → ℝ) (d : Fin n → ℝ) : Fin m → ℝ :=
  fun k => ∑ i, A k i * d i

/-- The residual of a matrix constraint. -/
noncomputable def residM {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Fin m → ℝ :=
  fun k => (∑ i, A k i * x i) + b k

/-- The loss: the sum of squared residuals. -/
noncomputable def lossM {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ k, (residM A b x k) ^ 2

/-- **The residual moves linearly along a direction.** -/
theorem residM_step {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x d : Fin n → ℝ) (t : ℝ)
    (k : Fin m) :
    residM A b (x - t • d) k = residM A b x k - t * AMul A d k := by
  unfold residM AMul
  have hexp : (∑ i, A k i * (x - t • d) i) = (∑ i, A k i * x i) - t * ∑ i, A k i * d i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexp]
  ring

/-- **The loss along a direction, expanded.** -/
theorem lossM_step {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x d : Fin n → ℝ) (t : ℝ) :
    lossM A b (x - t • d)
      = lossM A b x - 2 * t * (∑ k, residM A b x k * AMul A d k)
        + t ^ 2 * (∑ k, (AMul A d k) ^ 2) := by
  unfold lossM
  have hterm : ∀ k : Fin m,
      (residM A b (x - t • d) k) ^ 2
        = (residM A b x k) ^ 2 - 2 * t * (residM A b x k * AMul A d k)
          + t ^ 2 * (AMul A d k) ^ 2 := by
    intro k
    rw [residM_step]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-! ## Surjectivity, and the one-step decrease -/

/-- **`A` is surjective** when every target residual can be produced as a direction.

This is the coordinate-free form of full row rank: for finite-dimensional real spaces the two are
equivalent, and this is the form the perturbation argument consumes -- no `LinearMap.rank`, no span,
no kernel. -/
def Surjective {m n : ℕ} (A : Fin m → Fin n → ℝ) : Prop :=
  ∀ r : Fin m → ℝ, ∃ d : Fin n → ℝ, AMul A d = r

/-- **A nonzero residual can be removed in one step**, when the matrix is surjective.

Take `d` with `A d = r` and move `x - d`: the residual becomes `r - A d = 0`, so the loss drops from
`‖r‖²` to `0`. Sharper than the diagonal case, where the decrease was only known up to a scale factor,
and this is what makes the topological step easy: the family `x - s·d` scales the witness and keeps the
loss at `(1 - s)² ‖r‖²`.

The witness is written `x - (1:ℝ) • d` so that it matches `lossM_step` directly; converting to `x - d`
would need `one_smul` in the wrong direction.
-/
theorem exists_decrease {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hA : Surjective A) (hr : residM A b x ≠ 0) :
    ∃ y : Fin n → ℝ, lossM A b y < lossM A b x := by
  obtain ⟨d, hd⟩ := hA (residM A b x)
  refine ⟨x - (1 : ℝ) • d, ?_⟩
  rw [lossM_step A b x d 1]
  simp only [one_pow, mul_one]
  -- the first two terms cancel against the third
  have hsq : (∑ k, residM A b x k * AMul A d k) = ∑ k, (residM A b x k) ^ 2 := by
    rw [hd]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsq2 : (∑ k, (AMul A d k) ^ 2) = ∑ k, (residM A b x k) ^ 2 := by
    rw [hd]
  rw [hsq, hsq2]
  -- `L x - 2‖r‖² + ‖r‖² = L x - ‖r‖² < L x`
  have hpos : (0:ℝ) < ∑ k, (residM A b x k) ^ 2 := by
    obtain ⟨k0, hk0⟩ := Function.ne_iff.mp hr
    unfold lossM at *
    exact Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨k0, Finset.mem_univ _, sq_pos_of_ne_zero hk0⟩
  unfold lossM
  linarith

/-! ## The scaled family, and the topological step -/

/-- **The loss along the scaled witness.** At scale `s` every residual is multiplied by `1 - s`, so the
loss is `(1 - s)² ‖r‖²` -- strictly below `L x` for every `s ∈ (0, 2)` other than `0`. -/
theorem lossM_scaled {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x d : Fin n → ℝ)
    (hd : AMul A d = residM A b x) (s : ℝ) :
    lossM A b (x - s • d) = (1 - s) ^ 2 * ∑ k, (residM A b x k) ^ 2 := by
  rw [lossM_step A b x d s]
  have hsq : (∑ k, residM A b x k * AMul A d k) = ∑ k, (residM A b x k) ^ 2 := by
    rw [hd]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsq2 : (∑ k, (AMul A d k) ^ 2) = ∑ k, (residM A b x k) ^ 2 := by
    rw [hd]
  rw [hsq, hsq2]
  unfold lossM
  ring

/-- **No local minimum has a nonzero residual**, for a surjective matrix.

The packaging is identical to the diagonal case: `Metric.eventually_nhds_iff` bounds the ball, the
scale `min 1 (ε / (2(|d| + 1)))` keeps the point inside it, and `lossM_scaled` keeps the loss strictly
below `L x` for every such scale. -/
theorem not_localMin_of_resid_ne_zero {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hA : Surjective A) (hr : residM A b x ≠ 0) :
    ¬ IsLocalMin (lossM A b) x := by
  intro hmin
  obtain ⟨d, hd⟩ := hA (residM A b x)
  rw [IsLocalMin, IsMinFilter, Metric.eventually_nhds_iff] at hmin
  obtain ⟨ε, hεpos, hε⟩ := hmin
  -- the loss at a scaled point is `(1-s)^2 ‖r‖^2`, which is strictly below `L x` for `s ∈ (0,2)`
  have hL : lossM A b x = ∑ k, (residM A b x k) ^ 2 := rfl
  have hpos : (0:ℝ) < ∑ k, (residM A b x k) ^ 2 := by
    obtain ⟨k0, hk0⟩ := Function.ne_iff.mp hr
    exact Finset.sum_pos' (fun k _ => sq_nonneg _) ⟨k0, Finset.mem_univ _, sq_pos_of_ne_zero hk0⟩
  -- it suffices to find a nonzero `s` with `dist (x - s•d) x < ε`; the loss inequality then holds
  -- for every such `s` because it does not depend on the size of `s`
  have hfind : ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ dist (x - s • d) x < ε := by
    classical
    -- a common bound on the coordinates of `d`, so one scale works for all of them
    set D : ℝ := ∑ i, |d i| with hD
    have hD0 : (0:ℝ) ≤ D := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hDle : ∀ i : Fin n, |d i| ≤ D := by
      intro i
      exact Finset.single_le_sum (f := fun i => |d i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    refine ⟨min 1 (ε / (2 * (D + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    rw [dist_pi_lt_iff hεpos]
    intro i
    have hsub : (x - min 1 (ε / (2 * (D + 1))) • d) i - x i
        = -(min 1 (ε / (2 * (D + 1))) * d i) := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [Real.dist_eq, hsub, abs_neg, abs_mul,
      abs_of_pos (lt_min one_pos (by positivity : (0:ℝ) < ε / (2 * (D + 1))))]
    have hmono1 : min 1 (ε / (2 * (D + 1))) ≤ ε / (2 * (D + 1)) := min_le_right _ _
    have hmono2 : min 1 (ε / (2 * (D + 1))) * |d i| ≤ ε / (2 * (D + 1)) * |d i| :=
      mul_le_mul_of_nonneg_right hmono1 (abs_nonneg _)
    have hstep : ε / (2 * (D + 1)) * |d i| ≤ ε / (2 * (D + 1)) * D :=
      mul_le_mul_of_nonneg_left (hDle i) (by positivity)
    have hstrict : ε / (2 * (D + 1)) * D < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (D + 1))]
      nlinarith [hεpos, hD0]
    linarith
  obtain ⟨s, hs0, hs1, hsdist⟩ := hfind
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hle := hε hsdist
  have hs2 : s < 2 := by linarith
  rw [lossM_scaled A b x d hd s, hL] at hle
  have hsq : (1 - s) ^ 2 < 1 := by nlinarith [sq_nonneg (1 - s)]
  have hlt : (1 - s) ^ 2 * (∑ k, (residM A b x k) ^ 2) < ∑ k, (residM A b x k) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hsq hpos]
  linarith

/-! ## The equivalence, and `PenaltyExact` for a matrix constraint -/

/-- **A feasible point is a local minimum**: the loss is a sum of squares. -/
theorem localMin_of_feasible {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (h : ∀ k, residM A b x k = 0) : IsLocalMin (lossM A b) x := by
  apply isLocalMin_of_forall_le
  intro y
  show lossM A b x ≤ lossM A b y
  have hx0 : lossM A b x = 0 := by
    unfold lossM
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)]
    intro k _
    rw [h k]; ring
  rw [hx0]
  unfold lossM
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- **Local minima are exactly the feasible points**, for a surjective matrix.

The forward direction is `not_localMin_of_resid_ne_zero` contraposed; the reverse is non-negativity. -/
theorem localMin_iff_feasible {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hA : Surjective A) :
    IsLocalMin (lossM A b) x ↔ ∀ k, residM A b x k = 0 := by
  constructor
  · intro hmin k
    by_contra hne
    -- the residual vector is not the zero vector, since coordinate k is nonzero
    have hne0 : residM A b x ≠ 0 := by
      intro hzero
      exact hne (congrFun hzero k)
    exact not_localMin_of_resid_ne_zero A b x hA hne0 hmin
  · exact localMin_of_feasible A b x

/-- **`PenaltyExact` holds for a matrix constraint with a surjective weight matrix.**

This closes the last case of `lift.embed.local_minimiser_exact` that the perturbation argument reaches:
every local minimiser of `Σₖ rₖ²` satisfies `A x + b = 0`, provided `A` can produce any residual as a
direction. No derivative and no norm appear in the proof.

What is *not* claimed: that every matrix used in practice is surjective. A matrix with more rows than
columns cannot be, and then the constraint may be unsatisfiable -- which is the honest boundary, and it
is the same reason `zero_slope_not_exact` carries a slope hypothesis in the one-variable case. -/
theorem sq_penalty_exact_matrix {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hA : Surjective A) :
    ∀ x : Fin n → ℝ, IsLocalMin (lossM A b) x → ∀ k, residM A b x k = 0 :=
  fun x h => (localMin_iff_feasible A b x hA).mp h

end Lattice.Lib.Linear.PenaltyMatrix
