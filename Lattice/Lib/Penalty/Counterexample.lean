import Mathlib
import Lattice.Lib.Penalty.PolyExact
import Lattice.Lift.PenaltyEmbedding

/-!
# `Lattice.Lib.Penalty.Counterexample` -- the polynomial penalty is not exact

## What this file is for

`Lattice.Lib.Penalty.PolyExact.sq_eq_zero_of_localMin` needs `f' ≠ 0`. That hypothesis is not a
convenience: without it the statement is **false**, and this file proves the falsehood rather than
mentioning it.

The witness is `f x = x² + 1`, whose square is minimised at `0` while `f 0 = 1`:

* `L x = (x² + 1)²` satisfies `L x ≥ 1 = L 0`, so `0` is a **global** minimum;
* `f 0 = 1 ≠ 0`, so the penalty's minimiser is not a solution.

Since a global minimiser is a local minimiser, one witness refutes the unconditional statement at
every notion of "local" used in this project.

## Why the counterexample matters beyond bookkeeping

The affine case (`PenaltyMatrix`) has no such witness: a surjective `A` makes the residual's gradient
nonzero everywhere, so the "critical point of `f`" branch of `sq_localMin_dichotomy` is empty. For a
genuinely polynomial residual -- `x² + 1` is the smallest -- that branch is inhabited, and the
generalisation must carry the hypothesis or be wrong.

Recording the witness in Lean, rather than in a comment, is what makes the hypothesis defensible: a
reader can see that dropping it produces a provably false theorem.
-/

namespace Lattice.Lib.Penalty

open Lattice.Lift

/-- The residual `x ↦ x² + 1`: the smallest polynomial whose square has a minimiser away from its zero
set. -/
noncomputable def quadraticPlusOne : ℝ → ℝ := fun x => x ^ 2 + 1

/-- `quadraticPlusOne` never vanishes, so its zero set is empty. -/
theorem quadraticPlusOne_ne_zero (x : ℝ) : quadraticPlusOne x ≠ 0 := by
  unfold quadraticPlusOne
  positivity

/-- **`0` is a global minimum of `(x² + 1)²`.**

`L x = (x² + 1)² ≥ 1 = L 0`, where the inequality is `x² ≥ 0` and `x² + 1 ≥ 1 ⇒ square ≥ 1`. -/
theorem sq_quadraticPlusOne_ge (x : ℝ) :
    (quadraticPlusOne 0) ^ 2 ≤ (quadraticPlusOne x) ^ 2 := by
  unfold quadraticPlusOne
  have h1 : (1 : ℝ) ≤ x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  have h2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have h3 : (0 : ℝ) ≤ 1 := by norm_num
  nlinarith

/-- `0` is therefore a local minimum, hence in particular a local minimum in the sense used by
`IsLocalMin`. -/
theorem quadraticPlusOne_localMin : IsLocalMin (fun x => (quadraticPlusOne x) ^ 2) 0 :=
  isLocalMin_of_forall_le fun x => sq_quadraticPlusOne_ge x

/-- **The polynomial penalty is not exact.**

There is a residual `f` and a point `x` that locally minimises `f²` while `f x ≠ 0`. This is the
machine-checked reason `sq_eq_zero_of_localMin` carries `f' ≠ 0`, and it is why the geometric layer
must discharge that hypothesis per constraint rather than assume it.
-/
theorem polynomial_penalty_not_exact :
    ¬ ∀ (f : ℝ → ℝ) (x : ℝ), IsLocalMin (fun y => f y ^ 2) x → f x = 0 := by
  intro h
  have hx := h quadraticPlusOne 0 quadraticPlusOne_localMin
  exact quadraticPlusOne_ne_zero 0 hx

/-! ## The hypothesis is what the counterexample violates

For completeness: at the minimiser above, the derivative of `quadraticPlusOne` **does** vanish, which
is exactly the branch `sq_localMin_dichotomy` permits. So the counterexample is not an accident of the
theorem being stated wrongly; it is the second branch being non-empty. -/

/-- The derivative of `x ↦ x² + 1` at `0` is zero. -/
theorem hasDerivAt_quadraticPlusOne_zero : HasDerivAt quadraticPlusOne 0 0 := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2 + 1) (2 * 0 ^ (2 - 1) + 0) 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).add_const 1)
  simpa [quadraticPlusOne] using h

/-- **The counterexample lands in the `f' = 0` branch**, as `sq_localMin_dichotomy` predicts. -/
theorem quadraticPlusOne_dichotomy :
    quadraticPlusOne 0 = 0 ∨ HasDerivAt quadraticPlusOne 0 0 := by
  exact Or.inr hasDerivAt_quadraticPlusOne_zero

end Lattice.Lib.Penalty
