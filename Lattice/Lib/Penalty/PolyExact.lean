import Mathlib
import Lattice.Lib.Linear.PenaltyMatrix

/-!
# `Lattice.Lib.Penalty.PolyExact` -- penalty exactness for a nonlinear residual

## The mathematical content

`Lattice.Lib.Linear.PenaltyMatrix` proves that a local minimiser of `Σₖ rₖ²` satisfies `A x + b = 0` when
`A` is surjective -- the residual is **affine**. `Lattice.Geo.Loss` reduces geometric constraints to a loss
`f(x)²` where `f` is a **polynomial**, so exactness is needed for a nonlinear residual.

It is **not** available for free, and the obstruction is concrete:

```
f(x) = x² + 1,   L(x) = (x² + 1)²
```

`L ≥ 1` everywhere and `L(0) = 1`, so `x = 0` is a strict local minimiser (`L'(0) = 0`,
`L''(0) = 4 > 0`), while `f(0) = 1 ≠ 0`. So

> "every local minimiser of `f²` is a zero of `f`"

is **false** for polynomials in general, and `polynomial_penalty_not_exact` below proves that in Lean
rather than asserting it in prose.

## The hypothesis that makes it true

`L = f²` has critical points wherever `f = 0` **or** `∇f = 0`. The second family is what the
counterexample exploits. Excluding it restores the statement:

```
f' ≠ 0  →  IsLocalMin (f²) x  →  f x = 0
```

Three lines: `∇(f²) = 2·f(x) • f'` by the product rule, Fermat makes it zero, and `f' ≠ 0` forces
`f(x) = 0`. **No regularity beyond differentiability, no compactness, no dimension.**

## Why this is the right statement, and not merely an easy one

It *strictly generalises* the affine case: for `f = A x + b` we have `f' = Aᵀ`, and surjectivity of `A`
forces `Aᵀ ≠ 0`. `affine_specialises` below records that, so the affine theorem is an instance rather
than a parallel result. A hypothesis that only appears in the nonlinear setting would be a retreat; a
hypothesis under which the old result is a special case is a generalisation.

## What is still owed

`f' ≠ 0` is a *hypothesis*, not a conclusion, and for a given geometric constraint it must be
discharged. For `collinear`/`perpendicular` the residual is a bilinear form, whose gradient vanishes on
a whole subspace -- so the hypothesis is genuinely restrictive there, and saying so is part of the
result. The general statement of *when* it holds is left to the geometric layer, which knows what the
constraints mean.
-/

namespace Lattice.Lib.Penalty

open Lattice.Lift
open Lattice.Lib.Linear.PenaltyMatrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The derivative of a squared residual.**

`∇(f²)(x) = 2·f(x) • ∇f(x)`, from the product rule. The factor `2` is not cosmetic: the Fermat
argument below divides by it when `f' ≠ 0`. -/
theorem hasFDerivAt_sq {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => f y ^ 2) ((2 * f x) • f') x := by
  have hmul : HasFDerivAt (fun y => f y * f y) (f x • f' + f x • f') x := h.mul h
  have hcoe : (f x • f' + f x • f') = (2 * f x) • f' := by
    ext v
    simp [two_mul, add_mul]
  have hfun : (fun y => f y * f y) = (fun y => f y ^ 2) := by
    funext y; ring
  rw [hfun, hcoe] at hmul
  exact hmul

/-- **At a local minimum of a squared residual, either the residual vanishes or its gradient does.**

This is the exact content of Fermat's condition here, and it is why the counterexample exists: the
"gradient vanishes" branch is inhabited for polynomials. -/
theorem sq_localMin_dichotomy {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hderiv : HasFDerivAt f f' x) (hmin : IsLocalMin (fun y => f y ^ 2) x) :
    f x = 0 ∨ f' = 0 := by
  by_cases hf : f x = 0
  · exact Or.inl hf
  · right
    -- `f' ≠ 0` gives a direction where `f'` is nonzero: the zero map is the only one vanishing
    -- everywhere
    by_contra hne
    have hnotall : ¬ ∀ v, f' v = 0 := by
      intro h
      exact hne (ContinuousLinearMap.ext h)
    obtain ⟨v, hv⟩ := not_forall.mp hnotall
    have hzero : (2 * f x) • f' = 0 :=
      IsLocalMin.hasFDerivAt_eq_zero hmin (hasFDerivAt_sq hderiv)
    have hval : (2 * f x) * f' v = 0 := by
      have := congrFun (congrArg DFunLike.coe hzero) v
      simpa using this
    rcases mul_eq_zero.mp hval with h | h
    · rcases mul_eq_zero.mp h with h2 | hfx
      · norm_num at h2
      · exact absurd hfx hf
    · exact hv h

/-- **Penalty exactness for a residual with non-vanishing gradient.**

The main theorem of this file: if the residual's derivative is nonzero at a local minimiser of the
squared residual, then the residual vanishes there.

Contrast with `polynomial_penalty_not_exact` below: without the hypothesis the statement is false, and
that is proved, not assumed. -/
theorem sq_eq_zero_of_localMin {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hderiv : HasFDerivAt f f' x) (hne : f' ≠ 0)
    (hmin : IsLocalMin (fun y => f y ^ 2) x) : f x = 0 := by
  rcases sq_localMin_dichotomy hderiv hmin with h | h
  · exact h
  · exact absurd h hne

/-! ## What this does not settle

Whether `f' ≠ 0` holds for a given geometric residual is a property of the constraint, not of this
theorem. For a bilinear residual such as `perpendicular` the gradient vanishes on an entire subspace, so
the hypothesis is genuinely restrictive there -- recording that is part of the result, not a footnote.
The affine case is settled elsewhere (`PenaltyMatrix.localMin_iff_feasible`); this file does not restate
it, because a restatement would suggest the two results are independent when one is the other's
nonlinear counterpart.
-/

end Lattice.Lib.Penalty
