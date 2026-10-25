import Mathlib
import Lattice.Lib.Linear.PenaltyMatrix
import Lattice.Lift.PenaltyAnalysis

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

/-! ## The Fermat lemmas now live in `lift`

These three propositions were originally defined here. They contain no `lib`-level content --
only Mathlib analysis and the Fermat first-order condition -- so they belong in the `lift`
layer, and keeping them here forced `lift` modules to import `lib` (a layering violation that
the gate reports as I4). They are now defined exactly once, in
`Lattice.Lift.PenaltyAnalysis`, and the names below are the `lib`-side spellings of the same
terms.

`home` keeps the proof to one line and, more importantly, makes `#print axioms` and
`#check` resolve to the single `lift` definition rather than to a second copy.
-/
section Reexport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_sq {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => f y ^ 2) ((2 * f x) • f') x :=
  Lattice.Lift.hasFDerivAt_sq h

theorem sq_localMin_dichotomy {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hderiv : HasFDerivAt f f' x) (hmin : IsLocalMin (fun y => f y ^ 2) x) :
    f x = 0 ∨ f' = 0 :=
  Lattice.Lift.sq_localMin_dichotomy hderiv hmin

theorem sq_eq_zero_of_localMin {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hderiv : HasFDerivAt f f' x) (hne : f' ≠ 0)
    (hmin : IsLocalMin (fun y => f y ^ 2) x) : f x = 0 :=
  Lattice.Lift.sq_eq_zero_of_localMin hderiv hne hmin

end Reexport


/-! ## What this does not settle

Whether `f' ≠ 0` holds for a given geometric residual is a property of the constraint, not of this
theorem. For a bilinear residual such as `perpendicular` the gradient vanishes on an entire subspace, so
the hypothesis is genuinely restrictive there -- recording that is part of the result, not a footnote.
The affine case is settled elsewhere (`PenaltyMatrix.localMin_iff_feasible`); this file does not restate
it, because a restatement would suggest the two results are independent when one is the other's
nonlinear counterpart.
-/

end Lattice.Lib.Penalty
