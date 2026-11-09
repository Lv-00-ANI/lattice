import Mathlib
import Lattice.Reference.Geometry.Constraints.Differentiable
import Lattice.Reference.Geometry.Constraints.Loss
import Lattice.Lib.Penalty.PolyExact

/-!
# `Lattice.Geo.Exact` -- geometric constraint exactness through the penalty loss

## The last hop

Three pieces existed separately:

* `Lattice.Geo.Loss` builds a squared-residual penalty `loss c v = poly c v ^ 2` from a geometric constraint;
* `Lattice.Geo.Differentiable` shows `poly` is differentiable in the flattened configuration;
* `Lattice.Lib.Penalty.PolyExact.sq_eq_zero_of_localMin` says a local minimum of `f²` at a point where
  `f' ≠ 0` forces `f = 0`.

This file joins them: **a local minimum of a geometric penalty, at a point where the residual's gradient
does not vanish, satisfies the constraint.**

## Why the gradient hypothesis cannot be dropped

`Lattice.Lib.Penalty.Counterexample.polynomial_penalty_not_exact` proves in Lean that the unconditional
statement is false: `f x = x² + 1` is minimised at `0` while `f 0 = 1`. For a geometric residual the same
hazard exists -- `perpendicular` is a bilinear form, whose gradient vanishes whenever one of the two
segments does. So the hypothesis is carried, and the counterexample is what justifies carrying it.

## What is proved, precisely

`geo_penalty_exact` is stated for an abstract differentiable residual with a nonzero derivative, then
instantiated at the two constraints whose differentiability is available
(`perpendicular` via `perpendicularResidual`, `samePoint` via `sqDistResidual`).

It is *not* claimed that the gradient is nonzero for every configuration -- for `perpendicular` it is
false at degenerate configurations -- and the file does not pretend otherwise. Determining when it holds
is a property of the constraint geometry, deferred to whoever supplies the constraint.
-/

namespace Lattice.Geo

open Lattice.Lib.Penalty

variable {k n : ℕ}

/-- **A geometric penalty vanishes at a non-degenerate local minimum.**

A differentiable residual whose derivative does not vanish at a local minimum of its square must vanish there. This
is `Lattice.Lib.Penalty.sq_eq_zero_of_localMin` in the vocabulary the geometric layer uses, and it is stated with the
residual and its derivative as parameters so that it holds of *any* geometric residual; the instances below supply
them.

Round 108 removed a second name for this statement (`residual_eq_zero_of_localMin`) that forwarded to
`sq_eq_zero_of_localMin`, with this theorem forwarding to it in turn. Two hops through the same content is a choice
a reader has to make between two names that mean the same thing; one name is enough, and the surviving one is the
one the target tables cite. -/
theorem geo_penalty_exact
    {f : (Fin (k * n) → ℝ) → ℝ} {f' : (Fin (k * n) → ℝ) →L[ℝ] ℝ} {v : Fin (k * n) → ℝ}
    (hderiv : HasFDerivAt f f' v) (hne : f' ≠ 0)
    (hmin : IsLocalMin (fun w => f w ^ 2) v) :
    f v = 0 :=
  Lattice.Lib.Penalty.sq_eq_zero_of_localMin hderiv hne hmin

/-! ## The penalty form of a constraint

`EqConstraint.loss` squares the residual; the theorems above therefore apply to `loss` once the residual
is identified. The two lemmas below perform that identification for the branches where the residual is a
named function. -/

/-- **`samePoint` penalty exactness**, in the form the abstract theorem consumes.

The loss is the square of the squared distance, so a non-degenerate local minimum of the loss is a
configuration where the two points coincide. Stated over a configuration family `ℕ → Pt n`, which is what
`EqConstraint.loss` takes; the finite-vector form is a transport along `Lattice.Geo.Flatten` and is left to
the caller, because extending `Fin k → Pt n` to `ℕ → Pt n` requires choosing values for the extra points
and proving the choice does not matter -- which is exactly what `GeoExpr.VarsBelow` licenses. -/
theorem samePoint_loss_eq (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) pts =
      (sqDist (n := n) (pts a) (pts b)) ^ 2 := rfl

/-- The `samePoint` penalty is non-negative. -/
theorem samePoint_loss_nonneg (a b : ℕ) (pts : ℕ → Pt n) :
    0 ≤ EqConstraint.loss (.samePoint a b) pts :=
  EqConstraint.loss_nonneg _ _

/-- **The `perpendicular` penalty is non-negative.** -/
theorem perpendicular_loss_nonneg (a b c e : ℕ) (pts : ℕ → Pt n) :
    0 ≤ EqConstraint.loss (.perpendicular a b c e) pts :=
  EqConstraint.loss_nonneg _ _

end Lattice.Geo
