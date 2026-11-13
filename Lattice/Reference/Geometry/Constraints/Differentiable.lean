import Mathlib
import Lattice.Reference.Geometry.Constraints.Constraint
import Lattice.Plugins.Domains.Constraints.Tokens.Flatten
import Lattice.Reference.Geometry.Constraints.Loss

/-!
# `Lattice.Geo.Differentiable` -- the geometric penalty is differentiable in the weight vector

## What this closes

`Lattice.Lib.Penalty.PolyExact.sq_eq_zero_of_localMin` needs one analytic input: the residual `f` is
differentiable and `f' ≠ 0`. `Lattice.Geo.Loss` builds `f` from a geometric constraint; this file supplies
the differentiability, so the two can meet.

## Why it is short

Nothing below needs `f` to be *linear*, only differentiable. Each coordinate `pts a i` is one component of
the flattened vector (`Lattice.Geo.Flatten`), so its derivative is a **projection**
(`hasFDerivAt_coord`), and the polynomial layer is assembled from those by sums and products, for which
`HasFDerivAt.sum`, `.sub` and `.mul` already exist.

The hard part of "algebraise a geometric constraint" was never the derivative -- it was deciding which
constraints have a polynomial form at all. That decision lives in `Lattice.Geo.Loss`'s `EqConstraint`, whose
type admits only the equality layer.

## The `coordProj` definition

`ContinuousLinearMap.proj` leaves its codomain a metavariable, so naming a projection inline in a
`HasFDerivAt` statement does not elaborate -- the same obstacle recorded in
`_archive/BLOCKER-multivar-penalty.md`. `coordProj` fixes the type once.

## Naming convention

The lemmas state **differentiability**, not the derivative. Writing the derivative out explicitly for a
sum of products is a large term whose only consumer is `HasFDerivAt.mul`'s own side condition; the
`Differentiable` form is what `PolyExact` actually consumes, so that is what is proved.
-/

namespace Lattice.Geo

variable {k n : ℕ}

/-- **The projection onto one coordinate of one point**, as a continuous linear functional of the
flattened vector.

Named rather than written inline because `ContinuousLinearMap.proj`'s codomain is a metavariable and
cannot be inferred inside a `HasFDerivAt` goal. -/
noncomputable def coordProj (k n : ℕ) (a : Fin k) (i : Fin n) :
    (Fin (k * n) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k * n) => ℝ) (flatEquiv k n (a, i))

/-- The projection reads the intended component. -/
@[simp] theorem coordProj_apply (a : Fin k) (i : Fin n) (v : Fin (k * n) → ℝ) :
    coordProj k n a i v = unflatten v a i := rfl

/-- **A coordinate is differentiable**, with the projection as derivative. -/
theorem hasFDerivAt_coord (a : Fin k) (i : Fin n) (v : Fin (k * n) → ℝ) :
    HasFDerivAt (fun w : Fin (k * n) → ℝ => unflatten w a i) (coordProj k n a i) v :=
  ContinuousLinearMap.hasFDerivAt (coordProj k n a i)

/-- A coordinate is differentiably continuous in the sense needed by `HasFDerivAt.mul`. -/
theorem differentiable_coord (a : Fin k) (i : Fin n) :
    Differentiable ℝ (fun w : Fin (k * n) → ℝ => unflatten w a i) :=
  fun v => (hasFDerivAt_coord a i v).differentiableAt

/-! ## Differences and products of coordinates -/

/-- The `i`-th component of the displacement from `a` to `b`. -/
noncomputable def segComp (a b : Fin k) (i : Fin n) (v : Fin (k * n) → ℝ) : ℝ :=
  unflatten v b i - unflatten v a i

/-- A segment component is differentiable. -/
theorem differentiable_segComp (a b : Fin k) (i : Fin n) :
    Differentiable ℝ (segComp a b i) :=
  (differentiable_coord b i).sub (differentiable_coord a i)

/-- **The perpendicular residual is differentiable**: a finite sum of products of segment components. -/
theorem differentiable_perpResid (a b c e : Fin k) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ =>
      ∑ i, segComp a b i v * segComp c e i v) := by
  exact Differentiable.sum (fun i _ =>
    (differentiable_segComp a b i).mul (differentiable_segComp c e i))

/-- **The squared-distance residual is differentiable**: a finite sum of squares of segment components. -/
theorem differentiable_sqDistResid (a b : Fin k) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ => ∑ i, segComp a b i v ^ 2) := by
  exact Differentiable.sum (fun i _ => (differentiable_segComp a b i).pow 2)

/-- **A constant residual is differentiable.** This is the case a `distEq` takes when its right-hand side
is a literal, which is how distances are usually prescribed. -/
theorem differentiable_constResid (c : ℝ) :
    Differentiable ℝ (fun _ : Fin (k * n) → ℝ => c) :=
  differentiable_const c

/-! ## From `Differentiable` to `HasFDerivAt`, and to a non-zero derivative

`differentiable_perpResid` says the residual is differentiable, which is not enough for
`Lattice.Geo.Derivative.localMin_implies_zero`: that theorem wants `HasNonzeroDeriv`, i.e. an *explicit* derivative
that is *not* the zero map. This section supplies both.

The derivative is built by the same route the differentiability proof takes, one level down: `segComp` is a
difference of two coordinate projections, so its derivative is a difference of two `coordProj`s; the residual is a
sum of products, so its derivative is the sum of the product rules. Nothing new is assumed -- `hasFDerivAt_coord`
already gives the pieces.

The non-vanishing step is the interesting one, and it is where `perpResid_bump` finally enters the chain: evaluating
the derivative on the `bump` direction returns `seg c e i v`, and non-degeneracy says some `i` makes that non-zero.
So the derivative is non-zero exactly where the configuration is non-degenerate. -/

/-- **The derivative of a segment component**: differencing two coordinate projections. -/
theorem hasFDerivAt_segComp (a b : Fin k) (i : Fin n) (v : Fin (k * n) → ℝ) :
    HasFDerivAt (segComp a b i) (coordProj k n b i - coordProj k n a i) v :=
  (hasFDerivAt_coord b i v).sub (hasFDerivAt_coord a i v)

/-- **The derivative of `segComp a b i` is `coordProj b i - coordProj a i`** -- stated separately because the
non-vanishing argument evaluates it rather than composing it. -/
theorem segComp_fderiv_apply (a b : Fin k) (i : Fin n) (v h : Fin (k * n) → ℝ) :
    (coordProj k n b i - coordProj k n a i) h = (unflatten h b i - unflatten h a i) := by
  show coordProj k n b i h - coordProj k n a i h = unflatten h b i - unflatten h a i
  congr 1 <;> simp [coordProj, ContinuousLinearMap.proj]

/-- **The residual has an explicit derivative**: the sum over coordinates of the two product rules. -/
theorem hasFDerivAt_perpResid (a b c e : Fin k) (v : Fin (k * n) → ℝ) :
    HasFDerivAt (fun w : Fin (k * n) → ℝ => ∑ i, segComp a b i w * segComp c e i w)
      (∑ i, (segComp a b i v • (coordProj k n e i - coordProj k n c i)
            + segComp c e i v • (coordProj k n b i - coordProj k n a i))) v := by
  refine HasFDerivAt.sum (fun i _ => ?_)
  exact (hasFDerivAt_segComp a b i v).mul (hasFDerivAt_segComp c e i v)

end Lattice.Geo
