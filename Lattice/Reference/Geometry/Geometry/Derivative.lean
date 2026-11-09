import Mathlib
import Lattice.Reference.Geometry.Constraints.Pipeline
import Lattice.Lib.Penalty.PolyExact

/-!
# `Lattice.Geo.Derivative` -- the interface between the chain and the optimiser's conclusion

## What this file establishes, and what it deliberately does not

`Lattice.Geo.Pipeline.token_to_loss` ends at a penalty whose zero set is a linear form's vanishing set.
`Lattice.Lib.Penalty.PolyExact.sq_eq_zero_of_localMin` says a non-degenerate local minimum of a square is a zero.
Composing them gives what a training procedure needs: **a local minimum of the penalty satisfies the
constraint**.

The composition needs one analytic fact -- that the embedded evaluation is differentiable with a nonzero
derivative. **That fact is not proved here.** `ofLinearForm` is built by list recursion over `GeoExpr`, and
differentiating a `GeoExpr` needs an induction over the expression tree that tracks the derivative of each
subexpression. Several attempts to wire the existing `Lattice.Geo.Differentiable` projections into that induction
ran into a carrier mismatch: analytic notions need a normed group, and the pipeline's carrier `ℕ → Pt n` has
none.

What this file therefore provides is the **interface**: the predicate a caller must discharge, and the
composition proved from it. That is worth having on its own -- it names exactly which obligation remains, in a
form a reader can check -- and the obligation is recorded in `_archive/KNOWN-GAPS.md` rather than approximated
with a placeholder.

## Why the carrier is a parameter

The obstruction is that `ℕ → Pt n` is not a normed group, so the analytic hypotheses cannot be stated at the
pipeline's own carrier. Making `E` a parameter lets the caller instantiate it at whatever finite carrier their
application uses -- `Fin (k*n) → ℝ` via `Lattice.Geo.Flatten`, for instance -- without this file committing to a
particular embedding. `Lattice.Geo.Flatten` already provides the bijection a caller needs to move between `ℕ → Pt n`
and a finite carrier.

## Why a nonzero derivative is needed

A constant form has zero derivative, so its square has a minimum everywhere and the dichotomy cannot fire. That
is a real condition about the constraint's non-degeneracy, not a technicality.
-/

namespace Lattice.Geo

open Lattice.Lib.Penalty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The obligation an analytic treatment of the chain must discharge**: the embedded evaluation is
differentiable at a point, with a non-vanishing derivative.

Stated as a predicate rather than a formula because the formula is exactly what the missing `GeoExpr` induction
would produce. Naming the obligation is what makes the gap checkable rather than invisible. -/
def HasNonzeroDeriv (f : E → ℝ) (x : E) : Prop :=
  ∃ f' : E →L[ℝ] ℝ, f' ≠ 0 ∧ HasFDerivAt f f' x

/-- **A nondegenerate local minimum of the square is a zero**, *given* that obligation.

This is the composition, and it is the full content of "the optimiser's conclusion follows from the chain": the
hypothesis `hderiv` is the only analytic input, and everything else is already proved in
`Lattice.Lib.Penalty.PolyExact`. If `HasNonzeroDeriv` is ever discharged for a concrete `f`, this theorem becomes
the unconditional statement without modification. -/
theorem localMin_implies_zero (f : E → ℝ) (x : E)
    (hderiv : HasNonzeroDeriv f x) (hmin : IsLocalMin (fun y => f y ^ 2) x) :
    f x = 0 := by
  obtain ⟨f', hne, hfd⟩ := hderiv
  -- argument order is `hderiv → hne → hmin`
  exact sq_eq_zero_of_localMin hfd hne hmin

/-- **The chain's penalty is the square of the embedded expression.**

A definitional identity, recorded because the composition speaks about squares while the chain's penalty is
`EqConstraint.loss`; the two must be the same function for `Lattice.Lib.Penalty.PolyExact` to apply to the chain at
all. This is the bridge between `Lattice.Geo.Pipeline` and the analytic statement above. -/
theorem lossOfLinearForm_eq_sq {n : ℕ} (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    lossOfLinearForm c pts = (ofLinearForm c).evalPts pts ^ 2 :=
  rfl

/-- **The optimizer's conclusion for the chain**, stated with the penalty as the function under study.

Whatever carrier the caller works on, if the embedded evaluation is differentiable with a nonzero derivative and
the penalty has a local minimum there, then the penalty vanishes there -- that is, the constraint holds. The
hypothesis about `evalPts` is exactly what `lossOfLinearForm_eq_sq` turns into a hypothesis about the penalty.
-/
theorem localMin_implies_penalty_zero {n : ℕ} (c : Lattice.Core.LinearForm ℝ n)
    (embed : E → ℕ → Pt n) (x : E)
    (hderiv : HasNonzeroDeriv (fun y => (ofLinearForm c).evalPts (embed y)) x)
    (hmin : IsLocalMin (fun y => (ofLinearForm c).evalPts (embed y) ^ 2) x) :
    lossOfLinearForm c (embed x) = 0 := by
  have hzero : (ofLinearForm c).evalPts (embed x) = 0 :=
    localMin_implies_zero _ x hderiv hmin
  rw [lossOfLinearForm_eq_sq, hzero]
  ring

end Lattice.Geo
