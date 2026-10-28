import Mathlib
import Lattice.Domains.Differentiable
import Lattice.Domains.Square
import Lattice.Domains.ExprDeriv

/-!
# `Lattice.Geo.PenaltySmooth` -- the `square` penalties are differentiable

## What this closes

`Lattice.Geo.Square` establishes exactness for the two `square` penalties, and its closing note records that a
*local minimum* theorem is not available because differentiability had not been established. This file supplies
that premise.

## The three pieces, and where each was already proved

`sqDistEqPenalty a b d pts` is `(sqDist a b − d.evalPts pts)²`, and

* `sqDist a b` read on the flattened carrier is `∑ i, segComp a b i v ²` -- differentiable by
  `Lattice.Geo.Differentiable.differentiable_sqDistResid`;
* `d.evalPts ∘ toNatConfig` is differentiable by `Lattice.Geo.ExprDeriv.hasFDerivAt_eval`;
* `(· − ·)²` is differentiable, being a difference followed by a square.

So the smoothness is an assembly job, and `sqDist_eq_resid` is the only new identification -- the lemma that
`Square`'s `sqDist` and `Differentiable`'s residual sum are the same function.

## What this does *not* deliver, and why that is not a gap

A "local minimum satisfies the constraint" theorem is **not** provable for this layer, and its absence is not an
oversight. The `poly` layer gets such a theorem because its penalty is a *square whose gradient at a solution is
non-zero* -- a solution is a strictly positive minimum, so a local minimum must be a solution.

Here the penalty is itself a square of a residual. At a solution the residual is zero, so the penalty is zero and
its gradient is zero too: the minimum is *degenerate*, and `localMin_implies_zero` -- which needs a non-zero
derivative -- cannot fire.

What does hold, and is proved in `Square`, is the implication that matters for verification: **penalty zero
implies constraint satisfied**. A training procedure that drives the penalty to zero has produced a model; one
that merely reaches a stationary point may not have, and no theorem can claim otherwise. Recording the difference
is more useful than papering over it.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **`sqDist` on the flattened carrier is `Differentiable`'s residual.**

The two files reach the same function by different routes: `Dist` defines `sqDist` as a sum over coordinates of
squared differences of `Pt` components, and `Differentiable` builds `∑ i, segComp a b i v ^ 2` from projections.
This lemma is where they are identified, and it is what lets the smoothness result transfer. -/
theorem sqDist_eq_resid {k : ℕ} (a b : Fin k) (v : Fin (k * n) → ℝ) :
    sqDist (n := n) (unflatten v a) (unflatten v b)
      = ∑ i, segComp a b i v ^ 2 := by
  unfold sqDist segComp Lattice.Lib.Linear.PenaltyVector.sqNorm diff
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **The squared distance between two points is differentiable on the flattened carrier.** -/
theorem differentiable_sqDist {k : ℕ} (a b : Fin k) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ =>
      sqDist (n := n) (unflatten v a) (unflatten v b)) := by
  simpa only [sqDist_eq_resid] using differentiable_sqDistResid (n := n) a b

/-- **`sqDistEq`'s penalty is differentiable**, whenever the expression on the right side is.

The hypothesis `hd` is the expression's smoothness, which `Lattice.Geo.ExprDeriv.hasFDerivAt_eval` supplies for any
`GeoExpr` on a large enough carrier. Stating it as a hypothesis keeps this file independent of the carrier bound. -/
theorem differentiable_sqDistEqPenalty {k : ℕ} (a b : Fin k) (d : GeoExpr n)
    (hd : Differentiable ℝ (fun v : Fin (k * n) → ℝ => d.evalPts (toNatConfig v))) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ => sqDistEqPenalty a b d (toNatConfig v)) := by
  -- the penalty is the square of a difference, and both factors are differentiable
  have h : (fun v : Fin (k * n) → ℝ => sqDistEqPenalty a b d (toNatConfig v))
      = fun v : Fin (k * n) → ℝ =>
          (sqDist (n := n) (unflatten v a) (unflatten v b) - d.evalPts (toNatConfig v)) ^ 2 := by
    funext v
    unfold sqDistEqPenalty twoValuedPenalty
    -- 	oNatConfig v a and unflatten v a agree because  is a Fin k
    have hc : ∀ i : Fin k, toNatConfig v i = unflatten v i := by
      intro i
      unfold toNatConfig
      rw [dif_pos i.isLt]
    simp only [hc]
  rw [h]
  exact ((differentiable_sqDist a b).sub hd).pow 2

/-- **`equalLength`'s penalty is differentiable**: a difference of two squared distances, squared. -/
theorem differentiable_equalLengthPenalty {k : ℕ} (a b c e : Fin k) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ => equalLengthPenalty a b c e (toNatConfig v)) := by
  have h : (fun v : Fin (k * n) → ℝ => equalLengthPenalty a b c e (toNatConfig v))
      = fun v : Fin (k * n) → ℝ =>
          (sqDist (n := n) (unflatten v a) (unflatten v b)
            - sqDist (n := n) (unflatten v c) (unflatten v e)) ^ 2 := by
    funext v
    unfold equalLengthPenalty twoValuedPenalty
    have hc : ∀ i : Fin k, toNatConfig v i = unflatten v i := by
      intro i
      unfold toNatConfig
      rw [dif_pos i.isLt]
    simp only [hc]
  rw [h]
  exact ((differentiable_sqDist a b).sub (differentiable_sqDist c e)).pow 2

end Lattice.Geo
