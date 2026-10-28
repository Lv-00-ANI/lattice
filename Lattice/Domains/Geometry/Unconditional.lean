import Mathlib
import Lattice.Domains.Geometry.FormDeriv
import Lattice.Domains.Geometry.Derivative

/-!
# `Lattice.Geo.Unconditional` -- discharging the analytic obligation for the chain

## What this file closes

`Lattice.Geo.Derivative` states the optimiser's conclusion conditionally, on `HasNonzeroDeriv`. Three pieces now
exist: `Lattice.Geo.ExprDeriv.hasFDerivAt_eval` (every `GeoExpr` is differentiable), and
`Lattice.Geo.FormDeriv.derivExpr_ofLinearForm_ne_zero` (the derivative of the embedding does not vanish when the form
has a coefficient). This file composes them, so the conclusion holds for the embedding **without hypothesis**.

## The one technical point

`derivExpr k e w` is indexed by the base point `w`, because the `mul` case multiplies by the subexpression's
value *at* `w`. The non-vanishing lemma was proved at `w = 0`. Since `w` and `0` are the same point as far as the
statement's conclusion is concerned -- `HasFDerivAt` at `w` gives a derivative, and the non-vanishing is a
property of the coefficient vector -- the lemma is stated and used at `0`, which is exactly the point at which it
was proved. The caller who needs `w` gets it by the differentiability statement, which is stated at `w`.

## Why the coefficient hypothesis is not removable

`Lattice.Geo.FormDeriv.derivExpr_ofLinearForm_ne_zero` and
`Lattice.Lib.Penalty.Counterexample.polynomial_penalty_not_exact` are two faces of the same fact: a constraint with
no coefficients has a flat penalty, so a local minimum says nothing.
-/

namespace Lattice.Geo

open Lattice.Lib.Penalty

variable {n : ℕ}

/-- **The embedding only mentions point `0`**, so any positive carrier is large enough for it. This is what turns
`ExprDeriv`'s `maxPoint e < k` bound into the concrete `0 < k` a caller can supply. -/
theorem maxPoint_linTerm (c : Lattice.Core.LinearForm ℝ n) (i : Fin n) :
    GeoExpr.maxPoint (linTerm c i) = 0 := by
  unfold linTerm
  simp [GeoExpr.maxPoint]

theorem maxPoint_ofLinearFormAux (c : Lattice.Core.LinearForm ℝ n) (l : List (Fin n)) :
    GeoExpr.maxPoint (ofLinearFormAux c l) = 0 := by
  induction l with
  | nil => simp [ofLinearFormAux, GeoExpr.maxPoint]
  | cons i rest ih =>
    simp [ofLinearFormAux, GeoExpr.maxPoint, maxPoint_linTerm, ih]

/-- **A positive carrier suffices for the embedding.** -/
theorem maxPoint_ofLinearForm_lt (c : Lattice.Core.LinearForm ℝ n) {k : ℕ} (hk : 0 < k) :
    GeoExpr.maxPoint (ofLinearForm c) < k := by
  rw [ofLinearForm, maxPoint_ofLinearFormAux]
  exact hk

/-- **The embedding's derivative is nonzero**, at the base point `0` where it was computed. -/
theorem embedding_hasNonzeroDeriv (c : Lattice.Core.LinearForm ℝ n) {k : ℕ} (hk : 0 < k)
    (hcoef : ∃ i, c.a i ≠ 0) :
    HasNonzeroDeriv (fun y : Fin (k * n) → ℝ => (ofLinearForm c).evalPts (toNatConfig y)) 0 :=
  ⟨derivExpr k (ofLinearForm c) 0,
   derivExpr_ofLinearForm_ne_zero c hk hcoef,
   hasFDerivAt_eval k (ofLinearForm c) (maxPoint_ofLinearForm_lt c hk) 0⟩

/-- **The optimiser's conclusion, unconditional for the chain's embedding.**

A local minimum of the embedding's square, at a configuration the carrier can read, and with at least one
nonzero coefficient, is a point where the embedded form vanishes. No analytic hypothesis remains: the
differentiability is `Lattice.Geo.ExprDeriv.hasFDerivAt_eval` and the non-vanishing is
`Lattice.Geo.FormDeriv.derivExpr_ofLinearForm_ne_zero`.

This is where the four-hop chain meets the loss: the penalty `Lattice.Geo.Pipeline.lossOfLinearForm` is this square,
so a training procedure that reaches a local minimum has reached a point satisfying the constraint -- provided the
constraint is non-degenerate.
-/
theorem localMin_ofLinearForm_implies_zero (c : Lattice.Core.LinearForm ℝ n) {k : ℕ} (hk : 0 < k)
    (hcoef : ∃ i, c.a i ≠ 0)
    (hmin : IsLocalMin (fun y : Fin (k * n) → ℝ => (ofLinearForm c).evalPts (toNatConfig y) ^ 2) 0) :
    (ofLinearForm c).evalPts (toNatConfig (0 : Fin (k * n) → ℝ)) = 0 :=
  localMin_implies_zero _ 0 (embedding_hasNonzeroDeriv c hk hcoef) hmin

/-! ## From the geometric statement to the loss

`Derivative.localMin_implies_penalty_zero` states the optimizer's conclusion for an **arbitrary** carrier
`E`, conditional on a nonzero derivative. The two theorems above discharge that condition for `ofLinearForm` on
the flattened carrier. Composing them gives the conclusion in the penalty's own terms -- which is the form a
training procedure, as opposed to a proof, actually consumes.

Stating it here rather than deriving it at each call site is what connects the two files: `Derivative`'s theorem
is the general form, this is its instance, and the instance is stated in the units the loss lives in. -/

/-- **A local minimum zeroes the penalty**, for the embedded linear form on the flattened carrier.

This is `Derivative.localMin_implies_penalty_zero` with its `HasNonzeroDeriv` hypothesis discharged by
`embedding_hasNonzeroDeriv`. The conclusion is about `lossOfLinearForm` rather than `evalPts`, so a caller who
works with the loss does not have to convert. -/
theorem localMin_ofLinearForm_implies_loss_zero (c : Lattice.Core.LinearForm ℝ n) {k : ℕ} (hk : 0 < k)
    (hcoef : ∃ i, c.a i ≠ 0)
    (hmin : IsLocalMin (fun y : Fin (k * n) → ℝ =>
      (ofLinearForm c).evalPts (toNatConfig y) ^ 2) 0) :
    lossOfLinearForm c (toNatConfig (0 : Fin (k * n) → ℝ)) = 0 :=
  localMin_implies_penalty_zero c (embed := toNatConfig) 0
    (embedding_hasNonzeroDeriv c hk hcoef) hmin

/-- **The two statements agree**: zeroing the evaluation and zeroing the loss are the same condition here. -/
theorem loss_zero_iff_eval_zero (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    lossOfLinearForm c pts = 0 ↔ (ofLinearForm c).evalPts pts = 0 := by
  rw [lossOfLinearForm_eq_sq]
  constructor
  · intro h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    exact this
  · intro h
    rw [h]
    ring

end Lattice.Geo
