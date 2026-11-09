import Mathlib
import Lattice.Reference.Geometry.Constraints.ExprDeriv
import Lattice.Reference.Geometry.Geometry.Derivative

/-!
# `Lattice.Geo.ExprLocalMin` -- the local-minimum guarantee for the expression penalty

## Two islands, one chain

`Lattice.Geo.Expr` proves the exactness of the expression penalty (`evalPts_sub_eq_zero_iff`), and
`Lattice.Geo.ExprDeriv` differentiates `evalPts` (`hasFDerivAt_eval`). `gov/audit_islands.py` listed both as islands:
nothing outside either module consumed their theorems, and nothing connected them to each other.

They belong to one argument. The penalty is exact, so a local minimum of the squared penalty ought to be a zero; that
step needs the derivative, which is exactly what `ExprDeriv` supplies. This file makes the connection explicit.

## What is proved, and what is assumed

**Proved:**

* `evalPts_hasNonzeroDeriv` -- if the derivative `derivExpr k e w` is non-zero, then `evalPts ∘ toNatConfig` has a
  non-zero derivative at `w` in the sense `HasNonzeroDeriv` wants. This is `hasFDerivAt_eval` read off directly.
* `evalPts_localMin_implies_zero` -- given that non-vanishing, a local minimum of the squared penalty is a zero.

**Assumed:** that `derivExpr k e w ≠ 0`. This is **not** automatic. A constant expression has zero derivative
everywhere, and its penalty is minimized -- at every point -- without vanishing. So a hypothesis is the honest form
here, not a gap to be closed by a cleverer tactic: the statement is false without it.

Naming the hypothesis rather than hiding it is the point: a reader can see exactly which configurations the
guarantee covers, and the counterexample above says why it cannot cover more. -/

namespace Lattice.Geo

variable {n : ℕ}

/-- **A non-vanishing derivative of `evalPts` is exactly `HasNonzeroDeriv`**, because `hasFDerivAt_eval` already
supplies the `HasFDerivAt` half with `derivExpr k e w` as the derivative. -/
theorem evalPts_hasNonzeroDeriv
    (k : ℕ) (e : GeoExpr n) (hk : e.maxPoint < k) (w : Fin (k * n) → ℝ)
    (hne : derivExpr k e w ≠ 0) :
    HasNonzeroDeriv (fun y : Fin (k * n) → ℝ => e.evalPts (toNatConfig y)) w :=
  ⟨derivExpr k e w, hne, hasFDerivAt_eval k e hk w⟩

/-- **The expression penalty's local-minimum guarantee.**

With the derivative non-vanishing, a local minimum of the squared penalty forces the penalty to vanish -- so the
configuration satisfies the expression equation exactly. Without that hypothesis the statement is false: a constant
expression minimizes its own penalty everywhere and equals its constant, which need not be zero.

The two halves come from the two modules: `hasFDerivAt_eval` (differentiation) and `localMin_implies_zero`
(first-order optimality). -/
theorem evalPts_localMin_implies_zero
    (k : ℕ) (e : GeoExpr n) (hk : e.maxPoint < k) (w : Fin (k * n) → ℝ)
    (hne : derivExpr k e w ≠ 0)
    (hmin : IsLocalMin
      (fun y : Fin (k * n) → ℝ => (e.evalPts (toNatConfig y)) ^ 2) w) :
    e.evalPts (toNatConfig w) = 0 :=
  localMin_implies_zero (fun y : Fin (k * n) → ℝ => e.evalPts (toNatConfig y)) w
    (evalPts_hasNonzeroDeriv k e hk w hne) hmin

/-- **A constant expression is the counterexample the hypothesis excludes**, stated so the boundary above is not
merely asserted: every point is a local minimum of its squared penalty, and the penalty equals the constant
everywhere rather than vanishing. -/
theorem constExpr_localMin_counterexample
    (c : ℝ) (w : Fin (k * n) → ℝ) :
    IsLocalMin (fun y : Fin (k * n) → ℝ => ((GeoExpr.const c).evalPts (toNatConfig y)) ^ 2) w := by
  have hconst : ∀ y : Fin (k * n) → ℝ, (GeoExpr.const c).evalPts (toNatConfig y) = c := by
    intro y
    simp [GeoExpr.evalPts]
  simp only [hconst]
  exact isLocalMin_const

end Lattice.Geo
