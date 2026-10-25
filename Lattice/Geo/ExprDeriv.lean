import Mathlib
import Lattice.Geo.Differentiable
import Lattice.Geo.Pipeline

/-!
# `Lattice.Geo.ExprDeriv` -- differentiating a geometric expression

## Why this file exists

`Lattice.Geo.Derivative` records the obligation `HasNonzeroDeriv` as a hypothesis because nobody had proved that a
`GeoExpr`'s evaluation is differentiable. This file discharges it for the flattened carrier.

## The carrier, and why it must be finite

`GeoExpr.evalPts` takes `ℕ → Pt n`, which has no normed-group structure -- an infinite product of copies of `ℝ`
is not a normed space in the sense `HasFDerivAt` requires. The differentiability statement is therefore made
about the **flattened** carrier `Fin (k * n) → ℝ`, read back through `unflatten`.
`Lattice.Geo.Differentiable` already works there (`coordProj`, `hasFDerivAt_coord`), which is what makes the
recursion tractable.

The price is a side condition: `coord p axis` differentiates to the projection of point `p`, which exists on the
flattened carrier only when `p < k`. That is a real bound -- an expression mentioning point `k` cannot be read on
a carrier holding only `k` points -- and it is carried as `p < k` at every `coord` rather than hidden.

## The recursion

| constructor | derivative |
|:--|:--|
| `coord p axis` | the projection at `(p, axis)` |
| `const c` | `0` |
| `add e₁ e₂` | sum of derivatives |
| `sub e₁ e₂` | difference of derivatives |
| `mul e₁ e₂` | `e₂ · de₁ + e₁ · de₂` (product rule) |

Each row is the corresponding calculus rule, and `hasFDerivAt_eval` is the induction that turns them into one
theorem.

## What is and is not a hypothesis

The bound `p < k` is a hypothesis on the *expression-carrier pair*, not on the expression alone: a caller with an
expression mentioning point `p` simply chooses `k > p`. It cannot be removed, because the flattened carrier has no
slot for point `k`.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The largest point index an expression mentions.** A carrier with more than this many points can read the
expression; that is exactly the bound the differentiability statement needs. -/
def GeoExpr.maxPoint : GeoExpr n → ℕ
  | .coord p _ => p
  | .const _ => 0
  | .add e₁ e₂ => max (maxPoint e₁) (maxPoint e₂)
  | .sub e₁ e₂ => max (maxPoint e₁) (maxPoint e₂)
  | .mul e₁ e₂ => max (maxPoint e₁) (maxPoint e₂)

/-- **A flattened configuration reads every point the expression mentions**, given `maxPoint e < k`.

This is the bridge between the side condition and the carrier: it is what lets each `coord` case of the induction
produce a projection instead of getting stuck. -/
theorem maxPoint_lt_of_coord {e : GeoExpr n} {p : ℕ} {axis : Fin n}
    (h : GeoExpr.coord p axis = e) (hk : GeoExpr.maxPoint e < k) : p < k := by
  subst h
  simpa [GeoExpr.maxPoint] using hk

/-- **A finite configuration read as an `ℕ`-indexed one**, filling the remaining points with the origin.

The bridge between the flattened carrier (where analysis works) and `evalPts`'s own domain. Points beyond `k`
are never read, because `maxPoint e < k` bounds every index an expression can mention. -/
noncomputable def toNatConfig (w : Fin (k * n) → ℝ) : ℕ → Pt n :=
  fun p => if h : p < k then unflatten w ⟨p, h⟩ else 0

/-- **The derivative of an expression's evaluation, as a continuous linear functional on the flattened carrier.**

Defined by recursion so that `hasFDerivAt_eval` is an induction rather than a definition unfolding. The `mul`
case carries the product rule verbatim, which is why the operator-valued recursion closes.
-/
noncomputable def derivExpr (k : ℕ) (e : GeoExpr n) (w : Fin (k * n) → ℝ) :
    (Fin (k * n) → ℝ) →L[ℝ] ℝ :=
  match e with
  | .coord p axis =>
    if h : p < k then coordProj k n ⟨p, h⟩ axis else 0
  | .const _ => 0
  | .add e₁ e₂ => derivExpr k e₁ w + derivExpr k e₂ w
  | .sub e₁ e₂ => derivExpr k e₁ w - derivExpr k e₂ w
  | .mul e₁ e₂ =>
    e₂.evalPts (toNatConfig w) • derivExpr k e₁ w
      + e₁.evalPts (toNatConfig w) • derivExpr k e₂ w

/-! ## The induction

Each constructor is the corresponding calculus rule. The `coord` case reduces to
`Lattice.Geo.Differentiable.hasFDerivAt_coord`; `const` is constant; `add` and `sub` combine by linearity; `mul`
uses the product rule `HasFDerivAt.mul`, and its coefficient functions are the subexpressions' values, which are
themselves differentiable by the induction hypothesis.

The bound `maxPoint e < k` is what makes the `coord` case land on a real index. It propagates to the
subexpressions through `GeoExpr.maxPoint`'s definition, which is why that function is defined by the same
recursion.
-/

/-- **Every subexpression's points are within the whole's bound.** -/
theorem maxPoint_le_add_left {e₁ e₂ : GeoExpr n} : GeoExpr.maxPoint e₁ ≤ GeoExpr.maxPoint (.add e₁ e₂) := by
  simp [GeoExpr.maxPoint]

theorem maxPoint_le_sub_left {e₁ e₂ : GeoExpr n} : GeoExpr.maxPoint e₁ ≤ GeoExpr.maxPoint (.sub e₁ e₂) := by
  simp [GeoExpr.maxPoint]

theorem maxPoint_le_mul_left {e₁ e₂ : GeoExpr n} : GeoExpr.maxPoint e₁ ≤ GeoExpr.maxPoint (.mul e₁ e₂) := by
  simp [GeoExpr.maxPoint]

/-- **A point index below the whole's bound is below `k`.** -/
theorem lt_of_le_maxPoint {e : GeoExpr n} {p : ℕ} (h : p ≤ GeoExpr.maxPoint e)
    (hk : GeoExpr.maxPoint e < k) : p < k :=
  lt_of_le_of_lt h hk

/-- **A subexpression's bound follows from the whole's.** -/
theorem maxPoint_lt_of_le {e : GeoExpr n} {p : ℕ} (hp : p ≤ GeoExpr.maxPoint e)
    (hk : GeoExpr.maxPoint e < k) : p < k :=
  lt_of_le_of_lt hp hk

/-- **A configuration reads a coordinate the same way on both carriers.**

The link between `evalPts` (on `ℕ → Pt n`) and `unflatten` (on the flattened carrier): for a point index within
the bound, the two agree. -/
theorem evalPts_coord_of_lt {e : GeoExpr n} {p : ℕ} {axis : Fin n} {w : Fin (k * n) → ℝ}
    (hpk : p < k) :
    (GeoExpr.coord p axis).evalPts (toNatConfig w) = unflatten w ⟨p, hpk⟩ axis := by
  show toNatConfig w p axis = unflatten w ⟨p, hpk⟩ axis
  unfold toNatConfig
  rw [dif_pos hpk]

/-! ## The induction -/

/-- **Every expression is differentiable on a carrier large enough to read it.**

The bound `maxPoint e < k` is the content of "large enough": an expression mentioning point `k` has no place to
live on a carrier with `k` points, and the `coord` case would have to produce a projection for a point that does
not exist.

The induction is structural. `coord` cites `Lattice.Geo.Differentiable.hasFDerivAt_coord`; `const` is constant;
`add` and `sub` combine by linearity; `mul` uses the product rule with the subexpressions' values as
coefficients, which are themselves differentiable by the induction hypotheses.
-/
theorem hasFDerivAt_eval (k : ℕ) (e : GeoExpr n) (hk : GeoExpr.maxPoint e < k)
    (w : Fin (k * n) → ℝ) :
    HasFDerivAt (fun y => e.evalPts (toNatConfig y)) (derivExpr k e w) w := by
  induction e with
  | coord p axis =>
    -- the index is within the carrier, so the projection is the derivative
    by_cases hpk : p < k
    · have := hasFDerivAt_coord (k := k) (n := n) ⟨p, hpk⟩ axis w
      -- `evalPts` reads the coordinate through `toNatConfig`, which agrees on indices below `k`
      simpa [derivExpr, dif_pos hpk, toNatConfig, dif_pos hpk] using this
    · exact absurd (lt_of_le_of_lt (by simp [GeoExpr.maxPoint] : p ≤ GeoExpr.maxPoint (.coord p axis)) hk) hpk
  | const c =>
    -- a constant has zero derivative
    simpa [derivExpr] using
      (hasFDerivAt_const (c : ℝ) (x := w) : HasFDerivAt (fun _ : Fin (k * n) → ℝ => c) 0 w)
  | add e₁ e₂ ih₁ ih₂ =>
    have h₁ := ih₁ (by simp [GeoExpr.maxPoint] at hk ⊢; omega)
    have h₂ := ih₂ (by simp [GeoExpr.maxPoint] at hk ⊢; omega)
    simpa [derivExpr, GeoExpr.evalPts] using h₁.add h₂
  | sub e₁ e₂ ih₁ ih₂ =>
    have h₁ := ih₁ (by simp [GeoExpr.maxPoint] at hk ⊢; omega)
    have h₂ := ih₂ (by simp [GeoExpr.maxPoint] at hk ⊢; omega)
    simpa [derivExpr, GeoExpr.evalPts] using h₁.sub h₂
  | mul e₁ e₂ ih₁ ih₂ =>
    have hk₁ : GeoExpr.maxPoint e₁ < k := by simp [GeoExpr.maxPoint] at hk ⊢; omega
    have hk₂ : GeoExpr.maxPoint e₂ < k := by simp [GeoExpr.maxPoint] at hk ⊢; omega
    have h₁ := ih₁ hk₁
    have h₂ := ih₂ hk₂
    -- the product rule; `HasFDerivAt.mul` produces the same two summands in the opposite order
    have hmul := h₁.mul h₂
    simpa [derivExpr, GeoExpr.evalPts, smul_eq_mul, add_comm] using hmul

end Lattice.Geo
