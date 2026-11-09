import Mathlib
import Lattice.Reference.Geometry.Constraints.Differentiable
import Lattice.Reference.Geometry.Geometry.Exterior
import Lattice.Reference.Geometry.Constraints.ExprDeriv

/-!
# `Lattice.Geo.ExteriorSmooth` -- the existential layer's penalties are differentiable

## What this completes

`Lattice.Geo.PenaltySmooth` proves the `square` penalties differentiable. This file does the same for the
`existential` layer, so that **every penalty in the project is differentiable** on the flattened carrier.

## The assembly, with nothing new

`pluckerNorm u v` is a double sum of squared 2×2 minors, and each minor is a difference of products of segments.
`Lattice.Geo.Differentiable.differentiable_segComp` gives each segment component differentiable, so

* a minor is `f·g − g·f'`, differentiable as a difference of products;
* the norm is a sum of squares of those, differentiable as a sum of powers;
* the penalty composes the norm with the segment map, differentiable as a composition.

No analytic content beyond `Differentiable.sum`, `.mul`, `.sub`, `.pow` -- which is the point: the Plücker
construction was chosen so its penalty is a polynomial in finitely many coordinates, and such polynomials are
differentiable by construction.

## The one real obstacle: `ℕ` versus `Fin`

`GeoConstraint.seg` and the penalties index points by `ℕ`, while `Lattice.Geo.Differentiable` states its lemmas for
`Fin k`. The bridge is `toNatConfig`, which reads a `Fin (k*n) → ℝ` as an `ℕ → Pt n` by returning **the origin for
indices at or beyond `k`**. An out-of-range index therefore still gives a smooth function -- a constant -- and
`differentiable_segCompNat` handles both cases by splitting on whether each endpoint is in range.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **A 2×2 minor relating the segments `a→b` and `c→e`**, indexed on `ℕ`.

`Lattice.Geo.Exterior.cofactor` takes two vectors `Pt n`; here the vectors are those two segments of a configuration,
and the indices are `ℕ` because that is what `GeoConstraint.seg` uses. -/
noncomputable def crossOf (a b c e : ℕ) (i j : Fin n) (pts : ℕ → Pt n) : ℝ :=
  GeoConstraint.seg pts a b i * GeoConstraint.seg pts c e j
    - GeoConstraint.seg pts a b j * GeoConstraint.seg pts c e i

/-- **`toNatConfig` agrees with `unflatten` on the carrier.**

`k` is inferred from the carrier type of `v`, so it is not a named argument; the definition is unfolded with
`show` and the bound is discharged by `p.isLt`. -/
theorem toNatConfig_apply {k : ℕ} (v : Fin (k * n) → ℝ) (p : Fin k) :
    toNatConfig v p = unflatten v p := by
  show (if h : p.val < k then unflatten v ⟨p.val, h⟩ else 0) = unflatten v p
  rw [dif_pos p.isLt]

/-- **`toNatConfig` is the origin beyond the carrier**, so it is constant -- hence smooth -- there. -/
theorem toNatConfig_eq_zero_of_ge {k : ℕ} (v : Fin (k * n) → ℝ) (p : ℕ) (hp : k ≤ p) :
    toNatConfig v p = 0 := by
  show (if h : p < k then unflatten v ⟨p, h⟩ else 0) = 0
  rw [dif_neg (Nat.not_lt.mpr hp)]

/-- **A segment component is differentiable for `Fin k` indices.** -/
theorem differentiable_segCompFin {k : ℕ} (a b : Fin k) (i : Fin n) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ =>
      GeoConstraint.seg (toNatConfig v) a.val b.val i) := by
  have h : (fun v : Fin (k * n) → ℝ => GeoConstraint.seg (toNatConfig v) a.val b.val i)
      = fun v => segComp (n := n) a b i v := by
    funext v
    simp only [GeoConstraint.seg, segComp, toNatConfig_apply]
  rw [h]
  exact differentiable_segComp (n := n) a b i

/-- **A coordinate of `toNatConfig` is differentiable for arbitrary `ℕ` indices.**

Inside the carrier this is `coordProj`; beyond it the value is the constant `0`. Both are smooth, and splitting on
the bound is what makes the two cases available. -/
theorem differentiable_toNatConfig_coord {k : ℕ} (p : ℕ) (i : Fin n) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ => toNatConfig v p i) := by
  by_cases hp : p < k
  · -- inside: the projection, which `Lattice.Geo.Differentiable` already covers
    have h : (fun v : Fin (k * n) → ℝ => toNatConfig v p i)
        = fun v => unflatten v ⟨p, hp⟩ i := by
      funext v
      simp only [toNatConfig, dif_pos hp]
    rw [h]
    exact differentiable_coord (n := n) ⟨p, hp⟩ i
  · -- outside: the constant zero
    have hzero : ∀ v : Fin (k * n) → ℝ, toNatConfig v p = 0 :=
      fun v => toNatConfig_eq_zero_of_ge v p (Nat.not_lt.mp hp)
    have h : (fun v : Fin (k * n) → ℝ => toNatConfig v p i) = fun _ => (0 : ℝ) := by
      funext v
      rw [hzero v]
      rfl
    rw [h]
    exact differentiable_const 0

/-- **A segment component is differentiable for *arbitrary* `ℕ` indices**, being a difference of two
coordinates. -/
theorem differentiable_segCompNat {k : ℕ} (a b : ℕ) (i : Fin n) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ => GeoConstraint.seg (toNatConfig v) a b i) := by
  have h : (fun v : Fin (k * n) → ℝ => GeoConstraint.seg (toNatConfig v) a b i)
      = fun v => toNatConfig v b i - toNatConfig v a i := by
    funext v
    simp only [GeoConstraint.seg]
  rw [h]
  exact (differentiable_toNatConfig_coord b i).sub (differentiable_toNatConfig_coord a i)

/-- **A Plücker minor is differentiable**: a difference of two products of segment components. -/
theorem differentiable_crossOfFn {k : ℕ} (a b c e : ℕ) (i j : Fin n) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ => crossOf (n := n) a b c e i j (toNatConfig v)) :=
  ((differentiable_segCompNat a b i).mul (differentiable_segCompNat c e j)).sub
    ((differentiable_segCompNat a b j).mul (differentiable_segCompNat c e i))

/-- **The Plücker norm of two segments is differentiable**: a sum of squared minors. -/
theorem differentiable_pluckerOfFn {k : ℕ} (a b c e : ℕ) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ =>
      ∑ i : Fin n, ∑ j : Fin n, (crossOf (n := n) a b c e i j (toNatConfig v)) ^ 2) :=
  Differentiable.sum (fun i _ =>
    Differentiable.sum (fun j _ => (differentiable_crossOfFn a b c e i j).pow 2))

/-- **The collinearity penalty is differentiable.**

`collinearPenalty a b c pts` is `pluckerNorm (seg a b) (seg a c)`, and `pluckerNorm` is the double sum of squared
minors -- so the statement is the previous one with the segments identified, which is `simp` plus the two
`unfold`s that relate `Exterior`'s spelling to this file's. -/
theorem differentiable_collinearPenalty {k : ℕ} (a b c : ℕ) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ =>
      collinearPenalty (n := n) a b c (toNatConfig v)) := by
  have h : (fun v : Fin (k * n) → ℝ => collinearPenalty (n := n) a b c (toNatConfig v))
      = fun v => ∑ i : Fin n, ∑ j : Fin n,
          (crossOf (n := n) a b a c i j (toNatConfig v)) ^ 2 := by
    funext v
    simp only [collinearPenalty, pluckerNorm, cofactor, crossOf]
  rw [h]
  exact differentiable_pluckerOfFn a b a c

/-- **The parallel penalty is differentiable**, by the same identification. -/
theorem differentiable_parallelPenalty {k : ℕ} (a b c e : ℕ) :
    Differentiable ℝ (fun v : Fin (k * n) → ℝ =>
      parallelPenalty (n := n) a b c e (toNatConfig v)) := by
  have h : (fun v : Fin (k * n) → ℝ => parallelPenalty (n := n) a b c e (toNatConfig v))
      = fun v => ∑ i : Fin n, ∑ j : Fin n,
          (crossOf (n := n) a b c e i j (toNatConfig v)) ^ 2 := by
    funext v
    simp only [parallelPenalty, pluckerNorm, cofactor, crossOf]
  rw [h]
  exact differentiable_pluckerOfFn a b c e

end Lattice.Geo
