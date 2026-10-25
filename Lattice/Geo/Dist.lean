import Mathlib
import Lattice.Geo.Expr
import Lattice.Lib.Linear.PenaltyVector

/-!
# `Lattice.Geo.Dist` -- distances and the square layer

## The one idea in this file

`Lv-00`'s IR carries `sqrt` in `dist`, which makes every distance-bearing constraint transcendental
(`_archive/IR-DEFECTS.md`, defect 2). The way out is not to remove the square root but to observe that
`sqrt` is **injective on the non-negative reals**, so

```
dist a b = dist c d   ↔   ‖a - b‖² = ‖c - d‖²
```

taken under the side condition that both squared quantities are non-negative -- which they are, being
sums of squares.

`Lv-00` proved exactly this at dimension two (`RealLv00GeometryAnalytic.sq_dist_eq_of_dist_eq`, three
lines: `Real.sqrt_inj` plus two `positivity`). Nothing about it is two-dimensional, so this file states
it for `Pt n := Fin n → ℝ` and reuses `Lattice.Lib.Linear.PenaltyVector.sqNorm`, which already exists
for exactly this purpose.

## Why the direction matters, and what is *not* proved

The **injective** direction (`dist` equal ⟹ squares equal) is the useful one: it turns a `sqrt`
constraint into a polynomial one, with no side condition at all.

The **reverse** direction needs `0 ≤ d`, and the honest statement therefore carries it. Stating the
reverse without that hypothesis would be false -- `d` and `-d` have the same square -- and this project
does not move side conditions into prose.

## What stays out

`angle` and `equalAngle` involve `Real.cos` and a ratio of distances; they are not polynomial and are
not handled here. They are recorded as owed rather than approximated, per
`_archive/ZERO-ESCAPE-NOT-IMPLEMENTED.md`.
-/

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

variable {n : ℕ}

/-- The difference of two points, as a vector. -/
noncomputable def diff (p q : Pt n) : Pt n := fun i => p i - q i

/-- **Squared distance** between two points: `Σᵢ (pᵢ - qᵢ)²`.

This is deliberately *not* `dist p q ^ 2`. It is the polynomial that the whole reduction works with,
and defining it directly means every lemma below is about a polynomial, not about a square of a square
root that happens to simplify.

It is exactly `sqNorm` applied to `diff p q`, which is why `sqNorm`'s two lemmas -- non-negativity and
"vanishes iff every component does" -- apply without restatement. -/
noncomputable def sqDist (p q : Pt n) : ℝ := sqNorm (diff p q)

/-- `sqDist` is `sqNorm` of the difference. Stated so callers can rewrite rather than unfold. -/
theorem sqDist_eq_sqNorm (p q : Pt n) : sqDist p q = sqNorm (diff p q) := rfl

/-- **Squared distance is non-negative.** -/
theorem sqDist_nonneg (p q : Pt n) : 0 ≤ sqDist p q :=
  sqNorm_nonneg _

/-- **Squared distance vanishes exactly when the points coincide.**

The `←` direction is what makes the square layer replace `dist` faithfully: two points at distance
zero are the same point, so a constraint `sqDist a b = 0` is the constraint `a = b`. -/
theorem sqDist_eq_zero_iff (p q : Pt n) : sqDist p q = 0 ↔ p = q := by
  rw [sqDist]
  rw [sqNorm_eq_zero_iff]
  constructor
  · intro h
    funext i
    have := h i
    simp only [diff, Pi.sub_apply] at this
    linarith
  · intro h i
    rw [h]
    simp [diff]

/-- **Distance**, the square root of `sqDist`. This is the only place a square root appears. -/
noncomputable def dist (p q : Pt n) : ℝ := Real.sqrt (sqDist p q)

/-- Distance is non-negative, without any side condition. -/
theorem dist_nonneg (p q : Pt n) : 0 ≤ dist p q := Real.sqrt_nonneg _

/-- **Distance squared recovers the squared distance**, unconditionally.

`Real.sq_sqrt` needs non-negativity, which `sqDist_nonneg` supplies for free. This is why the square
layer costs nothing on the forward direction. -/
theorem dist_sq (p q : Pt n) : dist p q ^ 2 = sqDist p q := by
  rw [dist, Real.sq_sqrt (sqDist_nonneg p q)]

/-- **Equal distances imply equal squared distances.**

This is the reduction: a `sqrt`-bearing constraint becomes a polynomial one, with no side condition.
The proof is `Real.sqrt_inj` after observing that both arguments are sums of squares -- the same three
steps `Lv-00` used at dimension two, now at every dimension. -/
theorem sqDist_eq_of_dist_eq (p q r s : Pt n) (h : dist p q = dist r s) :
    sqDist p q = sqDist r s := by
  have h1 : 0 ≤ sqDist p q := sqDist_nonneg p q
  have h2 : 0 ≤ sqDist r s := sqDist_nonneg r s
  have h' : Real.sqrt (sqDist p q) = Real.sqrt (sqDist r s) := h
  exact (Real.sqrt_inj h1 h2).mp h'

/-- **Equal squared distances imply equal distances**, given that one of them is the square of a
non-negative number.

The hypothesis `0 ≤ d` is not removable: `d` and `-d` have the same square, so without it the reverse
direction is false. Stating it here rather than in prose is the point of the whole `Geo` layer. -/
theorem dist_eq_of_sqDist_eq (p q : Pt n) (d : ℝ) (hd : 0 ≤ d)
    (h : sqDist p q = d ^ 2) : dist p q = d := by
  rw [dist, h]
  exact Real.sqrt_sq hd

/-- **Equal distances to a common value imply equal squared distances.**

A specialisation of `sqDist_eq_of_dist_eq` that is the form constraints actually take:
`dist a b = d` and `dist c e = d` give `sqDist a b = sqDist c e` with no side condition. -/
theorem sqDist_eq_of_dist_eq_same (p q r s : Pt n) (d : ℝ)
    (h₁ : dist p q = d) (h₂ : dist r s = d) : sqDist p q = sqDist r s :=
  sqDist_eq_of_dist_eq p q r s (h₁.trans h₂.symm)

end Lattice.Geo
