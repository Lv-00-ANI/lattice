import Mathlib
import Lattice.Domains.Constraints.Expr
import Lattice.Lib.Linear.PenaltyVector
import Lattice.Lib.Penalty.QuadraticLocallyLipschitz

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


/-! ## `sqDist` 是**局部** Lipschitz 的，常数是 `4·B`

`Lattice.Lib.Penalty.QuadraticNotLipschitz.sq_not_lipschitz` 证明平方函数没有全局常数；
`QuadraticLocallyLipschitz.sum_sq_lipschitz_on_bounded` 证明在半径 `R` 的球上是 `2R`-Lipschitz。

**本节把后者搬到 `sqDist` 上。** 因为 `sqDist p q = sqNorm (diff p q) = ∑ i, (p i − q i)²`，
取 `f i := p i − q i`、`g i := p' i − q' i`，并注意
`|p i − q i| ≤ |p i| + |q i| ≤ 2B`，于是 `R = 2B`，常数是 `2R = 4B`。

⚠ **`p`、`q` 两侧都要有界**：距离的平方对**任一端**的移动都是二次敏感的，
所以只界一侧不够。这是「两点同时动」比「一点动」多出来的假设。
-/

/-- ⭐⭐ **`sqDist` 在半径 `B` 的球上是 Lipschitz 的**，常数 `4B`。

四个点（两组 `(p, q)`）都逐分量被 `B` 界住时，`sqDist` 的差不超过
`4B · ∑ i, |(p i − q i) − (p' i − q' i)|`。

**这是 `sum_sq_lipschitz_on_bounded` 的直接实例**，而那条在 `Lib/Penalty/` 里是抽象的；
**本定理是它在本库真实载体上的第一个消费者。** -/
theorem sqDist_lipschitz_on_bounded {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (p q p' q' : Pt n)
    (hp : ∀ i, |p i| ≤ B) (hq : ∀ i, |q i| ≤ B)
    (hp' : ∀ i, |p' i| ≤ B) (hq' : ∀ i, |q' i| ≤ B) :
    |sqDist p q - sqDist p' q'|
      ≤ 4 * B * ∑ i, |(p i - q i) - (p' i - q' i)| := by
  -- each difference component is bounded by `2B`
  have hf : ∀ i : Fin n, |(fun j => p j - q j) i| ≤ 2 * B := by
    intro i
    have h1 : |p i - q i| ≤ |p i| + |q i| := by
      have := abs_add (p i) (-(q i))
      simpa only [sub_eq_add_neg, abs_neg] using this
    linarith [hp i, hq i]
  have hg : ∀ i : Fin n, |(fun j => p' j - q' j) i| ≤ 2 * B := by
    intro i
    have h1 : |p' i - q' i| ≤ |p' i| + |q' i| := by
      have := abs_add (p' i) (-(q' i))
      simpa only [sub_eq_add_neg, abs_neg] using this
    linarith [hp' i, hq' i]
  have hmain := Lattice.Lib.Penalty.sum_sq_lipschitz_on_bounded
    (fun j => p j - q j) (fun j => p' j - q' j) (by linarith : (0:ℝ) ≤ 2 * B) hf hg
  -- `2 * (2 * B)` is `4 * B`
  have h4 : 2 * (2 * B) = 4 * B := by ring
  rw [h4] at hmain
  simpa only [sqDist, sqNorm, diff] using hmain


end Lattice.Geo