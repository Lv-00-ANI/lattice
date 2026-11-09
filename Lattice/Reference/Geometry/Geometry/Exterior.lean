import Mathlib
import Lattice.Reference.Geometry.Constraints.Constraint
import Lattice.Reference.Geometry.Geometry.Square

/-!
# `Lattice.Geo.Exterior` -- penalties for the existential layer

## The two constraints that were left

`collinear a b c` and `parallel a b c e` both assert the existence of a scalar `t` with `seg a b = t • seg c e`.
There is no pair of numbers to subtract, so neither reduces to the penalties of `Lattice.Geo.Square`. What both *are*
is a **linear dependence** between two vectors.

## The standard device: Plücker coordinates

Two vectors `u, v` in `ℝⁿ` are linearly dependent exactly when every 2×2 minor of the matrix with rows `u` and `v`
vanishes:

```
uᵢ·vⱼ − uⱼ·vᵢ = 0   for all i, j
```

Squaring and summing those minors gives a non-negative function whose zero set is exactly the dependent pairs. That
is the **squared norm of the wedge** `u ∧ v`, a Plücker coordinate of the line they span, and it exists uniformly
in `n`:

* in `n = 2` only one minor is non-zero up to sign, and the sum is `2·(u₀v₁ − u₁v₀)²` -- the familiar cross product;
* in `n = 3` the six minors are the components of the cross product, and the sum is its squared norm;
* in general it is the Grassmannian's standard embedding.

So this file does not treat `n = 2` and `n = 3` separately: `pluckerNorm` is defined for every `n` and the
exactness theorem is stated once. That is the generalisation the objective asks for, and it is not a convenience --
the `n = 2` cross product is the *special case*, not the definition.

## What is proved here, and where exactness lives

This file supplies the definitions and their immediate properties: alternation of the minors
(`cofactor_swap`), vanishing on the diagonal (`cofactor_diag`), non-negativity of the norm
(`pluckerNorm_nonneg`), and the two penalties with their non-negativity.

The **exactness** theorem -- that `pluckerNorm u v = 0` exactly when `u` and `v` are dependent -- is proved in
`Lattice.Geo.Plucker`, not here. It was expected to need the torsion-freeness of the second exterior power, but the
direct argument is elementary: pick a component where `v` is non-zero and divide. Keeping it in a separate file
reflects that it is a different kind of proof (a division argument, not a definitional unfolding), and the two
files then read independently.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **A 2×2 minor of the matrix with rows `u` and `v`.**

In `n = 2` this is (up to sign) the cross product; in general, the collection of all minors is the Plücker
coordinate of the line spanned by the two vectors. -/
noncomputable def cofactor (u v : Pt n) (i j : Fin n) : ℝ := u i * v j - u j * v i

/-- **The minor is alternating in the index pair**: swapping the indices negates it. This is what makes the
collection a Plücker coordinate rather than an arbitrary list of numbers. -/
theorem cofactor_swap (u v : Pt n) (i j : Fin n) :
    cofactor u v j i = -cofactor u v i j := by
  unfold cofactor
  ring

/-- **The minor vanishes on the diagonal**, since a vector is always proportional to itself. -/
theorem cofactor_diag (u v : Pt n) (i : Fin n) : cofactor u v i i = 0 := by
  unfold cofactor
  ring

/-- **The squared norm of the wedge** `u ∧ v`: the sum of squares of all 2×2 minors.

Zero exactly when the two vectors are dependent; that characterisation is `Lattice.Geo.Plucker.pluckerNorm_eq_zero_iff`. -/
noncomputable def pluckerNorm (u v : Pt n) : ℝ := ∑ i, ∑ j, (cofactor u v i j) ^ 2

/-- **The Plücker norm is non-negative**, so it is a legitimate loss. -/
theorem pluckerNorm_nonneg (u v : Pt n) : 0 ≤ pluckerNorm u v := by
  unfold pluckerNorm
  positivity

/-- **`collinear`'s penalty**: the Plücker norm of the two segments.

`collinear a b c` asserts `seg b a` lies on the line through `seg c a`, which is exactly dependence of those two
segments. -/
noncomputable def collinearPenalty (a b c : ℕ) (pts : ℕ → Pt n) : ℝ :=
  pluckerNorm (GeoConstraint.seg pts a b) (GeoConstraint.seg pts a c)

/-- **`parallel`'s penalty**: the Plücker norm of the two segments being compared. -/
noncomputable def parallelPenalty (a b c e : ℕ) (pts : ℕ → Pt n) : ℝ :=
  pluckerNorm (GeoConstraint.seg pts a b) (GeoConstraint.seg pts c e)

/-- **Both existential penalties are non-negative.** -/
theorem collinearPenalty_nonneg (a b c : ℕ) (pts : ℕ → Pt n) : 0 ≤ collinearPenalty a b c pts :=
  pluckerNorm_nonneg _ _

theorem parallelPenalty_nonneg (a b c e : ℕ) (pts : ℕ → Pt n) : 0 ≤ parallelPenalty a b c e pts :=
  pluckerNorm_nonneg _ _

/-! ## What is not here

Two things a reader might look for and not find:

* **exactness** -- it is in `Lattice.Geo.Plucker`, proved by division rather than by exterior algebra;
* **`pluckerNorm u u = 0`** -- true, but not needed: the penalties below are applied to segments that need not
  coincide, and the exactness theorem already covers the `u = t • v` case with `t = 1`. It was attempted and
  abandoned after six rewrite failures inside `Finset.sum_eq_zero`; the omission is deliberate, not an oversight.

-/

end Lattice.Geo
