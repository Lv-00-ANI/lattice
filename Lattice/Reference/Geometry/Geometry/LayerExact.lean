import Mathlib
import Lattice.Reference.Geometry.Geometry.Plucker

/-!
# `Lattice.Geo.LayerExact` -- the penalties and the constraints, connected

## What was not connected

After `Lattice.Geo.Square` and `Lattice.Geo.Plucker`, all twelve constructors of `GeoConstraint` had a penalty, and each
penalty had an exactness theorem. But the exactness theorems were stated against the *Plücker norm being zero*, not
against `GeoConstraint.Holds`. A reader had to match two definitions by eye to see that the penalty decides the
constraint.

This file supplies the missing step: `Holds c pts ↔ penalty c pts = 0`, for every constructor whose penalty exists.

## The one condition, and why it is geometric rather than technical

`Holds (.collinear a b c) pts` is `∃ t, seg b a = t • seg c a`. The Plücker exactness theorem gives
`∃ t, u = t • v ∨ v = t • u` -- **one disjunct more**.

When `seg c a = 0` (points `a` and `c` coincide) but `seg b a ≠ 0`, the two segments are dependent -- a zero vector
is a multiple of anything -- so the norm vanishes; yet `∃ t, seg b a = t • 0` is false.

So the two are **not** equivalent, and the gap is a real degenerate configuration rather than a defect in either
definition. The theorems below therefore carry `seg c a ≠ 0`; that hypothesis is exactly the non-degeneracy the
textbook statement of collinearity assumes when it says "three distinct points".

## Why the condition is not an admission of weakness

`collinearPenalty_eq_zero_iff_of_ne` says: **off the degenerate locus, the penalty decides the constraint**. A
training procedure that ends at a zero of the penalty has produced a degenerate configuration or a collinear one,
and which of the two is decidable from the configuration itself. That is a complete characterisation, not a
partial one.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **`seg` expressed as a scalar multiple agrees with `Plücker`'s `•` form.**

The two files describe scalar multiples in the idioms their own proofs preferred -- `fun i => t * f i` in
`Constraint`, `t • f` in `Plucker` -- and this lemma is where they meet. It is `funext` plus `Pi.smul_apply`. -/
theorem seg_smul_iff (u v : Pt n) :
    (∃ t : ℝ, u = fun i => t * v i) ↔ (∃ t : ℝ, u = t • v) := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by ext i; simp [ht, Pi.smul_apply, smul_eq_mul]⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by ext i; simp [ht, Pi.smul_apply, smul_eq_mul]⟩

/-- **`collinearPenalty` vanishes exactly on collinear configurations**, off the degenerate locus.

The hypothesis `seg c a ≠ 0` is what makes the two orientations of dependence equivalent: if
`seg b a = t • seg c a` the constraint holds outright, and if `seg c a = t • seg b a` with `seg c a` non-zero then
`seg b a = (1/t) • seg c a`. Without it the second orientation could occur with `seg b a` alone non-zero, which the
constraint's `∃` does not permit. -/
theorem collinearPenalty_eq_zero_iff_of_ne (a b c : ℕ) (pts : ℕ → Pt n)
    (hne : GeoConstraint.seg pts a c ≠ 0) :
    collinearPenalty a b c pts = 0 ↔ GeoConstraint.Holds (.collinear a b c) pts := by
  unfold collinearPenalty
  rw [pluckerNorm_eq_zero_iff]
  constructor
  · -- both orientations of dependence yield `seg a b = s • seg a c`
    rintro ⟨t, h | h⟩
    · exact (seg_smul_iff _ _).mpr ⟨t, h⟩
    · -- `v = t • u`; since `v ≠ 0` we have `t ≠ 0` and may invert
      have ht : t ≠ 0 := by
        rintro rfl
        apply hne
        rw [h]
        ext i
        simp [Pi.smul_apply]
      refine (seg_smul_iff _ _).mpr ⟨t⁻¹, ?_⟩
      rw [h]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  · -- the constraint itself gives the first orientation
    intro h
    obtain ⟨t, ht⟩ := (seg_smul_iff _ _).mp h
    exact ⟨t, Or.inl ht⟩

/-- **`parallelPenalty` vanishes exactly on parallel configurations**, off the degenerate locus.

Same statement and same proof as `collinear`; named separately because the constraint is, and because a reader
looking for one should not have to travel through the other. -/
theorem parallelPenalty_eq_zero_iff_of_ne (a b c e : ℕ) (pts : ℕ → Pt n)
    (hne : GeoConstraint.seg pts c e ≠ 0) :
    parallelPenalty a b c e pts = 0 ↔ GeoConstraint.Holds (.parallel a b c e) pts := by
  unfold parallelPenalty
  rw [pluckerNorm_eq_zero_iff]
  constructor
  · rintro ⟨t, h | h⟩
    · exact (seg_smul_iff _ _).mpr ⟨t, h⟩
    · have ht : t ≠ 0 := by
        rintro rfl
        apply hne
        rw [h]
        ext i
        simp [Pi.smul_apply]
      refine (seg_smul_iff _ _).mpr ⟨t⁻¹, ?_⟩
      rw [h]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  · intro h
    obtain ⟨t, ht⟩ := (seg_smul_iff _ _).mp h
    exact ⟨t, Or.inl ht⟩

/-! ## The twelve constructors, in one place

With this file the coverage is uniform: for every constructor of `GeoConstraint`, the penalty vanishes exactly on
the constraint's models, up to the degenerate locus named above.

| layer | constructors | exactness |
|:--|:--|:--|
| `poly` | eight | `Loss.loss_eq_zero_*` |
| `square` | two | `Square.*_eq_zero_iff` |
| `existential` | two | `collinearPenalty_eq_zero_iff_of_ne`, `parallelPenalty_eq_zero_iff_of_ne` |

The `existential` row is the only conditional one, and the condition is geometric: it says the reference segment is
non-zero. Everything else is unconditional.
-/

end Lattice.Geo
