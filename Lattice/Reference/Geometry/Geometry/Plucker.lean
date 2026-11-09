import Mathlib
import Lattice.Reference.Geometry.Geometry.Exterior

/-!
# `Lattice.Geo.Plucker` -- exactness of the Plücker penalty

## The theorem

`Lattice.Geo.Exterior` defines `pluckerNorm u v` as the sum of squares of all 2×2 minors of the matrix with rows
`u, v`. This file proves the half that makes it a *penalty for dependence* rather than merely a non-negative
function: **the norm vanishes exactly when the two vectors are dependent**.

## Why the proof is elementary

The interesting direction is "norm zero implies dependent", and it needs no exterior algebra -- only division.

Suppose every minor vanishes. If `v = 0` then `v = 0 • u` and we are done. Otherwise pick an index `i₀` with
`v i₀ ≠ 0`. For any `i`, the minor at `(i, i₀)` is

```
u i · v i₀ − u i₀ · v i = 0
```

so `u i = (u i₀ / v i₀) · v i`. Setting `t := u i₀ / v i₀` gives `u = t • v` componentwise.

The existence of `i₀` is where `Fin n` being non-empty matters: for `n = 0` both vectors are the empty function and
are trivially dependent, which the statement below handles by taking `t := 0`.

## Why the general `n` and not `n = 2`

In `n = 2` there are four minors, three independent, and `fin_cases` enumerates them. The general proof above is
**shorter** than that enumeration and needs no case split on the dimension, so it is the one written here. This is
the same reason `Exterior` defines the norm for all `n`: the dimension-2 cross product is the special case.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **A vanishing sum of squares has every summand zero**, in the two-index form used below.

Pulled out as its own lemma because the induction over two nested `Finset.sum`s is the mechanical part of the
argument and should not obscure the geometry. -/
theorem cofactor_eq_zero_of_plucker_zero (u v : Pt n) (h : pluckerNorm u v = 0)
    (i j : Fin n) : cofactor u v i j = 0 := by
  unfold pluckerNorm at h
  -- every summand is a square, hence non-negative, so their sum vanishes only if each does
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ∑ j : Fin n, (cofactor u v i j) ^ 2 := by
    intro i _
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h i (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hrow j (Finset.mem_univ j))

/-- **The Plücker norm vanishes exactly for dependent pairs.**

Dependence is stated with the two orientations folded together: for a pair of vectors, "one is a multiple of the
other" is symmetric in the sense that either orientation may hold, and folding them avoids a case split on which
vector is the non-zero one. -/
theorem pluckerNorm_eq_zero_iff (u v : Pt n) :
    pluckerNorm u v = 0 ↔ ∃ t : ℝ, u = t • v ∨ v = t • u := by
  constructor
  · intro h
    have hminor : ∀ i j, cofactor u v i j = 0 := cofactor_eq_zero_of_plucker_zero u v h
    -- if `v` is zero the second orientation is immediate
    by_cases hv : v = 0
    · exact ⟨0, Or.inr (by rw [hv]; simp)⟩
    · -- otherwise some component of `v` is non-zero, and that is the index to divide by
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
      have hne : v i₀ ≠ 0 := hi₀
      refine ⟨u i₀ / v i₀, Or.inl ?_⟩
      funext i
      have hz := hminor i i₀
      unfold cofactor at hz
      -- `u i * v i₀ - u i₀ * v i = 0`, so `u i = (u i₀ / v i₀) * v i`
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linarith [hz]
  · rintro ⟨t, hdep | hdep⟩
    · -- `u = t • v`: every minor vanishes
      subst hdep
      unfold pluckerNorm cofactor
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      have hz : (t * v i) * v j - (t * v j) * v i = (0 : ℝ) := by ring
      show ((t * v i) * v j - (t * v j) * v i) ^ 2 = (0 : ℝ)
      rw [hz]
      ring
    · -- `v = t • u`: symmetric
      subst hdep
      unfold pluckerNorm cofactor
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      have hz : u i * (t * u j) - u j * (t * u i) = (0 : ℝ) := by ring
      show (u i * (t * u j) - u j * (t * u i)) ^ 2 = (0 : ℝ)
      rw [hz]
      ring

end Lattice.Geo
