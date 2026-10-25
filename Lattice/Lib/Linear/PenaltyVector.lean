import Mathlib
import Lattice.Core.Syntax
import Lattice.Lift.PenaltyEmbedding

/-!
# `Lattice.Lib.Linear.PenaltyVector` -- the vector penalty, and where its proof stops

## What is in this file

The two algebraic facts a several-variable penalty argument needs, proved in full:

* `sqNorm_nonneg` -- a sum of squares is non-negative;
* `sqNorm_eq_zero_iff` -- it vanishes exactly when every component does.

These convert a *scalar* conclusion into a *componentwise* one, which is what the several-variable
exactness statement needs.

## What is deliberately not in this file

The theorem `IsLocalMin (∑ᵢ (aᵢxᵢ + bᵢ)²) x → ∀ i, aᵢxᵢ + bᵢ = 0` is **not** proved here, and the
attempt is recorded rather than hidden.

Two routes were tried.

**Route 1: apply the one-variable theorem to each summand.** Invalid. A local minimum of `∑ Lᵢ` need
not be a local minimum of any single `Lᵢ`: the sum can be flat while one term rises and another
falls. Componentwise reasoning from `Lattice.Lib.Linear.Penalty` is therefore unavailable.

**Route 2: several-variable Fermat** (`IsLocalMin.hasFDerivAt_eq_zero`). Mathematically correct --
the gradient is `∑ᵢ (2 rᵢ aᵢ) • projᵢ`, and a vanishing diagonal functional has all coefficients zero
-- but constructing the `HasFDerivAt` term for `∑ᵢ (aᵢxᵢ + bᵢ)²` did not elaborate on this
toolchain. The obstacle is the same class as `gov/BLOCKER-variable-width.md`:
`ContinuousLinearMap.proj` leaves its codomain a metavariable, so
`AddCommMonoid ((Fin n → ?m) →L[ℝ] ?m)` cannot be synthesised whenever the projection appears as a
value rather than an application. Fixing the codomain in a `def`, restating every lemma with a
pinned result type, and routing through `comp_hasDerivAt` all left the same stuck instance.

So the slot records the several-variable form as still owed, and this file contributes the algebraic
half rather than a partial theorem.

For a general matrix `A` the situation is further complicated: Fermat gives `Aᵀ(Ax + b) = 0`, and
concluding `Ax + b = 0` from that needs full **row** rank -- a statement about spans, not
coordinates.

## Why a partial file is still worth having

`sqNorm_eq_zero_iff` is exactly the lemma the missing proof would consume, so when the derivative
layer is built this file is a dependency rather than a dead end. It also does independent work: "a
sum of squares vanishes iff each term does" is used by every quantitative argument in `lib/`.
-/

namespace Lattice.Lib.Linear.PenaltyVector

/-- The squared norm, used as the loss for a residual vector. -/
noncomputable def sqNorm {n : ℕ} (r : Fin n → ℝ) : ℝ := ∑ i, (r i) ^ 2

/-- **A sum of squares is non-negative.** -/
theorem sqNorm_nonneg {n : ℕ} (r : Fin n → ℝ) : 0 ≤ sqNorm r :=
  Finset.sum_nonneg fun i _ => sq_nonneg (r i)

/-- **A sum of squares vanishes exactly when every component does.**

This is the bridge from a scalar conclusion (`sqNorm r = 0`) to a componentwise one
(`∀ i, r i = 0`), and it is the lemma the several-variable exactness proof would consume. -/
theorem sqNorm_eq_zero_iff {n : ℕ} (r : Fin n → ℝ) : sqNorm r = 0 ↔ ∀ i, r i = 0 := by
  unfold sqNorm
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (r i))]
  constructor
  · intro h i
    exact sq_eq_zero_iff.mp (h i (Finset.mem_univ i))
  · intro h i _
    simp [h i]

/-- The same statement with the residual written out, which is the form a caller holds. -/
theorem sqNorm_resid_eq_zero_iff {n : ℕ} (a b x : Fin n → ℝ) :
    sqNorm (fun i => a i * x i + b i) = 0 ↔ ∀ i, a i * x i + b i = 0 :=
  sqNorm_eq_zero_iff _

end Lattice.Lib.Linear.PenaltyVector
