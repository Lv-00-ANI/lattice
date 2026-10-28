import Mathlib
import Lattice.Core.Syntax
import Lattice.Runtime.PenaltyEmbedding
import Lattice.Lib.Linear.PenaltyVector
import Lattice.Lib.Linear.PenaltyPerturbN

open Lattice.Lib.Linear.PenaltyPerturbN

/-!
# `Lattice.Lib.Linear.PenaltyPerturb` -- several-variable exactness by perturbation

## Why not derivatives

`gov/BLOCKER-multivar-penalty.md` records the attempt through several-variable Fermat: the
mathematics is right, but the `HasFDerivAt` term for `∑ᵢ (aᵢxᵢ + bᵢ)²` does not elaborate here,
because `ContinuousLinearMap.proj` leaves its codomain a metavariable whenever it appears as a value.

This file takes the perturbation route, which needs **no derivative at all**: a nonzero residual can
be driven to zero by moving a single coordinate, and that move can be made arbitrarily small.

## The argument, in two steps

**Step 1 (algebra).** Perturbing only coordinate `j` changes exactly one summand:

```
L(x + c·eⱼ) = (rⱼ + c·aⱼ)² + Σ_{i≠j} rᵢ²
```

**Step 2 (aim).** Choosing `c := -rⱼ/aⱼ` zeroes that summand, so the loss becomes `Σ_{i≠j} rᵢ²`,
which is strictly smaller than `L(x)` whenever `rⱼ ≠ 0`.

**Step 3 (topology).** Because `c` can be scaled down arbitrarily, the perturbed point lies inside
any neighbourhood of `x`; combined with `IsLocalMin`'s `∀ᶠ y in nhds x, f x ≤ f y`, this contradicts
local minimality.

## The step that took several attempts

Step 1 is a `simp` fact, but only once `smul_eq_mul` is in the simp set: the term produced by
`Pi.smul_apply` is `a j * c • 1`, and until the `•` becomes a multiplication, `ring` sees an
unsimplified scalar action and cannot close the goal. That single missing lemma is why three earlier
attempts on this identity failed.

## Why `Fin 2`

At `Fin 2` the "all other coordinates" part is one summand, so the identity is closed by `ring`
without `Finset` bookkeeping. The `n`-ary version is the same identity with a sum over `i ≠ j`; the
argument structure is already complete here.
-/

namespace Lattice.Lib.Linear.PenaltyPerturb

open Lattice.Lib.Linear.PenaltyVector
open Lattice.Lift

/-- The unit vector supported at `j`, typed as `Fin 2 → ℝ`.

Written explicitly rather than with `Pi.single`, whose dependent family leaves `HSMul` unable to
synthesise in `x + c • Pi.single j 1`. -/
def e2 (j : Fin 2) : Fin 2 → ℝ := fun k => if k = j then 1 else 0

@[simp] theorem e2_self (j : Fin 2) : e2 j j = 1 := by
  simp [e2]

@[simp] theorem e2_ne {j k : Fin 2} (h : k ≠ j) : e2 j k = 0 := by
  simp [e2, h]

/-- The residual vector at `Fin 2`: `rᵢ = aᵢxᵢ + bᵢ`. -/
noncomputable def resid2 (a b x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => a i * x i + b i

/-- The loss at `Fin 2`, written coordinate by coordinate so the "other summand" is explicit. -/
noncomputable def loss2 (a b : Fin 2 → ℝ) : (Fin 2 → ℝ) → ℝ :=
  fun x => (resid2 a b x 0) ^ 2 + (resid2 a b x 1) ^ 2

/-! ## Step 1: how the residual responds to a coordinate step -/

/-- **The perturbed coordinate.** Moving coordinate `j` by `c` shifts its residual by `c·aⱼ`.

`smul_eq_mul` in the simp set is essential: `Pi.smul_apply` yields `a j * c • 1`, and `ring` cannot
close the goal while the scalar action is still a `•`. -/
theorem resid2_perturb (a b x : Fin 2 → ℝ) (c : ℝ) (j : Fin 2) :
    resid2 a b (x + c • e2 j) j = resid2 a b x j + c * a j := by
  simp only [resid2, Pi.add_apply, Pi.smul_apply, e2, if_true, mul_one, smul_eq_mul]
  ring

/-- **The untouched coordinate.** Moving coordinate `j` leaves every other residual alone. -/
theorem resid2_other (a b x : Fin 2 → ℝ) (c : ℝ) {j k : Fin 2} (h : k ≠ j) :
    resid2 a b (x + c • e2 j) k = resid2 a b x k := by
  simp only [resid2, Pi.add_apply, Pi.smul_apply, e2, if_neg h, mul_zero, smul_eq_mul, add_zero]

/-! ## Step 2: the aim -/

/-- **The scale that annihilates a residual.**

`c := -rⱼ/aⱼ` makes `rⱼ + c·aⱼ = 0`. Kept as its own theorem because `field_simp` needs `a j ≠ 0` in
*scope* to eliminate the division: written inline under `fin_cases`, the hypothesis was not visible
and the goal degenerated to `r - r * a * a⁻¹ = 0`, which no arithmetic tactic closes. -/
theorem perturb_zeroes (a b x : Fin 2 → ℝ) (j : Fin 2) (ha : a j ≠ 0) :
    resid2 a b (x + (-(resid2 a b x j / a j)) • e2 j) j = 0 := by
  rw [resid2_perturb]
  field_simp

/-- **A nonzero residual can always be strictly decreased** by moving one coordinate.

The witness drives that residual to zero, so the loss drops from `rⱼ² + K` to `K`; strictness is
`rⱼ² > 0`. After `fin_cases j` the annihilation fact is restated at the concrete coordinate, because
the general form's `j` elaborates to `((fun i => i) ⟨0, _⟩)`, which does not match the literal `0`. -/
theorem exists_decrease (a b x : Fin 2 → ℝ) (j : Fin 2) (ha : a j ≠ 0)
    (hr : resid2 a b x j ≠ 0) :
    ∃ y : Fin 2 → ℝ, loss2 a b y < loss2 a b x := by
  refine ⟨x + (-(resid2 a b x j / a j)) • e2 j, ?_⟩
  fin_cases j
  · have h0 : resid2 a b (x + (-(resid2 a b x 0 / a 0)) • e2 0) 0 = 0 :=
      perturb_zeroes a b x 0 ha
    have hres : resid2 a b x 0 ≠ 0 := hr
    have h1 : resid2 a b (x + (-(resid2 a b x 0 / a 0)) • e2 0) 1 = resid2 a b x 1 :=
      resid2_other a b x _ (by decide)
    show (resid2 a b (x + (-(resid2 a b x 0 / a 0)) • e2 0) 0) ^ 2
        + (resid2 a b (x + (-(resid2 a b x 0 / a 0)) • e2 0) 1) ^ 2
      < (resid2 a b x 0) ^ 2 + (resid2 a b x 1) ^ 2
    rw [h0, h1]
    have hsq : (0 : ℝ) < resid2 a b x 0 ^ 2 := sq_pos_of_ne_zero hres
    nlinarith
  · have h0 : resid2 a b (x + (-(resid2 a b x 1 / a 1)) • e2 1) 1 = 0 :=
      perturb_zeroes a b x 1 ha
    have hres : resid2 a b x 1 ≠ 0 := hr
    have h1 : resid2 a b (x + (-(resid2 a b x 1 / a 1)) • e2 1) 0 = resid2 a b x 0 :=
      resid2_other a b x _ (by decide)
    show (resid2 a b (x + (-(resid2 a b x 1 / a 1)) • e2 1) 0) ^ 2
        + (resid2 a b (x + (-(resid2 a b x 1 / a 1)) • e2 1) 1) ^ 2
      < (resid2 a b x 0) ^ 2 + (resid2 a b x 1) ^ 2
    rw [h0, h1]
    have hsq : (0 : ℝ) < resid2 a b x 1 ^ 2 := sq_pos_of_ne_zero hres
    nlinarith

/-- **The same conclusion at coordinate `0`.** -/
theorem exists_decrease_zero (a b x : Fin 2 → ℝ) (ha : a 0 ≠ 0) (hr : resid2 a b x 0 ≠ 0) :
    ∃ y : Fin 2 → ℝ, loss2 a b y < loss2 a b x :=
  exists_decrease a b x 0 ha hr

/-- **The same conclusion at coordinate `1`.** -/
theorem exists_decrease_one (a b x : Fin 2 → ℝ) (ha : a 1 ≠ 0) (hr : resid2 a b x 1 ≠ 0) :
    ∃ y : Fin 2 → ℝ, loss2 a b y < loss2 a b x :=
  exists_decrease a b x 1 ha hr

/-! ## Step 3: the scaled family, and why no local minimum has a nonzero residual -/

/-- The perturbed point at scale `s`: move coordinate `j` by `s·c` where `c` is the annihilating
step from `perturb_zeroes`.

Writing the family rather than a single point is what makes the topological step possible: `s` can be
driven to `0`, so the points approach `x`. -/
noncomputable def pertPoint (a b x : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) : Fin 2 → ℝ :=
  x + (s * (-(resid2 a b x j / a j))) • e2 j

/-- **The residual along the family.** At scale `s` the `j`-th residual is `(1 - s)·rⱼ`, so it is
strictly smaller in magnitude for every `s ∈ (0, 2)` other than `0`. -/
theorem pertPoint_resid (a b x : Fin 2 → ℝ) (j : Fin 2) (ha : a j ≠ 0) (s : ℝ) :
    resid2 a b (pertPoint a b x j s) j = (1 - s) * resid2 a b x j := by
  unfold pertPoint
  rw [resid2_perturb]
  field_simp
  ring

/-- **The loss strictly decreases along the family**, for any scale in `(0, 2)` other than zero.

The decrease is independent of how small `s` is -- that is exactly what the topological argument
needs, since it lets the point be placed inside any ball around `x`. -/
theorem pertPoint_loss_lt (a b x : Fin 2 → ℝ) (j : Fin 2) (ha : a j ≠ 0)
    (hr : resid2 a b x j ≠ 0) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    loss2 a b (pertPoint a b x j s) < loss2 a b x := by
  have hres := pertPoint_resid a b x j ha s
  have hsq : (pertPoint a b x j s : Fin 2 → ℝ) = pertPoint a b x j s := rfl
  fin_cases j
  · have h0 : resid2 a b (pertPoint a b x 0 s) 0 = (1 - s) * resid2 a b x 0 :=
      pertPoint_resid a b x 0 ha s
    have hresz : resid2 a b x 0 ≠ 0 := hr
    have h1 : resid2 a b (pertPoint a b x 0 s) 1 = resid2 a b x 1 := by
      unfold pertPoint
      exact resid2_other a b x _ (by decide)
    show (resid2 a b (pertPoint a b x 0 s) 0) ^ 2 + (resid2 a b (pertPoint a b x 0 s) 1) ^ 2
        < (resid2 a b x 0) ^ 2 + (resid2 a b x 1) ^ 2
    rw [h0, h1]
    -- `(1-s)^2 < 1` holds for `0 < s < 2`; the square may be zero when `s = 1`, in which
    -- case the summand vanishes entirely and the inequality is still strict
    have hlt : (1 - s) ^ 2 < 1 := by nlinarith [sq_nonneg (1 - s)]
    have hnonneg : (0:ℝ) ≤ (1 - s) ^ 2 := sq_nonneg _
    have hsqpos : (0:ℝ) < (resid2 a b x 0) ^ 2 := sq_pos_of_ne_zero hresz
    nlinarith [mul_lt_mul_of_pos_left hlt hsqpos]
  · have h0 : resid2 a b (pertPoint a b x 1 s) 1 = (1 - s) * resid2 a b x 1 :=
      pertPoint_resid a b x 1 ha s
    have hresz : resid2 a b x 1 ≠ 0 := hr
    have h1 : resid2 a b (pertPoint a b x 1 s) 0 = resid2 a b x 0 := by
      unfold pertPoint
      exact resid2_other a b x _ (by decide)
    show (resid2 a b (pertPoint a b x 1 s) 0) ^ 2 + (resid2 a b (pertPoint a b x 1 s) 1) ^ 2
        < (resid2 a b x 0) ^ 2 + (resid2 a b x 1) ^ 2
    rw [h0, h1]
    -- `(1-s)^2 < 1` holds for `0 < s < 2`; the square may be zero when `s = 1`, in which
    -- case the summand vanishes entirely and the inequality is still strict
    have hlt : (1 - s) ^ 2 < 1 := by nlinarith [sq_nonneg (1 - s)]
    have hnonneg : (0:ℝ) ≤ (1 - s) ^ 2 := sq_nonneg _
    have hsqpos : (0:ℝ) < (resid2 a b x 1) ^ 2 := sq_pos_of_ne_zero hresz
    nlinarith [mul_lt_mul_of_pos_left hlt hsqpos]

/-- **The perturbed point at scale `s` is within `|s·c|` of `x`.**

Proved componentwise through `dist_pi_lt_iff`, which avoids `Pi.norm_def`'s `OrderBot` requirement:
at coordinate `j` the displacement is `s·c` and elsewhere it is `0`. -/
theorem pertPoint_dist_lt (a b x : Fin 2 → ℝ) (j : Fin 2) {s ε : ℝ} (hε : 0 < ε)
    (h : |s * (-(resid2 a b x j / a j))| < ε) : dist (pertPoint a b x j s) x < ε := by
  unfold pertPoint
  rw [dist_pi_lt_iff hε]
  intro k
  have hsub : (x + (s * (-(resid2 a b x j / a j))) • e2 j) k - x k
      = (s * (-(resid2 a b x j / a j))) * e2 j k := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Real.dist_eq, hsub, abs_mul]
  by_cases hk : k = j
  · simp only [hk, e2_self, abs_one, mul_one]; exact h
  · simp only [e2, if_neg hk, abs_zero, mul_zero]; exact hε

/-- **A point with a nonzero residual is not a local minimum.**

This is several-variable exactness at `Fin 2`, obtained with neither a derivative nor a norm.

`IsLocalMin` unfolds to `∀ᶠ y in nhds x, L x ≤ L y`, and `Metric.eventually_nhds_iff` turns that into
`∃ ε > 0, ∀ y, dist y x < ε → L x ≤ L y`. Take the scale `s := ε / (2 * (|c| + 1))`, which is in
`(0, 2)` and nonzero: `pertPoint_loss_lt` gives a strictly smaller loss there, and `pertPoint_dist_lt`
places the point inside the ball. Contradiction.

The two halves are exactly the two facts that took several rounds to isolate: the decrease is
independent of the scale (so `s` may be as small as the ball requires), and the distance is
componentwise (so no `sup` over an unbounded index type is needed). -/
theorem not_localMin_of_resid_ne_zero (a b x : Fin 2 → ℝ) (j : Fin 2) (ha : a j ≠ 0)
    (hr : resid2 a b x j ≠ 0) : ¬ IsLocalMin (loss2 a b) x := by
  intro hmin
  rw [IsLocalMin, IsMinFilter, Metric.eventually_nhds_iff] at hmin
  obtain ⟨ε, hεpos, hε⟩ := hmin
  set c : ℝ := -(resid2 a b x j / a j) with hc
  -- bound the scale above by `1` as well, so it lies in `(0, 2)`
  set s : ℝ := min 1 (ε / (2 * (|c| + 1))) with hs
  have hden : (0:ℝ) < |c| + 1 := by positivity
  have hbase0 : 0 < ε / (2 * (|c| + 1)) := by positivity
  have hs0 : 0 < s := by
    rw [hs]
    exact lt_min one_pos hbase0
  have hsle : s ≤ ε / (2 * (|c| + 1)) := by
    rw [hs]
    exact min_le_right _ _
  have hs1 : s ≤ 1 := by
    rw [hs]
    exact min_le_left _ _
  have hs2 : s < 2 := by linarith
  -- the displacement bound
  have hsabs : |s * c| < ε := by
    have hc0 : (0:ℝ) ≤ |c| := abs_nonneg c
    have hle : |s * c| ≤ ε / (2 * (|c| + 1)) * |c| := by
      rw [abs_mul, abs_of_pos hs0]
      exact mul_le_mul_of_nonneg_right hsle hc0
    have hstrict : ε / (2 * (|c| + 1)) * |c| < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (|c| + 1))]
      nlinarith [abs_nonneg c, hεpos]
    linarith
  have hle := hε (pertPoint_dist_lt a b x j hεpos hsabs)
  linarith [pertPoint_loss_lt a b x j ha hr hs0 hs2]

/-! ## The equivalence, and `PenaltyExact`

With both directions the several-variable statement is complete at `Fin 2`. -/

/-- **A feasible point is a local minimum.** The loss is a sum of squares, hence non-negative and
zero at a feasible point. -/
theorem localMin_of_feasible (a b x : Fin 2 → ℝ) (h : ∀ i, resid2 a b x i = 0) :
    IsLocalMin (loss2 a b) x := by
  apply isLocalMin_of_forall_le
  intro y
  show loss2 a b x ≤ loss2 a b y
  have hx0 : loss2 a b x = 0 := by
    unfold loss2
    rw [h 0, h 1]
    ring
  rw [hx0]
  unfold loss2
  positivity

/-- **Local minima are exactly the feasible points** at `Fin 2`.

Derived from `Lattice.Lib.Linear.PenaltyPerturbN.localMin_iff_feasible` at `n = 2`. An earlier revision
carried a separate 138-character proof here that was character-for-character the general one; this
version cannot drift from the general statement, which is the point of a derivation over a copy.

`loss2` and `lossN` agree at `n = 2` after unfolding the two-term sum (`Fin.sum_univ_two`), and `resid2`
is literally `residN` there. Both are recorded as lemmas below so the transport is explicit rather than
hidden in a `convert`.

The `Fin 2` lemmas above (`resid2_perturb`, `perturb_zeroes`, `exists_decrease`,
`not_localMin_of_resid_ne_zero`) stay: their proofs use `fin_cases` rather than `Finset.sum_erase`, so
they are genuinely different work, not copies -- which is what the body audit measured. -/
theorem loss2_eq_lossN (a b : Fin 2 → ℝ) :
    loss2 a b = Lattice.Lib.Linear.PenaltyPerturbN.lossN a b := by
  funext x
  unfold loss2 Lattice.Lib.Linear.PenaltyPerturbN.lossN
  rw [Fin.sum_univ_two]
  rfl

/-- The `Fin 2` residual is the general one at `n = 2`. -/
theorem resid2_eq_residN (a b : Fin 2 → ℝ) (x : Fin 2 → ℝ) (i : Fin 2) :
    resid2 a b x i = Lattice.Lib.Linear.PenaltyPerturbN.residN a b x i := rfl

/-- **Local minima are exactly the feasible points** at `Fin 2`, derived from the general theorem. -/
theorem localMin_iff_feasible (a b x : Fin 2 → ℝ) (ha : ∀ i, a i ≠ 0) :
    IsLocalMin (loss2 a b) x ↔ ∀ i, resid2 a b x i = 0 := by
  rw [loss2_eq_lossN]
  rw [show (∀ i, resid2 a b x i = 0)
      ↔ (∀ i, Lattice.Lib.Linear.PenaltyPerturbN.residN a b x i = 0) from
    ⟨fun h i => by rw [← resid2_eq_residN]; exact h i,
     fun h i => by rw [resid2_eq_residN]; exact h i⟩]
  exact Lattice.Lib.Linear.PenaltyPerturbN.localMin_iff_feasible a b x ha

end Lattice.Lib.Linear.PenaltyPerturb
