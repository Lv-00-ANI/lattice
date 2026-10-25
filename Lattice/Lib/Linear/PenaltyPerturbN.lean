import Mathlib
import Lattice.Core.Syntax
import Lattice.Lift.PenaltyEmbedding
import Lattice.Lib.Linear.PenaltyVector

/-!
# `Lattice.Lib.Linear.PenaltyPerturbN` -- the penalty in `n` dimensions

## What is new, and what carries over verbatim

`Lattice.Lib.Linear.PenaltyPerturb` proves exactness at `Fin 2` by perturbation. Of its three steps, two
transfer unchanged to any arity:

* **the residual and its response to a coordinate step** -- `residN_perturb` is the same computation
  as at `Fin 2`, with the unit vector generalised;
* **the distance estimate** -- `dist_pi_lt_iff` is already stated for an arbitrary `Fintype`, and the
  componentwise bound is identical.

Only the **loss decomposition** is new: at `Fin 2` the "other coordinates" term is a single summand,
so `fin_cases` exhausted it; at `Fin n` it is `∑ i ∈ univ.erase j`. That is the whole difference, and
`lossN_perturb` records it with `Finset.add_sum_erase`.

## Why the same perturbation works

The step `c := -rⱼ/aⱼ`, scaled by `s`, sends `rⱼ` to `(1 - s)·rⱼ` just as before, so the `j`-th
summand shrinks in magnitude for every `s ∈ (0, 2)` while all others are untouched. The decrease does
not depend on how small `s` is, which is what lets the perturbed point be placed inside any ball
around the candidate minimiser.

## Scope

Widths are `Fin n`. The generic `Fintype` case needs a `DecidableEq` instance for the unit vector and
is not attempted here; `Fin n` is what `PenaltyVector` and the `Loss` instances use.
-/

namespace Lattice.Lib.Linear.PenaltyPerturbN

open Lattice.Lib.Linear.PenaltyVector
open Lattice.Lift

/-- The unit vector supported at `j`.

Written as an explicit `if` rather than with `Pi.single`, whose dependent family leaves `HSMul` unable
to synthesise in `x + c • Pi.single j 1`. -/
noncomputable def unitVec {n : ℕ} (j : Fin n) : Fin n → ℝ := fun k => if k = j then 1 else 0

@[simp] theorem unitVec_self {n : ℕ} (j : Fin n) : unitVec j j = 1 := by
  simp [unitVec]

theorem unitVec_ne {n : ℕ} {j k : Fin n} (h : k ≠ j) : unitVec j k = 0 := by
  simp [unitVec, h]

/-- The residual vector: `rᵢ = aᵢxᵢ + bᵢ`. -/
noncomputable def residN {n : ℕ} (a b x : Fin n → ℝ) : Fin n → ℝ := fun i => a i * x i + b i

/-- The loss: the sum of squared residuals. -/
noncomputable def lossN {n : ℕ} (a b : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (residN a b x i) ^ 2

/-- The perturbed point at scale `s`: coordinate `j` moves by `s·c` with `c := -rⱼ/aⱼ`. -/
noncomputable def pertPointN {n : ℕ} (a b x : Fin n → ℝ) (j : Fin n) (s : ℝ) : Fin n → ℝ :=
  x + (s * (-(residN a b x j / a j))) • unitVec j

/-! ## Step 1: the residual response -/

theorem residN_perturb {n : ℕ} (a b x : Fin n → ℝ) (c : ℝ) (j : Fin n) :
    residN a b (x + c • unitVec j) j = residN a b x j + c * a j := by
  simp only [residN, Pi.add_apply, Pi.smul_apply, unitVec, if_true, mul_one, smul_eq_mul]
  ring

theorem residN_other {n : ℕ} (a b x : Fin n → ℝ) (c : ℝ) {j k : Fin n} (h : k ≠ j) :
    residN a b (x + c • unitVec j) k = residN a b x k := by
  simp only [residN, Pi.add_apply, Pi.smul_apply, unitVec, if_neg h, mul_zero, smul_eq_mul,
    add_zero]

/-! ## Step 2: the loss decomposition -- the only genuinely new step -/

/-- **Perturbing coordinate `j` changes only the `j`-th summand**, and sends it to `(1 - s)·rⱼ`.

At `Fin 2` this was `fin_cases`; here it is `Finset.add_sum_erase`, which splits the sum into the
`j`-th term and a sum over the remaining indices. Those remaining indices are untouched by
`residN_other`, which is why the decomposition is exactly "the `j`-th summand plus a constant". -/
theorem lossN_perturb {n : ℕ} (a b x : Fin n → ℝ) (j : Fin n) (ha : a j ≠ 0) (s : ℝ) :
    lossN a b (pertPointN a b x j s)
      = ((1 - s) * residN a b x j) ^ 2 + ∑ i ∈ Finset.univ.erase j, (residN a b x i) ^ 2 := by
  unfold lossN pertPointN
  -- split the sum into the `j`-th term and the rest
  rw [← Finset.add_sum_erase (Finset.univ)
    (fun i => (residN a b (x + (s * (-(residN a b x j / a j))) • unitVec j) i) ^ 2)
    (Finset.mem_univ j)]
  -- the `j`-th summand becomes `(1 - s)·rⱼ`
  have hj : residN a b (x + (s * (-(residN a b x j / a j))) • unitVec j) j
      = (1 - s) * residN a b x j := by
    rw [residN_perturb]
    field_simp
    ring
  -- the remaining summands are untouched
  have hrest : (∑ i ∈ Finset.univ.erase j,
        (residN a b (x + (s * (-(residN a b x j / a j))) • unitVec j) i) ^ 2)
      = ∑ i ∈ Finset.univ.erase j, (residN a b x i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    congr 1
    exact residN_other (j := j) (k := i) a b x (s * (-(residN a b x j / a j))) hne
  rw [hj, hrest]

/-- The same decomposition stated for the original point, which is what the comparison needs. -/
theorem lossN_eq (a b x : Fin n → ℝ) (j : Fin n) :
    lossN a b x = (residN a b x j) ^ 2 + ∑ i ∈ Finset.univ.erase j, (residN a b x i) ^ 2 := by
  unfold lossN
  rw [← Finset.add_sum_erase (Finset.univ) (fun i => (residN a b x i) ^ 2) (Finset.mem_univ j)]

/-- **The loss strictly decreases along the family**, for any scale in `(0, 2)`.

The comparison reduces to `(1 - s)^2 · rⱼ² < rⱼ²`, the same arithmetic as at `Fin 2`: `(1 - s)^2 < 1`
and `rⱼ² > 0`. The "other coordinates" sum is identical on both sides, so it cancels. -/
theorem lossN_perturb_lt {n : ℕ} (a b x : Fin n → ℝ) (j : Fin n) (ha : a j ≠ 0)
    (hr : residN a b x j ≠ 0) {s : ℝ} (hs0 : 0 < s) (hs2 : s < 2) :
    lossN a b (pertPointN a b x j s) < lossN a b x := by
  rw [lossN_perturb a b x j ha s, lossN_eq a b x j]
  have hlt : (1 - s) ^ 2 < 1 := by nlinarith [sq_nonneg (1 - s)]
  have hsqpos : (0 : ℝ) < (residN a b x j) ^ 2 := sq_pos_of_ne_zero hr
  nlinarith [mul_lt_mul_of_pos_left hlt hsqpos]

/-! ## Step 3: the distance estimate, unchanged in substance -/

/-- **The perturbed point is within `|s·c|` of `x`.**

`dist_pi_lt_iff` is stated for an arbitrary `Fintype`, so the componentwise argument used at `Fin 2`
carries over: the displacement is `s·c` at coordinate `j` and `0` elsewhere. -/
theorem pertPointN_dist_lt {n : ℕ} (a b x : Fin n → ℝ) (j : Fin n) {s ε : ℝ} (hε : 0 < ε)
    (h : |s * (-(residN a b x j / a j))| < ε) : dist (pertPointN a b x j s) x < ε := by
  unfold pertPointN
  rw [dist_pi_lt_iff hε]
  intro k
  have hsub : (x + (s * (-(residN a b x j / a j))) • unitVec j) k - x k
      = (s * (-(residN a b x j / a j))) * unitVec j k := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Real.dist_eq, hsub, abs_mul]
  by_cases hk : k = j
  · simp only [hk, unitVec_self, abs_one, mul_one]; exact h
  · simp only [unitVec, if_neg hk, abs_zero, mul_zero]; exact hε

/-! ## Step 4: no local minimum has a nonzero residual -/

/-- **A point with a nonzero residual is not a local minimum**, at any arity.

`IsLocalMin` unfolds to `∀ᶠ y in nhds x, L x ≤ L y`, which `Metric.eventually_nhds_iff` turns into
`∃ ε > 0, ∀ y, dist y x < ε → L x ≤ L y`. The scale is bounded above by both `1` (so it lies in the
`(0, 2)` range where the loss decreases) and `ε / (2·(|c| + 1))` (so the point stays inside the
ball). Nothing here depends on the arity beyond the two lemmas above. -/
theorem not_localMin_of_resid_ne_zero {n : ℕ} (a b x : Fin n → ℝ) (j : Fin n) (ha : a j ≠ 0)
    (hr : residN a b x j ≠ 0) : ¬ IsLocalMin (lossN a b) x := by
  intro hmin
  rw [IsLocalMin, IsMinFilter, Metric.eventually_nhds_iff] at hmin
  obtain ⟨ε, hεpos, hε⟩ := hmin
  -- the displacement direction, written literally so no `set`/`rw` is needed anywhere
  set d : ℝ := |-(residN a b x j / a j)| with hd
  set s : ℝ := min 1 (ε / (2 * (d + 1))) with hs
  have hbase0 : 0 < ε / (2 * (d + 1)) := by positivity
  have hden : (0:ℝ) < 2 * (d + 1) := by positivity
  have hs0 : 0 < s := by
    rw [hs]; exact lt_min one_pos hbase0
  have hsle : s ≤ ε / (2 * (d + 1)) := by
    rw [hs]; exact min_le_right _ _
  have hs1 : s ≤ 1 := by
    rw [hs]; exact min_le_left _ _
  have hs2 : s < 2 := by linarith
  have hd0 : (0:ℝ) ≤ d := by rw [hd]; exact abs_nonneg _
  have hsabs : |s * (-(residN a b x j / a j))| < ε := by
    have heq : |s * (-(residN a b x j / a j))| = s * d := by
      rw [abs_mul, abs_of_pos hs0, hd, mul_comm]
    rw [heq]
    have hmono : s * d ≤ ε / (2 * (d + 1)) * d :=
      mul_le_mul_of_nonneg_right hsle hd0
    have hstrict : ε / (2 * (d + 1)) * d < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [hεpos, hd0]
    linarith
  have hle := hε (pertPointN_dist_lt a b x j hεpos hsabs)
  have hlt := lossN_perturb_lt a b x j ha hr hs0 hs2
  linarith

/-- **A feasible point is a local minimum**, at any arity: the loss is a sum of squares. -/
theorem localMin_of_feasible {n : ℕ} (a b x : Fin n → ℝ) (h : ∀ i, residN a b x i = 0) :
    IsLocalMin (lossN a b) x := by
  apply isLocalMin_of_forall_le
  intro y
  show lossN a b x ≤ lossN a b y
  have hx0 : lossN a b x = 0 := by
    unfold lossN
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
    intro i _
    rw [h i]; ring
  rw [hx0]
  unfold lossN
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **Local minima are exactly the feasible points**, at any arity and with nonzero slopes. -/
theorem localMin_iff_feasible {n : ℕ} (a b x : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    IsLocalMin (lossN a b) x ↔ ∀ i, residN a b x i = 0 := by
  constructor
  · intro hmin i
    by_contra hne
    exact not_localMin_of_resid_ne_zero a b x i (ha i) hne hmin
  · exact localMin_of_feasible a b x

/-- **`PenaltyExact` holds for the `n`-variable squared-residual penalty.**

This is the `n`-ary form of `PenaltyPerturb.sq_penalty_exact_fin2`: every local minimiser of the loss
satisfies the constraint, with no derivative and no norm anywhere in the proof.

The general *matrix* case remains owed: there `Aᵀ(A x + b) = 0` only forces `A x + b = 0` under a full
rank condition, which is a statement about spans rather than coordinates. -/
theorem sq_penalty_exact_finN {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ i, a i ≠ 0) :
    ∀ x : Fin n → ℝ, IsLocalMin (lossN a b) x → ∀ i, residN a b x i = 0 :=
  fun x h => (localMin_iff_feasible a b x ha).mp h

end Lattice.Lib.Linear.PenaltyPerturbN
