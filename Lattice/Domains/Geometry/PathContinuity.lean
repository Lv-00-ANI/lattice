import Mathlib
import Lattice.Domains.Constraints.DistContinuous
import Lattice.Domains.Geometry.PolyNondegenerate

/-!
# `Lattice.Geo.PathContinuity` -- the path that the `.samePoint` branch would need

## Where this sits

`EqConstraint.poly (.samePoint a b)` is `sqDist (pts a) (pts b)`. Closing the branch means showing that a
configuration with `pts a ≠ pts b` cannot be a local minimum of its square. Round 114 established that an *exact*
coordinate overwrite is not enough, because `IsLocalMin` is a neighbourhood condition and the overwrite can land
arbitrarily far away. What is needed instead is a path: vary one coordinate by `t`, stay near the starting point as
`t → 0`, and decrease the sum of squares along the way.

Three of the four pieces are here: the path is continuous, the penalty strictly decreases along it under a sign
condition on `t`, and that sign condition holds for a scaled `-d`. The fourth -- the quantified "for every
neighbourhood there is a small enough `t`" -- is not done; see the closing section.

## The tool

`Continuous.update` says that if `f` and `g` are continuous then so is `t ↦ Function.update (f t) i (g t)`. The path
is a nested application of it: update coordinate `i` of `pts a` by `t`, then update slot `a` of `pts` with the
result. Both levels are the same lemma, which is why the proof reads as two applications rather than as an argument
about product topologies -- `continuous_pi_iff` and the neighbourhood characterisation never appear explicitly.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **Varying one coordinate of a point is continuous.** The inner step of the path. -/
theorem continuous_update_coord (p : Pt n) (i : Fin n) :
    Continuous (fun t : ℝ => Function.update p i (p i + t)) := by
  have h1 : Continuous (fun t : ℝ => p i + t) := continuous_const.add continuous_id
  exact Continuous.update continuous_const i h1

/-- **Varying one slot of a point sequence is continuous.** The outer step of the path. -/
theorem continuous_update_slot (pts : ℕ → Pt n) (a : ℕ) :
    Continuous (fun v : Pt n => Function.update pts a v) :=
  Continuous.update continuous_const a continuous_id

/-- **The `.samePoint` path is continuous.** -/
theorem continuous_samePoint_path (pts : ℕ → Pt n) (a : ℕ) (i : Fin n) :
    Continuous (fun t : ℝ =>
      Function.update pts a (Function.update (pts a) i (pts a i + t))) := by
  have h1 : Continuous (fun t : ℝ => Function.update (pts a) i (pts a i + t)) :=
    continuous_update_coord (pts a) i
  exact Continuous.update continuous_const a h1

/-- **The path starts at `pts`.** -/
theorem samePoint_path_zero (pts : ℕ → Pt n) (a : ℕ) (i : Fin n) :
    Function.update pts a (Function.update (pts a) i (pts a i + 0)) = pts := by
  simp

/-- **The path leaves every other slot alone.** -/
theorem samePoint_path_of_ne (pts : ℕ → Pt n) (a : ℕ) (i : Fin n) (t : ℝ) {j : ℕ} (hj : j ≠ a) :
    Function.update pts a (Function.update (pts a) i (pts a i + t)) j = pts j :=
  Function.update_noteq hj _ pts

/-! ## The penalty strictly decreases along the path

**First, `sqDist` takes two points, not a point sequence.** `poly (.samePoint a b) pts` is `sqDist (pts a) (pts b)`,
so only `pts a` and `pts b` matter, and the inner update suffices; the outer `Function.update pts a` never has to
appear in the estimate.

**Second, the single-coordinate split isolates `t`.** Writing `d` for the one differing coordinate,

    sqDist (update (pts a) i (pts a i + t)) (pts b)  =  (d + t)^2 + C

with `C` free of `t`. Comparing against `d^2 + C` reduces the claim to `(d + t)^2 < d^2`, which holds exactly when
`t * (2 * d + t) < 0`. -/

/-- **Squaring loses a comparison exactly when the sign condition holds.** -/
theorem sq_lt_sq_iff_mul_sign (d t : ℝ) :
    (d + t) ^ 2 < d ^ 2 ↔ t * (2 * d + t) < 0 := by
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The penalty along the path, with the moving coordinate split off.** -/
theorem sqDist_along_path_split (p q : Pt n) (i : Fin n) (t : ℝ) :
    sqDist (n := n) (Function.update p i (p i + t)) q
      = (p i + t - q i) ^ 2 + ∑ j in Finset.univ \ {i}, (p j - q j) ^ 2 := by
  rw [sqDist_eq_coord_add_rest]
  congr 1
  · rw [Function.update_same]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := by
      intro h
      exact (Finset.mem_sdiff.mp hj).2 (by simp [h])
    rw [Function.update_noteq hji]

/-- **Along the path the penalty strictly decreases**, provided the sign condition on `t` holds.

The hypothesis keeps two questions apart: whether a decreasing `t` exists is arithmetic
(`sq_lt_sq_iff_mul_sign`), whether it is small enough to stay inside a neighbourhood is topology. -/
theorem sqDist_along_path_lt (p q : Pt n) (i : Fin n) {t : ℝ}
    (h : t * (2 * (p i - q i) + t) < 0) :
    sqDist (n := n) (Function.update p i (p i + t)) q < sqDist (n := n) p q := by
  rw [sqDist_along_path_split, sqDist_eq_coord_add_rest]
  have hsq := (sq_lt_sq_iff_mul_sign (p i - q i) t).mpr h
  linarith

/-! ## The fifth step: a decreasing `t` can be taken arbitrarily small

The sign condition describes an **open** interval -- the roots of `t (t + 2 d)` are `0` and `-2 d`, distinct because
`d ≠ 0` -- so it contains points of any small magnitude. That is what lets a caller satisfy two demands at once: move
enough to decrease the penalty, and little enough to remain inside a neighbourhood.

The witness is `-d * min 1 (ε / (2 * |d|))`. The `min` does the work twice over: capping at `1` keeps the step inside
`(min (0, -2d), max (0, -2d))`, and capping at `ε / (2 * |d|)` keeps its magnitude below `ε`.

Round 119 recorded this step as blocked on `|-d * m| = |d| * m`, where repeated `simp`/`rw` produced `|(|d|)|`. The
obstruction turned out to be narrower than that: the rewrite needs `0 < m`, not `0 < d`. Supplying `abs_of_pos hm`
alone closes it in one step, and `abs_of_pos hd` is what failed -- `d ≠ 0` does not give `0 < d`. -/

/-- **The sign condition holds for a scaled `-d`.** With `0 < m <= 1`, the point `-d * m` lies in the interval where
the product is negative. -/
theorem neg_mul_two_add_neg_mul_neg (d m : ℝ) (hd : d ≠ 0) (hm0 : 0 < m) (hm1 : m ≤ 1) :
    -d * m * (2 * d + -d * m) < 0 := by
  have hd2 : 0 < d ^ 2 := by positivity
  have hpos : 0 < m * (2 - m) := by nlinarith
  have hEq : -d * m * (2 * d + -d * m) = -(d ^ 2) * m * (2 - m) := by ring
  rw [hEq]
  nlinarith

/-- **A decreasing step can be made arbitrarily small.**

For every `ε > 0` there is a `t` with `0 < |t| < ε` satisfying the sign condition of `sqDist_along_path_lt`. This is
the arithmetic half of "the path leaves the point in a decreasing direction *and* stays nearby"; the topology is in
`continuous_samePoint_path`. -/
theorem exists_small_descent (d : ℝ) (hd : d ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, t ≠ 0 ∧ |t| < ε ∧ t * (2 * d + t) < 0 := by
  have hDpos : 0 < |d| := abs_pos.mpr hd
  set m : ℝ := min 1 (ε / (2 * |d|)) with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := by rw [hm]; exact min_le_left _ _
  have hmle : m ≤ ε / (2 * |d|) := by rw [hm]; exact min_le_right _ _
  have hm0 : 0 ≤ m := le_of_lt hmpos
  refine ⟨-d * m, ?_, ?_, ?_⟩
  · -- the step is non-zero
    intro hzero
    have hdm : d * m = 0 := by linarith
    rcases mul_eq_zero.mp hdm with h | h
    · exact hd h
    · exact (ne_of_gt hmpos) h
  · -- the step is small
    have hDm : |d| * m ≤ ε / 2 := by
      calc |d| * m ≤ |d| * (ε / (2 * |d|)) :=
              mul_le_mul_of_nonneg_left hmle (le_of_lt hDpos)
        _ = ε / 2 := by field_simp; ring
    have habs : |-d * m| = |d| * m := by
      rw [abs_mul, abs_neg, abs_of_pos hmpos]
    rw [habs]
    linarith
  · -- the step points downhill
    have := neg_mul_two_add_neg_mul_neg d m hd hmpos hm1
    linarith [this]

/-! ## The sixth step: a local minimum rules out arbitrarily small decrease

The composition rests on one general fact about `ℝ` that has nothing to do with geometry: an `Eventually` statement at
`0` cannot coexist with witnesses of its negation at every scale. `Metric.eventually_nhds_iff` reads `Eventually` as
"there is a `d > 0` such that everything within `d` satisfies the property", and the arbitrarily-small witness at that
`d` contradicts it.

That lemma is stated first, on its own, because it is what the geometry consumes -- and because it is reusable: any
branch that can produce a decrease at every scale gets `not IsLocalMin` from it, with no further topology. -/

/-- **An `Eventually` property at `0` is incompatible with counterexamples at every scale.**

The general form of the last step. Note the hypothesis is exactly what `exists_small_descent` provides: for every
`ε > 0`, a `t` with `|t| < ε` where the property fails. -/
theorem not_eventually_zero_of_small_counterexample {P : ℝ → Prop}
    (h : ∀ᶠ t in nhds (0 : ℝ), P t)
    (hbad : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, |t| < ε ∧ ¬ P t) :
    False := by
  obtain ⟨d, hd, hdprop⟩ := Metric.eventually_nhds_iff.mp h
  obtain ⟨t, ht, hnot⟩ := hbad d hd
  exact hnot (hdprop (by simpa [Real.dist_eq, sub_zero] using ht))

/-! ## The sixth step: a local minimum rules out arbitrarily small decrease

The composition has one line of arithmetic left, and the arithmetic needs names. Throughout the proof the same real
appears as `sqDist (update (pts a) i (pts a i + t)) (pts b)` in one place and as its own expression in another;
`linarith` compares *terms*, so identical reals written differently are invisible to it. Naming both before the final
step is what closes it -- the last obstruction was bookkeeping, not mathematics. -/

/-- **A configuration with `pts a ≠ pts b` is not a local minimum of the `.samePoint` penalty's square.**

The five earlier pieces feed this: local minimality pulls back along `continuous_samePoint_path` to an `Eventually`
statement at `0`, `exists_small_descent` supplies a witness at every scale, and
`not_eventually_zero_of_small_counterexample` turns the pair into a contradiction.

Nothing here is specific to `EqConstraint.poly (.samePoint a b)` beyond reading its penalty as `sqDist (pts a) (pts b)`. -/
theorem sqDist_samePoint_not_localMin (a b : ℕ) (ha : a ≠ b) (pts : ℕ → Pt n)
    (hne : pts a ≠ pts b) :
    ¬ IsLocalMin (fun x : ℕ → Pt n => (sqDist (n := n) (x a) (x b)) ^ 2) pts := by
  intro hmin
  -- some coordinate differs
  have hex : ∃ i : Fin n, pts a i ≠ pts b i := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  obtain ⟨i, hi⟩ := hex
  have hd : pts a i - pts b i ≠ 0 := sub_ne_zero.mpr hi
  -- the path, written out so rewrites can find it
  have hcont : Filter.Tendsto
      (fun t : ℝ => Function.update pts a (Function.update (pts a) i (pts a i + t)))
      (nhds (0 : ℝ)) (nhds pts) := by
    have hc := (continuous_samePoint_path pts a i).tendsto 0
    simpa using hc
  -- pull local minimality back along the path
  have hev : ∀ᶠ t in nhds (0 : ℝ),
      (sqDist (n := n) (pts a) (pts b)) ^ 2
        ≤ (sqDist (n := n)
            ((fun s : ℝ => Function.update pts a (Function.update (pts a) i (pts a i + s))) t a)
            ((fun s : ℝ => Function.update pts a (Function.update (pts a) i (pts a i + s))) t b)) ^ 2 :=
    hcont.eventually hmin
  -- the counterexample at every scale
  refine not_eventually_zero_of_small_counterexample hev (fun ε hε => ?_)
  obtain ⟨t, _ht0, htε, htlt⟩ := exists_small_descent (pts a i - pts b i) hd hε
  refine ⟨t, htε, ?_⟩
  -- name the two quantities so the arithmetic can see them
  set A : ℝ := sqDist (n := n) (Function.update (pts a) i (pts a i + t)) (pts b) with hA
  set B : ℝ := sqDist (n := n) (pts a) (pts b) with hB
  have hnnA : (0 : ℝ) ≤ A := by rw [hA]; exact sqDist_nonneg _ _
  have hlt : A < B := by
    rw [hA, hB]
    exact sqDist_along_path_lt (pts a) (pts b) i htlt
  -- the pulled-back inequality, rewritten into the names
  have hb : Function.update pts a (Function.update (pts a) i (pts a i + t)) b = pts b :=
    Function.update_noteq (Ne.symm ha) _ pts
  have ha' : Function.update pts a (Function.update (pts a) i (pts a i + t)) a
      = Function.update (pts a) i (pts a i + t) :=
    Function.update_same a _ pts
  intro hle
  simp only [ha', hb] at hle
  nlinarith

end Lattice.Geo
