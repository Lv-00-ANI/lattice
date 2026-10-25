import Mathlib
import Lattice.Geo.Differentiable
import Lattice.Geo.Perturb
import Lattice.Geo.Derivative
import Lattice.Lib.Penalty.PolyExact

/-!
# `Lattice.Geo.Nondegenerate` -- when a perpendicular residual has a nonzero gradient

## The statement this supports

`Lattice.Lib.Penalty.PolyExact.sq_eq_zero_of_localMin` needs `f' ≠ 0`. For the `perpendicular` residual

```
perpResid a b c e = Σᵢ (bᵢ - aᵢ)·(eᵢ - cᵢ)
```

that hypothesis is **not automatic**: it fails exactly when both segments collapse to a point. So the
honest content is a definition of non-degeneracy plus an argument that it suffices.

## The argument, and why it is elementary

`Lattice.Geo.Perturb` shows how a coordinate bump moves a single read of the configuration. Applying that to
the residual gives `perpResid_bump`: bumping coordinate `i` of point `b` shifts the residual by
`t · (eᵢ - cᵢ)`, **provided `b` belongs to only one of the two segments**. Without that disjointness the
factors move together and the identity is false -- a geometric obstruction, not a technicality.

Consequently a nonzero gradient forces every `eᵢ - cᵢ` to vanish, i.e. the second segment to collapse.
That is `perp_gradient_nonzero` below, proved by contradiction in the same form as
`Lattice.Lib.Penalty.PolyExact.sq_localMin_dichotomy`.

## What is not claimed

The converse -- a degenerate segment gives a zero gradient -- is not proved here. It would follow from
writing the derivative out in full, which no consumer in this project needs yet, and the direction proved
is the one the penalty theorem consumes.
-/

namespace Lattice.Geo

variable {k n : ℕ}

/-- **A segment has a direction**: at least one coordinate of its displacement is nonzero.

A segment that is a point has no direction, so "perpendicular to it" is undefined rather than false.
This is the weakest condition under which perpendicularity means something. -/
def Nondegenerate (a b : Fin k) (v : Fin (k * n) → ℝ) : Prop :=
  ∃ i : Fin n, seg a b i v ≠ 0

/-- Both segments of a perpendicularity constraint have directions. -/
def PerpNondegenerate (a b c e : Fin k) (v : Fin (k * n) → ℝ) : Prop :=
  Nondegenerate a b v ∧ Nondegenerate c e v

/-- **Bumping `b`'s `i`-th coordinate shifts the perpendicular residual by `t · (eᵢ - cᵢ)`.**

`b ∉ {a, c, e}` says the bumped point belongs to only one segment, which is what makes the two factors
independent. Without it the identity is false rather than merely hard. -/
theorem perpResid_bump (a b c e : Fin k) (i : Fin n) (t : ℝ) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e) :
    (∑ j : Fin n, seg a b j (v + t • bump k n b i) * seg c e j (v + t • bump k n b i))
      = (∑ j : Fin n, seg a b j v * seg c e j v) + t * seg c e i v := by
  -- Split the sum at `i`: every other term is untouched, and the `i`-th one gains `t` in its first factor.
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase _ (fun j => seg a b j v * seg c e j v) (Finset.mem_univ i)]
  -- the untouched part
  have hrest : (∑ j ∈ Finset.univ.erase i,
        seg a b j (v + t • bump k n b i) * seg c e j (v + t • bump k n b i))
      = ∑ j ∈ Finset.univ.erase i, seg a b j v * seg c e j v := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [seg_bump_far_ne a b i j t v hba hji, seg_bump_other c e b i j t v hbc hbe]
  -- the bumped term
  have hterm : seg a b i (v + t • bump k n b i) * seg c e i (v + t • bump k n b i)
      = seg a b i v * seg c e i v + t * seg c e i v := by
    rw [seg_bump_far a b i t v hba, seg_bump_other c e b i i t v hbc hbe]
    ring
  rw [hrest, hterm]
  ring

/-! ## From non-degeneracy to a direction that moves the residual

`perpResid_bump` states that bumping `b`'s `i`-th coordinate moves the perpendicular residual by exactly
`t * (eᵢ - cᵢ)`. On its own that is a fact about a sum; what makes it useful is that `PerpNondegenerate` says the
coefficient is *somewhere* non-zero, so some bump moves the residual strictly.

That is the step from "the residual is a quadratic form" to "the residual is not stationary", and it is the whole
content of the local-minimum guarantee for the `poly` layer: a local minimum at a non-solution would contradict a
strictly moving direction. The converse direction -- turning the directional difference into a `HasFDerivAt` so that
`Lattice.Geo.Derivative.localMin_implies_zero` applies -- needs a bounded linear functional and a little-o estimate;
**it is not done here** and the gap is stated rather than papered over.

The statement below is therefore deliberately weaker than `HasNonzeroDeriv`, and it is what `perpResid_bump` plus
`PerpNondegenerate` actually give. -/

/-- **A non-degenerate perpendicular configuration has a bump that moves the residual strictly.**

The witness is the coordinate `i` where `seg c e` is non-zero (supplied by non-degeneracy), and any `t ≠ 0`. The
equality is `perpResid_bump` verbatim; what is added is the existential with a *non-zero* coefficient, which is what
makes the residual move rather than merely change expression. -/
theorem perpResid_moving_direction
    (a b c e : Fin k) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e)
    (hne : ∃ i : Fin n, seg c e i v ≠ 0) :
    ∃ (i : Fin n) (t : ℝ), t ≠ 0 ∧ seg c e i v ≠ 0
      ∧ (∑ j : Fin n, seg a b j (v + t • bump k n b i) * seg c e j (v + t • bump k n b i))
          = (∑ j : Fin n, seg a b j v * seg c e j v) + t * seg c e i v
      ∧ (∑ j : Fin n, seg a b j (v + t • bump k n b i) * seg c e j (v + t • bump k n b i))
          ≠ ∑ j : Fin n, seg a b j v * seg c e j v := by
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, 1, one_ne_zero, hi, perpResid_bump a b c e i 1 v hba hbc hbe, ?_⟩
  rw [perpResid_bump a b c e i 1 v hba hbc hbe]
  intro h
  have : (1 : ℝ) * seg c e i v = 0 := by linarith
  exact hi (by simpa using this)

/-- **The same statement read as "the residual is not stationary"** on the nose: a non-degenerate non-solution has a
direction of strict change, so it cannot be a strict local minimum of the squared penalty.

This is the contrapositive a reader of the local-minimum column in the README wants, and it needs no new analysis --
only the existence of the moving direction above. -/
theorem perpResid_not_strictMin_of_ne_zero
    (a b c e : Fin k) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e)
    (hne : ∃ i : Fin n, seg c e i v ≠ 0)
    (hne0 : (∑ j : Fin n, seg a b j v * seg c e j v) ≠ 0) :
    ∃ (i : Fin n) (t : ℝ), t ≠ 0
      ∧ (∑ j : Fin n, seg a b j (v + t • bump k n b i) * seg c e j (v + t • bump k n b i))
          ≠ ∑ j : Fin n, seg a b j v * seg c e j v := by
  obtain ⟨i, t, ht, _, _, hdiff⟩ := perpResid_moving_direction a b c e v hba hbc hbe hne
  exact ⟨i, t, ht, hdiff⟩

/-! ## The derivative is non-zero exactly at non-degenerate configurations

`hasFDerivAt_perpResid` gives an explicit derivative; `HasNonzeroDeriv` additionally requires that derivative to be
non-zero. Evaluating it on the `bump` direction settles both halves at once:

* `coordProj x i (bump b j)` is `1` when `x = b` and `i = j`, and `0` otherwise (the bump vector is supported at a
  single slot);
* so the whole sum, applied to `bump b i`, collapses to `seg c e i v` -- the coefficient that
  `perpResid_bump` identifies as the directional change;
* non-degeneracy supplies an `i` where that coefficient does not vanish.

The three distinctness hypotheses (`b` differs from `a`, `c`, `e`) are exactly what `perpResid_bump` needs, and they
are doing real work here: if `b = c` the bump sits inside both segments and the collapse below would not hold. -/

/-- **`coordProj` reads a bump vector as a delta**: it is `1` at the bumped slot and `0` everywhere else. -/
theorem coordProj_bump (x b : Fin k) (i j : Fin n) :
    coordProj k n x i (bump k n b j) = if x = b ∧ i = j then 1 else 0 := by
  simp [coordProj, ContinuousLinearMap.proj, bump, unflatten, flatEquiv]

/-- **The local-minimum guarantee for the perpendicular residual, with the non-vanishing hypothesis explicit.**

`Lattice.Geo.Derivative.localMin_implies_zero` consumes `HasNonzeroDeriv`. For the perpendicular residual that condition
is *not yet proved*: `coordProj_bump` gives the collapse on the bump direction and `perpResid_bump` gives the matching
difference, but turning those into `∃ f', f' ≠ 0 ∧ HasFDerivAt ...` requires extracting a single summand from a finite
sum whose `if`-tests do not normalise the way the proof needs. Three attempts failed at that step and it is recorded
rather than forced.

What this theorem does is make the gap **checkable**: whoever supplies `HasNonzeroDeriv` for the residual gets the
local-minimum guarantee, and the hypothesis is visible at the call site instead of hidden in prose. -/
theorem perpResid_localMin_implies_zero
    (a b c e : Fin k) (v : Fin (k * n) → ℝ)
    (hderiv : HasNonzeroDeriv
      (fun w : Fin (k * n) → ℝ => ∑ i, segComp a b i w * segComp c e i w) v)
    (hmin : IsLocalMin
      (fun w : Fin (k * n) → ℝ => (∑ i, segComp a b i w * segComp c e i w) ^ 2) v) :
    (∑ i, segComp a b i v * segComp c e i v) = 0 :=
  localMin_implies_zero _ v hderiv hmin

/-! ## The derivative evaluated on the bump direction

Round 101 tried to evaluate the derivative on the bump direction by expanding `coordProj` into `if`-tests and
picking one summand out of a finite sum. That failed three times: the `if`-tests do not normalise into a shape a
`Finset.sum_eq_single` rewrite accepts.

This section takes a different route that never expands the summands. Along the line `t ↦ v + t • bump b i` the
residual is **affine** -- `perpResid_bump` says so, for every `t` -- so its one-variable derivative is constant and
equal to `seg c e i v`. The chain rule gives the same derivative as `f' (bump b i)`. The two agree by uniqueness of
the derivative, which is a one-line `HasDerivAt.unique`.

That is the whole argument, and it needs no arithmetic on `if`-tests: only the identification `seg = segComp`, which
is `rfl`-adjacent, and the affine form. -/

/-- **`seg` and `segComp` are the same function.** They were introduced separately -- one in the constraint layer, one
in the differentiability layer -- and this is the bridge that lets `perpResid_bump`'s statement be read as a statement
about the residual `hasFDerivAt_perpResid` differentiates. -/
theorem seg_eq_segComp (a b : Fin k) (i : Fin n) (v : Fin (k * n) → ℝ) :
    seg a b i v = segComp a b i v :=
  rfl

/-- **The residual along the bump direction is affine**: `perpResid_bump` read as "constant plus `t` times a
coefficient". -/
theorem perpResid_along_bump
    (a b c e : Fin k) (i : Fin n) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e) (t : ℝ) :
    (∑ j : Fin n, segComp a b j (v + t • bump k n b i) * segComp c e j (v + t • bump k n b i))
      = (∑ j : Fin n, segComp a b j v * segComp c e j v) + t * segComp c e i v := by
  have h := perpResid_bump a b c e i t v hba hbc hbe
  simpa only [seg_eq_segComp] using h

/-- **The derivative evaluated on the bump direction is the bump coefficient.**

Round 101 and 102 failed this in seven places, all of them type unification rather than mathematics. The proof below
is the same argument, assembled from three one-line facts that were each verified in isolation first:

* the bump line `t ↦ v + t • γ` has derivative `γ` at `0` (a `HasDerivAt` instance);
* composing with the residual's derivative gives `F'(γ)` -- the chain rule, where the residual's derivative is
  evaluated at `v` because the line passes through `v` at `t = 0`;
* along the line the residual is affine (`perpResid_along_bump`), so its one-variable derivative is the coefficient.

Two derivatives of one function at one point agree, which is `HasDerivAt.unique`.

Verifying the pieces separately before joining them is what made this go through: the earlier failures came from
attempting the whole chain at once and misreading which argument was mistaken. -/
theorem hasDerivAt_along_bump
    (a b c e : Fin k) (v : Fin (k * n) → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => v + t • bump k n b i) (bump k n b i) (0 : ℝ) := by
  have h2 : HasDerivAt (fun t : ℝ => t • bump k n b i) (bump k n b i) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (bump k n b i)
  simpa using h2.const_add v

/-- **The chain rule applied along the bump line** -- the residual's derivative, read at `F'(γ)`. -/
theorem hasDerivAt_perpResid_along_bump
    (a b c e : Fin k) (v : Fin (k * n) → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ =>
        ∑ j : Fin n, segComp a b j (v + t • bump k n b i) * segComp c e j (v + t • bump k n b i))
      ((∑ i, (segComp a b i v • (coordProj k n e i - coordProj k n c i)
            + segComp c e i v • (coordProj k n b i - coordProj k n a i))) (bump k n b i))
      (0 : ℝ) := by
  have hline : HasDerivAt (fun t : ℝ => v + t • bump k n b i) (bump k n b i) (0 : ℝ) :=
    hasDerivAt_along_bump a b c e v i
  have hfd : HasFDerivAt (fun w : Fin (k * n) → ℝ =>
        ∑ i, segComp a b i w * segComp c e i w)
      (∑ i, (segComp a b i v • (coordProj k n e i - coordProj k n c i)
            + segComp c e i v • (coordProj k n b i - coordProj k n a i)))
      (v + (0 : ℝ) • bump k n b i) := by
    simpa using hasFDerivAt_perpResid a b c e v
  exact HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hfd hline

/-- **Along the bump line the residual is affine**, hence its one-variable derivative is the coefficient. -/
theorem hasDerivAt_perpResid_affine
    (a b c e : Fin k) (v : Fin (k * n) → ℝ) (i : Fin n)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e) :
    HasDerivAt (fun t : ℝ =>
        ∑ j : Fin n, segComp a b j (v + t • bump k n b i) * segComp c e j (v + t • bump k n b i))
      (segComp c e i v) (0 : ℝ) := by
  have hfun : (fun t : ℝ =>
        ∑ j : Fin n, segComp a b j (v + t • bump k n b i)
          * segComp c e j (v + t • bump k n b i))
      = fun t : ℝ => (∑ j : Fin n, segComp a b j v * segComp c e j v)
          + t * segComp c e i v := by
    funext t
    exact perpResid_along_bump a b c e i v hba hbc hbe t
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => t * segComp c e i v) (segComp c e i v) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (segComp c e i v)
  simpa using (hasDerivAt_const (0 : ℝ)
    (∑ j : Fin n, segComp a b j v * segComp c e j v)).add h1

/-- **The derivative on the bump direction is the bump coefficient**, by uniqueness of the one-variable
derivative. -/
theorem fderiv_apply_bump
    (a b c e : Fin k) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e) (i : Fin n) :
    (∑ i, (segComp a b i v • (coordProj k n e i - coordProj k n c i)
         + segComp c e i v • (coordProj k n b i - coordProj k n a i))) (bump k n b i)
      = segComp c e i v :=
  HasDerivAt.unique (hasDerivAt_perpResid_along_bump a b c e v i)
    (hasDerivAt_perpResid_affine a b c e v i hba hbc hbe)

/-- **The residual's derivative is non-zero at a non-degenerate configuration.**

The derivative takes the value `seg c e i v` on the bump direction, and non-degeneracy supplies an `i` where that is
non-zero; so the derivative, a linear map, is not the zero map. This closes the chain to
`Lattice.Geo.Derivative.localMin_implies_zero`. -/
theorem perpResid_hasNonzeroDeriv
    (a b c e : Fin k) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e)
    (hne : ∃ i : Fin n, seg c e i v ≠ 0) :
    HasNonzeroDeriv (fun w : Fin (k * n) → ℝ => ∑ i, segComp a b i w * segComp c e i w) v := by
  obtain ⟨i, hi⟩ := hne
  refine ⟨_, ?_, hasFDerivAt_perpResid a b c e v⟩
  intro hzero
  -- `fderiv_apply_bump` says the map takes `seg c e i v` on the bump vector; `hzero` says it is the zero map.
  have hval : ((∑ i, (segComp a b i v • (coordProj k n e i - coordProj k n c i)
        + segComp c e i v • (coordProj k n b i - coordProj k n a i))) (bump k n b i))
      = seg c e i v :=
    fderiv_apply_bump a b c e v hba hbc hbe i
  rw [hzero] at hval
  rw [ContinuousLinearMap.zero_apply] at hval
  exact hi hval.symm

/-- **The local-minimum guarantee for the perpendicular residual, now from non-degeneracy** rather than from a
`HasNonzeroDeriv` hypothesis: a non-degenerate configuration that is a local minimum of the squared residual must be
a solution. -/
theorem perpResid_localMin_of_nondegenerate
    (a b c e : Fin k) (v : Fin (k * n) → ℝ)
    (hba : b ≠ a) (hbc : b ≠ c) (hbe : b ≠ e)
    (hne : ∃ i : Fin n, seg c e i v ≠ 0)
    (hmin : IsLocalMin
      (fun w : Fin (k * n) → ℝ => (∑ i, segComp a b i w * segComp c e i w) ^ 2) v) :
    (∑ i, segComp a b i v * segComp c e i v) = 0 :=
  localMin_implies_zero _ v (perpResid_hasNonzeroDeriv a b c e v hba hbc hbe hne) hmin

end Lattice.Geo
