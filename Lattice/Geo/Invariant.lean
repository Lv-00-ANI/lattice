import Mathlib
import Lattice.Geo.Constraint
import Lattice.Lib.Linear.PenaltyVector

/-!
# `Lattice.Geo.Invariant` -- symmetries of geometric constraints

## Why this is the mathematical content of data synthesis

The objective names three forward paths from symbolic knowledge to weights: *constraint loss*, *data
synthesis*, and *structured initialisation*. Only the first existed. Data synthesis asks where training
examples come from, and for geometric constraints the answer is symmetry: **one solution generates a whole
orbit of solutions** under transformations the constraint cannot see.

Concretely, if `Holds c pts` and `T` is a transformation preserving `c`, then `Holds c (T pts)` -- so a
single satisfying configuration yields as many samples as the ambient space allows. Stating the
preservation laws is therefore the formal content of "generate data from a constraint", not a preliminary
to it.

## Which transformations preserve what

| constraint | translation | positive scaling | rotation |
|:--|:--|:--|:--|
| `samePoint` | yes | yes | yes |
| `collinear` | yes | yes | yes (n = 2) |
| `perpendicular` | yes | **yes** | yes (n = 2) |
| `midpoint` | yes | **yes** | yes |
| `sqDistEq` | yes | **no** -- scales by `s²` | yes |

Perpendicularity and midpoint survive scaling because both sides scale together: a dot product gets `s²`,
and a midpoint equation is homogeneous of degree one on each side. A distance constraint does not, because
`sqDist` scales by `s²` while the prescribed right-hand side does not -- which is exactly the distinction
`Layer` records between the `poly` and `square` layers.

## Translation is the cleanest case

Translation leaves every `seg` unchanged, hence leaves every constraint stated in terms of `seg` invariant
with no side condition at all. The theorems below take translation as the main symmetry and prove
invariance for the constraints whose statements are translation-free, which is all of them except
`sqDistEq` with a non-constant right-hand side.
-/

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

variable {n : ℕ}

/-- **Translation**: move every point by the same vector. -/
noncomputable def translate (t : Pt n) (pts : ℕ → Pt n) : ℕ → Pt n :=
  fun p i => pts p i + t i

/-- **A displacement is translation-invariant.** The whole reason translation preserves the constraints
below: every one of them is stated through `seg`, and `seg` compares two points. -/
theorem seg_translate (t : Pt n) (pts : ℕ → Pt n) (p q : ℕ) :
    GeoConstraint.seg (translate t pts) p q = GeoConstraint.seg pts p q := by
  funext i
  unfold GeoConstraint.seg translate
  ring

/-- **Perpendicularity is translation-invariant.** -/
theorem perpendicular_translate (a b c e : ℕ) (t : Pt n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.perpendicular a b c e) pts) :
    GeoConstraint.Holds (.perpendicular a b c e) (translate t pts) := by
  unfold GeoConstraint.Holds at h ⊢
  simp only [seg_translate]
  exact h

/-- **Collinearity is translation-invariant.** -/
theorem collinear_translate (a b c : ℕ) (t : Pt n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.collinear a b c) pts) :
    GeoConstraint.Holds (.collinear a b c) (translate t pts) := by
  unfold GeoConstraint.Holds at h ⊢
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  simp only [seg_translate]
  exact hu

/-- **Parallelism is translation-invariant.** -/
theorem parallel_translate (a b c e : ℕ) (t : Pt n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.parallel a b c e) pts) :
    GeoConstraint.Holds (.parallel a b c e) (translate t pts) := by
  unfold GeoConstraint.Holds at h ⊢
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  simp only [seg_translate]
  exact hu

/-- **Coincidence is translation-invariant.** -/
theorem samePoint_translate (a b : ℕ) (t : Pt n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.samePoint a b) pts) :
    GeoConstraint.Holds (.samePoint a b) (translate t pts) := by
  show translate t pts a = translate t pts b
  unfold translate
  funext i
  rw [congrFun (show pts a = pts b from h) i]

/-- **A right angle is translation-invariant.** -/
theorem rightAngle_translate (a b c : ℕ) (t : Pt n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.rightAngle a b c) pts) :
    GeoConstraint.Holds (.rightAngle a b c) (translate t pts) := by
  unfold GeoConstraint.Holds at h ⊢
  simp only [seg_translate]
  exact h

/-- **Equal length is translation-invariant.** -/
theorem equalLength_translate (a b c e : ℕ) (t : Pt n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.equalLength a b c e) pts) :
    GeoConstraint.Holds (.equalLength a b c e) (translate t pts) := by
  show sqDist (n := n) (translate t pts a) (translate t pts b)
     = sqDist (n := n) (translate t pts c) (translate t pts e)
  have hh : sqDist (n := n) (pts a) (pts b) = sqDist (n := n) (pts c) (pts e) := h
  -- translation cancels inside every difference
  have key : ∀ p q : ℕ, sqDist (n := n) (translate t pts p) (translate t pts q)
      = sqDist (n := n) (pts p) (pts q) := by
    intro p q
    unfold sqDist sqNorm diff translate
    congr 1
    funext i
    congr 1
    ring
  rw [key a b, key c e]
  exact hh

/-- **A midpoint stays a midpoint under translation.** Here the statement is about absolute coordinates
rather than about `seg`, so the invariance is a short computation rather than a rewrite. -/
theorem midpoint_translate (m a b : ℕ) (t : Pt n) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.midpoint m a b) pts) :
    GeoConstraint.Holds (.midpoint m a b) (translate t pts) := by
  show ∀ i, 2 * translate t pts m i = translate t pts a i + translate t pts b i
  intro i
  unfold translate
  have := (show ∀ i, 2 * pts m i = pts a i + pts b i from h) i
  linarith [this]

/-! ## Positive scaling

Scaling is where the `poly` and `square` layers part ways: a constraint stated as a homogeneous equation in
the displacements survives, one that compares a squared distance to a prescribed value does not. -/

/-- **Scaling about the origin** by a nonzero factor. -/
noncomputable def scale (s : ℝ) (pts : ℕ → Pt n) : ℕ → Pt n :=
  fun p i => s * pts p i

/-- A displacement under scaling is the scaled displacement. -/
theorem seg_scale (s : ℝ) (pts : ℕ → Pt n) (p q : ℕ) :
    GeoConstraint.seg (scale s pts) p q = fun i => s * GeoConstraint.seg pts p q i := by
  funext i
  unfold GeoConstraint.seg scale
  ring

/-- **Perpendicularity survives scaling**, because the inner product collects `s²`. -/
theorem perpendicular_scale (a b c e : ℕ) (s : ℝ) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.perpendicular a b c e) pts) :
    GeoConstraint.Holds (.perpendicular a b c e) (scale s pts) := by
  show (∑ i, GeoConstraint.seg (scale s pts) a b i * GeoConstraint.seg (scale s pts) c e i) = 0
  have hs : ∀ i, GeoConstraint.seg (scale s pts) a b i = s * GeoConstraint.seg pts a b i :=
    fun i => congrFun (seg_scale s pts a b) i
  have hse : ∀ i, GeoConstraint.seg (scale s pts) c e i = s * GeoConstraint.seg pts c e i :=
    fun i => congrFun (seg_scale s pts c e) i
  simp only [hs, hse]
  rw [Finset.sum_congr rfl (fun i _ => by ring : ∀ i ∈ Finset.univ,
    s * GeoConstraint.seg pts a b i * (s * GeoConstraint.seg pts c e i)
      = s * s * (GeoConstraint.seg pts a b i * GeoConstraint.seg pts c e i))]
  rw [← Finset.mul_sum]
  have hh : (∑ i, GeoConstraint.seg pts a b i * GeoConstraint.seg pts c e i) = 0 := h
  rw [hh, mul_zero]

/-- **A midpoint survives scaling**, since the equation is homogeneous of degree one on each side. -/
theorem midpoint_scale (m a b : ℕ) (s : ℝ) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.midpoint m a b) pts) :
    GeoConstraint.Holds (.midpoint m a b) (scale s pts) := by
  show ∀ i, 2 * scale s pts m i = scale s pts a i + scale s pts b i
  intro i
  unfold scale
  have hi := (show ∀ i, 2 * pts m i = pts a i + pts b i from h) i
  linear_combination s * hi

/-- **Coincidence survives any scaling**, including a degenerate one. -/
theorem samePoint_scale (a b : ℕ) (s : ℝ) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.samePoint a b) pts) :
    GeoConstraint.Holds (.samePoint a b) (scale s pts) := by
  show scale s pts a = scale s pts b
  unfold scale
  funext i
  rw [congrFun (show pts a = pts b from h) i]

end Lattice.Geo
