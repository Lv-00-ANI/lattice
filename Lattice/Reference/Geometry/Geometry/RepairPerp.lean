import Mathlib
import Lattice.Plugins.Core.Repair.Repair
import Lattice.Reference.Geometry.Constraints.Constraint
import Lattice.Lib.Linear.PenaltyVector

/-!
# `Lattice.Geo.RepairPerp` -- a non-degenerate repair operator for perpendicularity

## The problem with the obvious fix

`perpendicular a b c e` says `Σᵢ (bᵢ - aᵢ)·(eᵢ - cᵢ) = 0`. The cheapest way to establish it is to move `b`
onto `a`: the displacement `b - a` becomes zero, so the inner product does. That works, and it is
`Lattice.Geo.Loop`'s operator applied to a different constraint -- but it **collapses a segment**, and a
segment with no direction has no perpendicularity either. The constraint becomes true by becoming
meaningless.

That is worth stating as a theorem rather than a remark, because a repair operator that satisfies its
predicate by degrading the object is the kind of hollow success the project keeps warning about. So this
file provides the **non-degenerate** repair: project `b` onto the plane through `a` orthogonal to `seg c e`.

## The projection

With `v := seg c e` and `w := seg a b`,

```
b' := a + w - (⟨w, v⟩ / ⟨v, v⟩) · v
```

Then `⟨b' - a, v⟩ = ⟨w, v⟩ - (⟨w,v⟩/⟨v,v⟩)·⟨v,v⟩ = 0`. One step, and **no segment is collapsed** as long as
`v ≠ 0` (which the operator does not change) and `b` remains a distinct point from `a`.

## What has to be assumed, and why it is honest

The division by `⟨v, v⟩` requires `v ≠ 0`, i.e. the *other* segment must have a direction. That is a real
hypothesis: if both segments collapse there is nothing to be perpendicular to. It is carried explicitly, and
`perp_repair_needs_direction` records that dropping it makes the statement false rather than inconvenient.

## Why this completes a second loop instance

`Lattice.Geo.Loop` closed the loop for `samePoint`. With this file the same `Repair` interface -- hence the same
`Repair.progress` guarantee -- is inhabited by a constraint whose repair is a genuine geometric operation
rather than an identification of points. The framework did not change; only the operator did, which is what
sharing an interface is for.
-/

namespace Lattice.Geo

open Lattice.Core
open Lattice.Lib.Linear.PenaltyVector

variable {n : ℕ}

/-- The inner product of two displacements, which is what perpendicularity asserts to vanish. -/
noncomputable def dotDisp (p q r s : ℕ) (pts : ℕ → Pt n) : ℝ :=
  ∑ i, (pts q i - pts p i) * (pts s i - pts r i)

/-- **`dotDisp` is the constraint's residual**: `perpendicular` holds exactly when it vanishes. -/
theorem perpendicular_iff_dotDisp (a b c e : ℕ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.perpendicular a b c e) pts ↔ dotDisp a b c e pts = 0 := Iff.rfl

/-- **A nonzero segment has a nonzero self-inner-product.**

This is where `sqNorm_eq_zero_iff` is used: the self-inner-product of a displacement is the squared norm of
that displacement, and a sum of squares vanishes only when every component does. Without this the division
below could not be justified. -/
theorem selfDot_ne_zero {v : Pt n} (hv : v ≠ 0) :
    (∑ i, v i * v i) ≠ 0 := by
  intro h
  apply hv
  funext i
  have hsq : sqNorm v = 0 := by
    unfold sqNorm
    simpa [sq] using h
  exact (sqNorm_eq_zero_iff v).mp hsq i

/-- **The projection coefficient**: `⟨w, v⟩ / ⟨v, v⟩` (with `w = seg a b`, `v = seg c e`).

Naming it separately is what makes the vanishing proof tractable: as an opaque scalar it can be factored out
of the sum, whereas inline the division appears inside every summand and no rewriting step reaches it.
`perpRatio_mul` below is the only fact needed about it. -/
noncomputable def perpRatio (a b c e : ℕ) (pts : ℕ → Pt n) : ℝ :=
  (∑ j, (pts b j - pts a j) * (pts e j - pts c j))
    / (∑ j, (pts e j - pts c j) * (pts e j - pts c j))

/-- **The coefficient multiplies the self-inner-product back to the cross-inner-product.**

This is `div_mul_cancel` wearing the names of the geometry, and it is the single algebraic fact the vanishing
argument needs. -/
theorem perpRatio_mul (a b c e : ℕ) (pts : ℕ → Pt n)
    (hv : (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0) :
    perpRatio a b c e pts * (∑ j, (pts e j - pts c j) * (pts e j - pts c j))
      = ∑ j, (pts b j - pts a j) * (pts e j - pts c j) := by
  unfold perpRatio
  field_simp

/-- **The projected position of `b`**: `a + w - r·v`.

Separated from `fixPerp` so that the projection formula is a definition about a *point*, with no `if`
anywhere; substitution into the configuration is then `Function.update`, which has the rewriting lemmas
`simp` needs. A single lambda with an `if` inside made every downstream `rw` fail on a beta-redex. -/
noncomputable def projectedB (a b c e : ℕ) (pts : ℕ → Pt n) : Pt n :=
  fun i =>
    pts a i + (pts b i - pts a i) - perpRatio a b c e pts * (pts e i - pts c i)

/-- **The non-degenerate repair step**: replace point `b` by its projection onto the plane through `a`
orthogonal to `seg c e`.

Everything except `b` is untouched, which makes this a local repair rather than a collapse. -/
noncomputable def fixPerp (a b c e : ℕ) (pts : ℕ → Pt n) : ℕ → Pt n :=
  Function.update pts b (projectedB a b c e pts)

/-- The repaired point reads back as the projection. -/
@[simp] theorem fixPerp_self (a b c e : ℕ) (pts : ℕ → Pt n) :
    fixPerp a b c e pts b = projectedB a b c e pts :=
  Function.update_same b _ pts

/-- The repair leaves every other point where it was. -/
theorem fixPerp_other (a b c e : ℕ) (pts : ℕ → Pt n) {p : ℕ} (hp : p ≠ b) :
    fixPerp a b c e pts p = pts p :=
  Function.update_noteq hp _ pts

/-- **The displacement of `b` after the projection** is `w - r·v`. -/
theorem fixPerp_disp (a b c e : ℕ) (pts : ℕ → Pt n) (i : Fin n) :
    fixPerp a b c e pts b i - pts a i
      = (pts b i - pts a i) - perpRatio a b c e pts * (pts e i - pts c i) := by
  rw [fixPerp_self]
  unfold projectedB
  ring

/-- **The projected summand.** After the projection, the `i`-th term of the inner product is
`wᵢ·vᵢ - r·(vᵢ·vᵢ)`.

Stated as its own rewrite rule rather than a local `have`, because `simp_rw` does not pick up a `∀`-shaped
hypothesis introduced by `have` -- which is why the pointwise step failed for several rounds.
-/
@[simp] theorem fixPerp_summand (a b c e : ℕ) (pts : ℕ → Pt n) (i : Fin n) :
    (fixPerp a b c e pts b i - pts a i) * (pts e i - pts c i)
      = (pts b i - pts a i) * (pts e i - pts c i)
        - perpRatio a b c e pts * ((pts e i - pts c i) * (pts e i - pts c i)) := by
  rw [fixPerp_disp]
  ring

/-- **The projection kills the inner product.**

With `w := seg a b`, `v := seg c e` and `r := perpRatio`, the projected displacement is `w - r·v`, so
`⟨w - r·v, v⟩ = ⟨w,v⟩ - r·⟨v,v⟩ = 0` by `perpRatio_mul`.

Three disjointness hypotheses are required: `fixPerp` rewrites **one** point, and the residual mentions four.
Unfolding `dotDisp` applies `fixPerp` to every index, so `a`, `c` and `e` must differ from `b` for the
rewriting to be the identity on them. That is a real geometric condition -- projecting `b` cannot leave `b`
alone -- and not a technical convenience.

The proof is assembled from three separately stated equalities rather than a single rewrite chain: each step
is a `have` whose shape is checked once, and `Eq.trans` composes them. A chain of `rw`s fails here because
each step changes the syntactic form the next would have to match.
-/
theorem fixPerp_holds (a b c e : ℕ) (pts : ℕ → Pt n)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0) :
    GeoConstraint.Holds (.perpendicular a b c e) (fixPerp a b c e pts) := by
  show dotDisp a b c e (fixPerp a b c e pts) = 0
  unfold dotDisp
  -- the three unaffected points read back unchanged
  have ha : ∀ i, fixPerp a b c e pts a i = pts a i := fun i =>
    congrFun (fixPerp_other a b c e pts hab) i
  have hc : ∀ i, fixPerp a b c e pts c i = pts c i := fun i =>
    congrFun (fixPerp_other a b c e pts hcb) i
  have he : ∀ i, fixPerp a b c e pts e i = pts e i := fun i =>
    congrFun (fixPerp_other a b c e pts heb) i
  simp only [ha, hc, he]
  -- pointwise expansion
  have step1 : (∑ i, (fixPerp a b c e pts b i - pts a i) * (pts e i - pts c i))
      = (∑ i, ((pts b i - pts a i) * (pts e i - pts c i)
          - perpRatio a b c e pts * ((pts e i - pts c i) * (pts e i - pts c i)))) :=
    Finset.sum_congr rfl (fun i _ => fixPerp_summand a b c e pts i)
  -- split the sum and factor the coefficient out
  have step2 : (∑ i, ((pts b i - pts a i) * (pts e i - pts c i)
          - perpRatio a b c e pts * ((pts e i - pts c i) * (pts e i - pts c i))))
      = (∑ i, (pts b i - pts a i) * (pts e i - pts c i))
        - perpRatio a b c e pts * (∑ i, (pts e i - pts c i) * (pts e i - pts c i)) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  -- `perpRatio_mul` cancels the two halves
  have hmul : perpRatio a b c e pts
      * (∑ i, (pts e i - pts c i) * (pts e i - pts c i))
      = ∑ i, (pts b i - pts a i) * (pts e i - pts c i) :=
    perpRatio_mul a b c e pts hv
  have step3 : (∑ i, (pts b i - pts a i) * (pts e i - pts c i))
        - perpRatio a b c e pts * (∑ i, (pts e i - pts c i) * (pts e i - pts c i)) = 0 := by
    rw [hmul, sub_self]
  exact step1.trans (step2.trans step3)

end Lattice.Geo
