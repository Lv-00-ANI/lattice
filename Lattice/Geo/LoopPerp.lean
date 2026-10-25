import Mathlib
import Lattice.Geo.RepairPerp
import Lattice.Core.Repair

/-!
# `Lattice.Geo.LoopPerp` -- the verification loop for perpendicularity

## What this adds to `Lattice.Geo.Loop`

`Lattice.Geo.Loop` closed the loop for `samePoint` by copying one point onto another. That operator works by
**identifying** two points, which is the least geometric repair imaginable: it satisfies the constraint by
removing the configuration the constraint was about.

`Lattice.Geo.RepairPerp` supplied the opposite kind of operator -- a projection that moves one point and leaves
the rest -- and proved it establishes the perpendicularity. This file turns that operator into a `Repair`
inhabitant, so the loop's convergence guarantee applies to a repair that *rotates* rather than *collapses*.

## The conservativity lemma

`Repair.absorbs` demands that a satisfying configuration is left untouched. For a projection this is a
theorem, not a convention: when the displacement is already orthogonal the coefficient `perpRatio` is zero and
the projected point equals the original. `fixPerp_absorbs` proves it.

That lemma is the precise content of the objective's "回路收敛**不破坏语义**": a repair that moved an
already-correct configuration would converge while destroying what it had. Conservativity is what rules that
out, and it is provable here because `perpRatio` is defined as a quotient that vanishes on the nose.

## The hypothesis about the reference segment

`fixPerp` divides by `⟨v, v⟩` where `v = seg c e`. For the repair to be total, `c` and `e` must differ in
*every* configuration, so the instance carries `∀ pts, pts c ≠ pts e`. That is a genuine condition on the
constraint -- two coincident points define no direction to be perpendicular to -- and it is stated as a
parameter rather than assumed silently.
-/

namespace Lattice.Geo

open Classical

variable {n : ℕ}

/-- **The projection is the identity when the constraint already holds.**

If `⟨w, v⟩ = 0` then `perpRatio = 0`, so `w - 0·v = w` and `b` is unchanged. This is the conservativity that
`Repair.absorbs` requires, and the reason a perpendicular repair can be iterated without undoing previous
progress. -/
theorem fixPerp_absorbs (a b c e : ℕ) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.perpendicular a b c e) pts)
    (hv : (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0) :
    fixPerp a b c e pts = pts := by
  funext p
  by_cases hp : p = b
  · rw [hp]
    -- at `b` the projection is `a + w - 0·v = b`
    rw [fixPerp_self]
    funext i
    unfold projectedB perpRatio
    have hzero : (∑ j, (pts b j - pts a j) * (pts e j - pts c j)) = 0 := h
    rw [hzero, zero_div, zero_mul, sub_zero]
    ring
  · exact fixPerp_other a b c e pts hp

/-- **The measure for the perpendicular repair**: zero exactly where the constraint holds.

Defined through `Holds` rather than through the explicit sum. An earlier revision wrote the sum out and then
had to prove the two forms agree -- which is the same `seg`-versus-subtraction mismatch that made
`fixPerp_holds` hard. Using the predicate removes the conversion entirely.
-/
noncomputable def perpMeasure (a b c e : ℕ) (pts : ℕ → Pt n) : ℕ :=
  if GeoConstraint.Holds (.perpendicular a b c e) pts then 0 else 1

/-- The measure vanishes exactly on satisfying configurations. -/
theorem perpMeasure_eq_zero_iff (a b c e : ℕ) (pts : ℕ → Pt n) :
    perpMeasure a b c e pts = 0 ↔ GeoConstraint.Holds (.perpendicular a b c e) pts := by
  unfold perpMeasure
  by_cases h : GeoConstraint.Holds (.perpendicular a b c e) pts <;> simp [h]

/-- **A repair operator for perpendicularity.**

Unlike `Lattice.Geo.Loop.samePointRepair`, whose step identifies two points, this one **moves** `b` onto the
plane through `a` orthogonal to `seg c e`. The disjointness hypotheses and the reference-segment condition are
geometric: the projection rewrites one point, and it needs a direction to project against.
-/
noncomputable def perpRepair (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n, (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0) :
    Lattice.Core.Repair (ℕ → Pt n) where
  Sat := fun pts => GeoConstraint.Holds (.perpendicular a b c e) pts
  fix := fixPerp a b c e
  μ := perpMeasure a b c e
  absorbs := by
    intro pts h
    exact fixPerp_absorbs a b c e pts h (hv pts)
  decreases := by
    intro pts h
    -- the fix establishes the constraint, so the measure falls from 1 to 0
    have hsat : GeoConstraint.Holds (.perpendicular a b c e) (fixPerp a b c e pts) :=
      fixPerp_holds a b c e pts hab hcb heb (hv pts)
    show perpMeasure a b c e (fixPerp a b c e pts) < perpMeasure a b c e pts
    unfold perpMeasure
    simp only [hsat, h, if_true, if_false]
    norm_num

  atomic := by
    intro pts h
    exact (perpMeasure_eq_zero_iff a b c e pts).mp h

/-- **The verification loop converges for perpendicularity.**

`Repair.progress` at `perpRepair`: from any configuration, some number of projection steps reaches one where
the two segments are orthogonal. -/
theorem perp_loop_converges (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n, (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    ∃ k : ℕ, (perpRepair a b c e hab hcb heb hv).Sat
      ((perpRepair a b c e hab hcb heb hv).iterate k pts) :=
  (perpRepair a b c e hab hcb heb hv).progress pts

/-- **The loop converges in one step**, sharper than `Repair.progress` promises: a single projection
suffices. -/
theorem perp_loop_converges_in_one (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n, (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.perpendicular a b c e) (fixPerp a b c e pts) :=
  fixPerp_holds a b c e pts hab hcb heb (hv pts)

/-- **Convergence does not destroy meaning.** After the loop the constraint holds, and — because
`fixPerp_absorbs` — a configuration that already satisfied it would not have been altered. Together these are
the objective's "回路收敛不破坏语义" for this constraint. -/
theorem perp_loop_preserves (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n, (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) (h : GeoConstraint.Holds (.perpendicular a b c e) pts) :
    fixPerp a b c e pts = pts :=
  fixPerp_absorbs a b c e pts h (hv pts)

/-! ## What `perpRepair` leaves alone

`fixPerp` writes into exactly one slot: `b`'s. So every other point keeps its position, and any constraint that
mentions no coordinate of `b` survives the step.

That matters because of a failure recorded in `Lattice.Geo.ClosedLoop`: a *product* repair -- `Sat := Sat₁ ∧ Sat₂`,
`fix := R₁.fix ∘ R₂.fix`, `μ := μ₁ + μ₂` -- does not satisfy `Repair.decreases`, since repairing one constraint can
undo another and the summed measure need not drop. The hypothesis that would rescue the product is
**non-interference**, and here is a concrete instance of it: a `samePoint p q` constraint with `p, q ≠ b` is
preserved by the perpendicular repair, because the repair never writes to `p` or `q`.

The condition is not a technicality. When `p = b` the repair moves `b` onto its projection, and the coincidence is
generally broken -- exactly the interference the product would have to exclude. -/

/-- **`fixPerp` writes only at `b`**: every other index keeps its position. -/
theorem fixPerp_apply_of_ne (a b c e : ℕ) (pts : ℕ → Pt n) (p : ℕ) (hp : p ≠ b) :
    fixPerp (n := n) a b c e pts p = pts p :=
  Function.update_noteq hp _ pts

/-- **The perpendicular repair preserves a `samePoint` constraint whose points avoid `b`.**

This discharges, for one pair of constraints, the non-interference hypothesis that a product `Repair` would need. -/
theorem fixPerp_preserves_samePoint (a b c e : ℕ) (pts : ℕ → Pt n) (p q : ℕ)
    (hp : p ≠ b) (hq : q ≠ b) (h : pts p = pts q) :
    fixPerp (n := n) a b c e pts p = fixPerp (n := n) a b c e pts q := by
  rw [fixPerp_apply_of_ne a b c e pts p hp, fixPerp_apply_of_ne a b c e pts q hq]
  exact h

end Lattice.Geo
