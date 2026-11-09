import Mathlib
import Lattice.Reference.Geometry.Geometry.Loop
import Lattice.Reference.Geometry.Geometry.LoopPerp
import Lattice.Reference.Geometry.Geometry.RepairPerp
import Lattice.Core.Repair

/-!
# `Lattice.Geo.ConjRepair` -- repairing two constraints of different kinds at once

## The problem this file answers

`Lattice.Geo.ClosedLoop` records that a product of repairs does not work in general. Given `R₁ R₂ : Repair α` and
`Sat := Sat₁ ∧ Sat₂`, `fix := R₁.fix ∘ R₂.fix`, `μ := μ₁ + μ₂`, the `decreases` field fails: repairing `R₁` can
undo what `R₂` just did, so `μ₂` climbs back while `μ₁` falls and the sum need not drop.

The hypothesis that rescues the product is **non-interference** -- each repair leaves the other's satisfying set
alone. `Lattice.Geo.LoopPerp` supplies one half of it for two concrete constraints:

* `fixPerp_apply_of_ne`: the perpendicular repair writes only at `b`;
* `fixPerp_preserves_samePoint`: so a `samePoint p q` with `p, q ≠ b` survives it.

This file supplies the other half and builds the product.

## The other half, and why it needs a set-membership hypothesis

`fixSamePoint p q` writes only at `q`. For it to leave `perpendicular a b c e` alone, `q` must avoid **every** point
the constraint mentions: `q ∉ {a, b, c, e}`. One inequality would not do -- the constraint reads four positions, and
writing into any of them changes it.

That is a real restriction, not a formality: it says the two constraints must not share a point. Sharing a point is
exactly how interference arises, so a product that pretended otherwise would fail on a counterexample rather than
in the arithmetic.

## What the sum-measure argument needs

With `μ := samePointMeasure + perpMeasure` (each 0 or 1), the decrease case analysis has only a few shapes, and the
interference hypotheses are what close them:

* neither satisfied: the first step drops `samePointMeasure` to 0, the second drops `perpMeasure` to 0;
* only `samePoint` satisfied: the first step is the identity, the second drops `perpMeasure`;
* only `perpendicular` satisfied: the first step drops `samePointMeasure` **and**, by non-interference, leaves
  `perpMeasure` at 0; the second step is the identity on the measure;
* both satisfied: absorbed, so `decreases` is vacuous.

## What is **not** claimed

That the two constraints can be repaired when they *do* share a point. The product above is only one way to combine
repairs, and its failure when `q ∈ {a, b, c, e}` says that way does not extend -- not that no way does.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **`fixSamePoint p q` writes only at `q`**, read off `Function.update`. -/
theorem fixSamePoint_apply_of_ne (p q : ℕ) (pts : ℕ → Pt n) (i : ℕ) (h : i ≠ q) :
    fixSamePoint p q pts i = pts i := by
  show Function.update pts q (pts p) i = pts i
  exact Function.update_noteq h (pts p) pts

/-- **A `samePoint` repair whose written slot avoids every point of a perpendicular constraint leaves that
constraint alone.**

`q ∉ {a, b, c, e}` is the whole content: all four positions the constraint reads are untouched, so the dot product is
the same before and after. -/
theorem fixSamePoint_preserves_perp
    (a b c e p q : ℕ) (pts : ℕ → Pt n)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e) :
    GeoConstraint.Holds (.perpendicular a b c e) (fixSamePoint p q pts)
      ↔ GeoConstraint.Holds (.perpendicular a b c e) pts := by
  have ha : fixSamePoint p q pts a = pts a := fixSamePoint_apply_of_ne p q pts a (fun h => hqa h.symm)
  have hb : fixSamePoint p q pts b = pts b := fixSamePoint_apply_of_ne p q pts b (fun h => hqb h.symm)
  have hc : fixSamePoint p q pts c = pts c := fixSamePoint_apply_of_ne p q pts c (fun h => hqc h.symm)
  have he : fixSamePoint p q pts e = pts e := fixSamePoint_apply_of_ne p q pts e (fun h => hqe h.symm)
  show (∑ i, GeoConstraint.seg (fixSamePoint p q pts) a b i
            * GeoConstraint.seg (fixSamePoint p q pts) c e i) = 0
      ↔ (∑ i, GeoConstraint.seg pts a b i * GeoConstraint.seg pts c e i) = 0
  have hcongr : (∑ i, GeoConstraint.seg (fixSamePoint p q pts) a b i
                       * GeoConstraint.seg (fixSamePoint p q pts) c e i)
              = (∑ i, GeoConstraint.seg pts a b i * GeoConstraint.seg pts c e i) := by
    apply Finset.sum_congr rfl
    intro i _
    show (fixSamePoint p q pts b i - fixSamePoint p q pts a i)
           * (fixSamePoint p q pts e i - fixSamePoint p q pts c i)
       = (pts b i - pts a i) * (pts e i - pts c i)
    rw [ha, hb, hc, he]
  rw [hcongr]

/-- **The composite measure**: `samePointMeasure` plus `perpMeasure`. Each is 0 or 1, so the sum is 0 exactly when
both constraints hold -- which is what `atomic` below needs. -/
noncomputable def conjMeasure (a b c e p q : ℕ) (pts : ℕ → Pt n) : ℕ :=
  samePointMeasure p q pts + perpMeasure a b c e pts

/-- **The composite measure is zero exactly when both constraints hold.** A sum of two naturals is zero exactly
when both are. -/
theorem conjMeasure_eq_zero_iff (a b c e p q : ℕ) (pts : ℕ → Pt n) :
    conjMeasure a b c e p q pts = 0
      ↔ pts p = pts q ∧ GeoConstraint.Holds (.perpendicular a b c e) pts := by
  unfold conjMeasure
  rw [Nat.add_eq_zero_iff, samePointMeasure_eq_zero_iff, perpMeasure_eq_zero_iff]

/-- **Repairing a `samePoint` and a `perpendicular` constraint together.**

The two constraints are repaired in sequence -- first the coincidence, then the perpendicularity -- and the measure is
their sum. That product shape fails in general (`Lattice.Geo.ClosedLoop` records why), and it works here because each
step leaves the other constraint alone:

* `fixSamePoint` writes only at `q`, and `q` avoids all four points the perpendicular constraint reads;
* `fixPerp` writes only at `b`, and `p, q` both avoid `b`.

So after the two steps both constraints hold, the measure is `0`, and the hypothesis that the composite was failing
(`¬ Sat pts`) guarantees it started above `0`.

The hypotheses are therefore not decoration: `q ∉ {a, b, c, e}` is what rules out interference, `p, q ≠ b` is what
rules out the perpendicular step breaking the coincidence, and the remaining non-degeneracy conditions are what the
two individual repairs already required. -/
noncomputable def conjRepair
    (a b c e p q : ℕ)
    (hp : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n,
      (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0) :
    Lattice.Core.Repair (ℕ → Pt n) where
  Sat := fun pts => pts p = pts q ∧ GeoConstraint.Holds (.perpendicular a b c e) pts
  fix := fun pts => fixPerp a b c e (fixSamePoint p q pts)
  μ := conjMeasure a b c e p q
  absorbs := by
    intro pts h
    show fixPerp a b c e (fixSamePoint p q pts) = pts
    rw [fixSamePoint_absorbs p q pts h.1]
    exact fixPerp_absorbs a b c e pts h.2
  decreases := by
    intro pts h
    -- After the two steps both constraints hold, so the measure is zero.
    have hs1 : fixPerp a b c e (fixSamePoint p q pts) p
             = fixPerp a b c e (fixSamePoint p q pts) q :=
      fixPerp_preserves_samePoint a b c e (fixSamePoint p q pts) p q hp hqb
        (fixSamePoint_holds p q pts)
    have hs2 : GeoConstraint.Holds (.perpendicular a b c e)
        (fixPerp a b c e (fixSamePoint p q pts)) :=
      fixPerp_holds a b c e (fixSamePoint p q pts) hab hcb heb (hv _)
    have hzero : conjMeasure a b c e p q (fixPerp a b c e (fixSamePoint p q pts)) = 0 :=
      (conjMeasure_eq_zero_iff a b c e p q _).mpr ⟨hs1, hs2⟩
    -- The measure that was not zero, because the point failed.
    have hpos : conjMeasure a b c e p q pts ≠ 0 := by
      intro hz
      exact h ((conjMeasure_eq_zero_iff a b c e p q pts).mp hz)
    show conjMeasure a b c e p q (fixPerp a b c e (fixSamePoint p q pts))
       < conjMeasure a b c e p q pts
    rw [hzero]
    exact Nat.pos_of_ne_zero hpos
  atomic := by
    intro pts h
    exact (conjMeasure_eq_zero_iff a b c e p q pts).mp h

end Lattice.Geo
