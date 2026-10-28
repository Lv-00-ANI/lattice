import Mathlib
import Lattice.Geo.Loop
import Lattice.Geo.SeqRepresentation
import Lattice.Geo.ConjRepair
import Lattice.Geo.Flatten
import Lattice.Runtime.Extraction
/-!
# `Lattice.Geo.ClosedLoop` -- the verification loop closed on a concrete geometric object

## What this file is

`Lattice.Lift.loop_fixed_point` states, for an abstract `Representation` and `Repair`, that the loop stops at a point
which is satisfied, repair-stable, and fixed by compile-then-extract. That theorem says nothing about geometry:
`P` and `W` are arbitrary.

This file supplies the two concrete pieces and applies it:

* the `Representation` is `flattenRepresentation k n` -- finite point sets laid out as real vectors, with
  `flatten`/`unflatten` as the two directions (`Lattice.Geo.Flatten`);
* the `Repair` is `samePointRepairFin a b` -- the `Fin k` version, which copies `a`'s position into `b`'s slot
  (`Lattice.Geo.Loop`).

Putting them together gives a statement about actual geometry: **from any finite point set there is a
configuration where `a` and `b` coincide, further repair leaves it alone, and it survives the round trip through
the real vector space.**

## Why the two concrete pieces had to be built rather than reused

The `ℕ`-indexed `samePointRepair` of `Lattice.Geo.Loop` is a `Repair (ℕ → Pt n)`, and `flattenRepresentation` is
indexed by `Fin k`. A `Repair` must live on the same type as the `Representation` it is paired with, so the choice
was to re-index the repair or to re-index the representation -- and re-indexing the repair costs three proofs that
never depended on `ℕ` in the first place. Re-indexing the representation was rejected: `flatten` needs a finite
index to have a finite image, and an infinite index would make the round trip say something different.

## What is **not** claimed

That the loop returns to the configuration it started from. It cannot: that would need a right inverse of extraction
on the semantic quotient, and `Lattice.Geo.Semantic.semantic_not_injective` shows none exists. The loop stops at *a*
stable configuration, not *the* original one. This is the same layering the objective demands of reversibility --
object level bijective, semantic level not -- applied to the loop rather than to the extraction.
-/

namespace Lattice.Geo

variable {k n : ℕ}

/-- **The loop stops at a configuration where `a` and `b` coincide, repair does not move it, and the round trip
through the real vector space returns it unchanged.**

This is `Lattice.Lift.loop_fixed_point` at the two concrete instances this layer provides, and it is the object-level
statement the abstract theorem was for. Note what the three conjuncts cost: the first from `Repair.progress`, the
second from `Repair.absorbs`, the third from `flattenEquiv`'s two inverse laws. -/
theorem geometric_loop_fixed_point (a b : Fin k) (pts : Fin k → Pt n) :
    ∃ q : Fin k → Pt n,
      q a = q b ∧
      (samePointRepairFin a b).fix q = q ∧
      (flattenRepresentation k n).extract ((flattenRepresentation k n).compile q) = q :=
  Lattice.Lift.loop_fixed_point (flattenRepresentation k n) (samePointRepairFin a b) pts

/-- **The stopping configuration is reached in finitely many repair steps**, stated with the step count a caller
watching the repair would want, rather than existentially over all configurations. -/
theorem geometric_loop_reaches_satisfied (a b : Fin k) (pts : Fin k → Pt n) :
    ∃ m : ℕ, (samePointRepairFin a b).Sat ((samePointRepairFin a b).fix^[m] pts) :=
  (samePointRepairFin a b).progress pts

/-- **… and once there, the loop cannot move off it**, which is the stability half on its own. -/
theorem geometric_loop_is_stable (a b : Fin k) (pts : Fin k → Pt n) :
    ∃ q : Fin k → Pt n,
      q a = q b ∧ (samePointRepairFin a b).fix q = q :=
  Lattice.Lift.loop_fixed_point_stable (flattenRepresentation k n) (samePointRepairFin a b) pts

/-! ## A whole family of `samePoint` constraints at once

The theorems above handle one constraint. A real geometric problem carries a family: "these `k` points all
coincide" is `k * k` constraints, and the repair loop has to satisfy all of them together.

Two ways to get there were considered and one was rejected.

**Rejected: a product `Repair`.** Given `R₁ R₂ : Repair α`, one would define `Sat := Sat₁ ∧ Sat₂` and
`fix := R₁.fix ∘ R₂.fix` with `μ := R₁.μ + R₂.μ`. The `decreases` field then fails: repairing `R₁` can undo what
`R₂` just fixed, so `R₂.μ` climbs back while `R₁.μ` falls, and the sum need not drop. Adding a non-interference
hypothesis would rescue it, at the cost of a hypothesis the geometry layer cannot supply -- no repair here keeps
another constraint satisfied by construction.

**Taken: collapse.** For `samePoint` specifically there is a repair that satisfies the whole family in one step, so
no product is needed: move every point onto one chosen point's position. The measure reaches zero immediately, and
the conclusion covers all `k * k` constraints rather than one.

The limitation is honest: collapsing satisfies *conjunctions of `samePoint`*, not arbitrary conjunctions. -/

/-- **Collapse every point onto `p₀`'s position.** One step, not an iteration: the result already satisfies every
`samePoint` constraint among the points. -/
def collapseTo (p₀ : Fin k) (pts : Fin k → Pt n) : Fin k → Pt n :=
  fun _ => pts p₀

/-- **Collapsing satisfies every `samePoint` constraint at once.** -/
theorem collapseTo_pairwise (p₀ : Fin k) (pts : Fin k → Pt n) (i j : Fin k) :
    collapseTo p₀ pts i = collapseTo p₀ pts j :=
  rfl

/-- **The collision is total**: every point lands on `p₀`'s position, which is what makes the family satisfied
rather than only pairwise-equal by accident. -/
theorem collapseTo_apply (p₀ : Fin k) (pts : Fin k → Pt n) (i : Fin k) :
    collapseTo p₀ pts i = pts p₀ :=
  rfl

/-- **The collapsed configuration is a fixed point of the whole family's requirement and survives the round trip.**

This is the closed loop on a *family* of constraints rather than a single one: from any finite point set there is a
configuration in which all points coincide, and which `flatten`/`unflatten` return unchanged.

Note what is **not** claimed: that the loop *reaches* the collapsed configuration by iterating `fix`. Collapse is a
one-shot map, not a `Repair` step, so this theorem says the configuration exists and is round-trip stable -- the
`geometric_loop_fixed_point` above is what says the iterative loop reaches a stable point, and it does so for one
constraint at a time. -/
theorem geometric_loop_all_samePoint (p₀ : Fin k) (pts : Fin k → Pt n) :
    ∃ q : Fin k → Pt n,
      (∀ i j : Fin k, q i = q j) ∧
      (flattenRepresentation k n).extract ((flattenRepresentation k n).compile q) = q :=
  ⟨collapseTo p₀ pts, collapseTo_pairwise p₀ pts,
    (flattenRepresentation k n).roundtrip _⟩

/-- **The family statement via the abstract loop**: if a repair is given whose satisfying set is "all points
coincide", then the iterative loop reaches a configuration that is both fully collapsed and round-trip stable. -/
theorem geometric_loop_reaches_all_samePoint
    (Rp : Lattice.Core.Repair (Fin k → Pt n))
    (hRsat : ∀ q, Rp.Sat q ↔ ∀ i j : Fin k, q i = q j)
    (pts : Fin k → Pt n) :
    ∃ q : Fin k → Pt n,
      (∀ i j : Fin k, q i = q j) ∧
      Rp.fix q = q ∧
      (flattenRepresentation k n).extract ((flattenRepresentation k n).compile q) = q := by
  obtain ⟨q, hsat, habs, hrt⟩ :=
    Lattice.Lift.loop_fixed_point (flattenRepresentation k n) Rp pts
  exact ⟨q, (hRsat q).mp hsat, habs, hrt⟩

/-! ## The loop closed on two constraints of different kinds

The theorems above pair the loop with one constraint kind at a time. `Lattice.Geo.ConjRepair` builds a `Repair` for the
*conjunction* of a `samePoint` and a `perpendicular` -- possible only because each repair writes into a single slot
and the two slots are disjoint (`q ∉ {a, b, c, e}`, `p, q ≠ b`), so neither undoes the other.

`Lattice.Geo.SeqRepresentation` then supplies the `Representation` those repairs need: the constraint language indexes
points by `ℕ`, while `flattenRepresentation` indexes them by `Fin k`, so a `Repair (ℕ → Pt n)` could not be paired
with it. Flattening `(ℕ → Pt n)` to `(ℕ → ℝ)` row-major removes that mismatch.

With both pieces in place the abstract theorem applies unchanged, and what comes out is the only form of closure the
project claims: **a stop point, not a return**. -/

/-- **The loop stops at a configuration satisfying two constraints of different kinds, repair-stable, and
round-trip fixed.**

This is `Lattice.Lift.loop_fixed_point` at `seqRepresentation` and `conjRepair`. The three conjuncts cost exactly what
they cost there -- termination, absorption, and the round trip -- but here all three are about a real geometric
configuration rather than an abstract `P`. -/
theorem conj_loop_fixed_point
    (hn : 0 < n)
    (a b c e p q : ℕ)
    (hp : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n,
      (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    ∃ r : ℕ → Pt n,
      (r p = r q ∧ GeoConstraint.Holds (.perpendicular a b c e) r) ∧
      (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).fix r = r ∧
      (seqRepresentation (n := n) hn).extract
        ((seqRepresentation (n := n) hn).compile r) = r :=
  Lattice.Lift.loop_fixed_point (seqRepresentation (n := n) hn)
    (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv) pts

/-- **The loop reaches a state satisfying both constraints** in finitely many repair steps, with the step count
exposed. -/
theorem conj_loop_reaches
    (a b c e p q : ℕ)
    (hp : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n,
      (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    ∃ m : ℕ,
      (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).Sat
        ((conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).fix^[m] pts) :=
  (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).progress pts

/-- **... and the stop point is stable on its own**, stated without the round trip for a caller that only watches
the repair. -/
theorem conj_loop_is_stable
    (hn : 0 < n)
    (a b c e p q : ℕ)
    (hp : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqe : q ≠ e)
    (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n,
      (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    ∃ r : ℕ → Pt n,
      (r p = r q ∧ GeoConstraint.Holds (.perpendicular a b c e) r) ∧
      (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv).fix r = r :=
  Lattice.Lift.loop_fixed_point_stable (seqRepresentation (n := n) hn)
    (conjRepair a b c e p q hp hqa hqb hqc hqe hab hcb heb hv) pts

end Lattice.Geo
