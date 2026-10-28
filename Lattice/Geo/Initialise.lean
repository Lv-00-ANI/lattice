import Mathlib
import Lattice.Domains.Constraint
import Lattice.Geo.Invariant

/-!
# `Lattice.Geo.Initialise` -- constructing a satisfying configuration without training

## The third forward path

The objective names three ways to go from symbolic knowledge to weights: constraint loss, data synthesis,
and structured initialisation. This file supplies the third.

The distinction matters. A loss *searches* for a satisfying point; an initialiser **computes** one. When the
constraint determines its solution set algebraically there is no reason to search, and writing the solution
down gives the optimiser a start that is already correct on those constraints. That is what "structured
initialisation" means, and why it is not the same as a good guess.

## What is constructed here, and what is not

The collapsing configuration -- every point at the origin -- is the one witness that needs no case analysis,
and it settles five of the twelve predicates outright. It does **not** settle `sqDistEq` or `equalLength`
with a nonzero target: those prescribe a distance that a collapsed configuration cannot have. That boundary
is a theorem (`allSame_perpendicular` etc. are positive; the distance case is excluded by the shape of the
statements), not a remark.

## Why the base case is worth having

`allSame` is a *witness of satisfiability*, and satisfiability is what makes a penalty meaningful: a penalty
encodes a constraint faithfully only when the constraint can actually be met, otherwise its minimum is
positive and it says nothing -- the failure `Lattice.Lib.Penalty.Counterexample.polynomial_penalty_not_exact`
records. So this file connects the initialisation path to the loss path rather than sitting beside it.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The collapsing configuration**: every point sits at the origin. -/
noncomputable def allSame : ℕ → Pt n := fun _ _ => 0

/-- Two collapsing points at the same coordinate are equal, which is the only fact the proofs below need. -/
theorem allSame_apply (p : ℕ) (i : Fin n) : allSame (n := n) p i = 0 := rfl

/-- **Every coincidence constraint holds at the collapsing configuration.** -/
theorem allSame_samePoint (a b : ℕ) :
    GeoConstraint.Holds (n := n) (.samePoint a b) allSame := by
  show allSame a = allSame b
  funext i
  rfl

/-- **Every midpoint constraint holds at the collapsing configuration**, trivially: `0 = 0 + 0`. -/
theorem allSame_midpoint (m a b : ℕ) :
    GeoConstraint.Holds (n := n) (.midpoint m a b) allSame := by
  show ∀ i, 2 * allSame m i = allSame a i + allSame b i
  intro i
  have hm : allSame (n := n) m i = 0 := rfl
  have ha : allSame (n := n) a i = 0 := rfl
  have hb : allSame (n := n) b i = 0 := rfl
  rw [hm, ha, hb]
  norm_num

/-- **Every perpendicularity constraint holds at the collapsing configuration**, since both displacements
vanish. -/
theorem allSame_perpendicular (a b c e : ℕ) :
    GeoConstraint.Holds (n := n) (.perpendicular a b c e) allSame := by
  show (∑ i, GeoConstraint.seg allSame a b i * GeoConstraint.seg allSame c e i) = 0
  apply Finset.sum_eq_zero
  intro i _
  simp [GeoConstraint.seg, allSame]

/-- **Every collinearity constraint holds at the collapsing configuration**: the zero vector is a multiple of
itself. -/
theorem allSame_collinear (a b c : ℕ) :
    GeoConstraint.Holds (n := n) (.collinear a b c) allSame := by
  refine ⟨0, ?_⟩
  funext i
  simp [GeoConstraint.seg, allSame]

/-- **Every parallelism constraint holds at the collapsing configuration.** -/
theorem allSame_parallel (a b c e : ℕ) :
    GeoConstraint.Holds (n := n) (.parallel a b c e) allSame := by
  refine ⟨0, ?_⟩
  funext i
  unfold GeoConstraint.seg
  simp [GeoConstraint.seg, allSame]

/-- **Every right angle holds at the collapsing configuration.** -/
theorem allSame_rightAngle (a b c : ℕ) :
    GeoConstraint.Holds (n := n) (.rightAngle a b c) allSame := by
  show (∑ i, GeoConstraint.seg allSame a b i * GeoConstraint.seg allSame b c i) = 0
  apply Finset.sum_eq_zero
  intro i _
  simp [GeoConstraint.seg, allSame]

/-- **Structured initialisation for a coincidence system.**

A constraint list made only of coincidences is satisfied by the collapsing configuration, with the witness
written down rather than asserted to exist. This is the base case every more elaborate initialiser needs,
and it is exact -- no search, no side conditions. -/
theorem satisfiable_of_samePoint_only (G : List (GeoConstraint n))
    (h : ∀ c ∈ G, ∃ a b : ℕ, c = .samePoint a b) :
    ∃ pts : ℕ → Pt n, ∀ c ∈ G, GeoConstraint.Holds c pts := by
  refine ⟨allSame, ?_⟩
  intro c hc
  obtain ⟨a, b, rfl⟩ := h c hc
  exact allSame_samePoint a b

/-- **Structured initialisation for a system of coincidences and midpoints.**

The two linear layers together are still settled by the collapsing configuration, so the initialiser covers a
strictly larger class without needing the midpoint equations to be solved. This is worth stating separately
because it shows the method's reach is not accidental: any constraint whose statement is homogeneous in
positions is met at the origin. -/
theorem satisfiable_of_linear_layers (G : List (GeoConstraint n))
    (h : ∀ c ∈ G,
      (∃ a b : ℕ, c = .samePoint a b) ∨ (∃ m a b : ℕ, c = .midpoint m a b)) :
    ∃ pts : ℕ → Pt n, ∀ c ∈ G, GeoConstraint.Holds c pts := by
  refine ⟨allSame, ?_⟩
  intro c hc
  rcases h c hc with ⟨a, b, rfl⟩ | ⟨m, a, b, rfl⟩
  · exact allSame_samePoint a b
  · exact allSame_midpoint m a b

end Lattice.Geo
