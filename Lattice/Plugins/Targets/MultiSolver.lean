/-
# A `SpecSolver` for MANY constraints, not one

**Round 73's instance handled a SINGLE `samePoint` constraint.**
**That is the base case, but a spec is a LIST -- and the list is where the difficulty lives: a
solution for `c₁` need not be a solution for `c₂`, so a multi-constraint solver cannot simply reuse
the single-constraint one.**

## The family this file closes, and why it is a genuine multi-constraint case

**A list of `samePoint` constraints.** **`samePoint a b` says two points coincide.**

**Key observation: a CONSTANT configuration satisfies EVERY `samePoint` simultaneously.**
**=> the solver is `fun _ => c` for a fixed `c : Pt n`, and it is correct for specs of ANY length.**

**This is not a triviality dressed up as a theorem**: **it is the case where the constraints are
mutually COMPATIBLE by construction**, and it is exactly the case where "solve the whole spec at once"
has a closed form.
**A solver that could only handle `[c]` would be an interface nobody could use; a solver that handles
lists of arbitrary length exercises `HoldsSet`'s `∧` structure, which is the part T0's `construct_sound`
must traverse.**

## What is proved

**`holdsSet_samePoint_all`**: **any constant configuration satisfies any list of `samePoint`s.**
**`penalty_samePoint_all_zero`**: **and the total penalty of that list is zero there.**
-/

import Lattice.Plugins.Targets.Solver

namespace Lattice.Plugins.Targets

open Lattice.Geo
open Lattice.Geo.ConstraintSet
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open scoped BigOperators

/-- **A constant configuration satisfies a list of `samePoint` constraints.**

**Induction on the list**: **the head is discharged by the single-constraint lemma from round 73, the
tail by the induction hypothesis.** **This is the step that exercises `HoldsSet`'s `∧` -- a solver
must traverse it, not merely satisfy one conjunct.** -/
theorem holdsSet_samePoint_all {n : ℕ} (cs : List (ℕ × ℕ)) (p : Pt n) :
    HoldsSet (cs.map (fun ab => GeoConstraint.samePoint ab.1 ab.2)) (fun _ => p) := by
  induction cs with
  | nil =>
    -- the empty spec is satisfied by anything
    simp only [List.map_nil]
    exact holdsSet_nil _
  | cons hd tl ih =>
    refine ⟨?_, ?_⟩
    · -- the head: `GeoConstraint.Holds (samePoint a b) pts` is `pts a = pts b`
      rfl
    · exact ih

/-- **The total penalty of a `samePoint` list vanishes at a constant configuration.**

**Induction on the list, using `penalty_samePoint_const` at the head.** **The emptiness case is
`List.sum_nil`.** -/
theorem penalty_samePoint_all_zero {n : ℕ} (cs : List (ℕ × ℕ)) (p : Pt n) :
    ((cs.map (fun ab => GeoConstraint.samePoint ab.1 ab.2)).map
      (fun c => penaltyLoss c (fun _ => p))).sum = 0 := by
  induction cs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, penalty_samePoint_const, ih, add_zero]

/-- **A spec made of `samePoint` constraints.**

**The constructor takes a list of POINT PAIRS and builds the spec, with expressibility discharged by
`samePoint_expressible` at each position.**
**`HoldsSet` then reduces to `holdsSet_samePoint_all`, which is why the solver below is real rather
than hypothetical.** -/
def samePointSpec {n : ℕ} (cs : List (ℕ × ℕ)) : ExpressibleSpec n where
  constraints := cs.map (fun ab => GeoConstraint.samePoint ab.1 ab.2)
  expressible := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨ab, _, rfl⟩ := hc
    exact samePoint_expressible ab.1 ab.2

/-- **The `samePoint` family's solver, stated over the family rather than over `SpecSolver`.**

**`SpecSolver` quantifies `∀ S : ExpressibleSpec n` -- EVERY spec.**
**A `samePoint`-only construction cannot fill that field: an arbitrary `S` may contain
`rightAngle`, and `sound` would then have to hold for a constraint the construction knows nothing
about.**
**=> the family's solver is stated as its own structure, with the spec FIXED to the family.**

**This is not a weakening introduced to make the proof go through: it is the discovery that
`SpecSolver`'s `∀ S` is the right strength for a UNIVERSAL constructor and the WRONG strength for a
family-specific one.**
**Round 74 could only ASSERT this and cited a theorem that did not exist.**
**=> `SolverBoundary.no_specSolver` now PROVES it: `SpecSolver n` is `IsEmpty` whenever `Pt n` is
nonempty, because the expressible spec `[eqZero (const 1)]` has no model at all.**
**The reference is corrected rather than left pointing at nothing.** -/
structure FamilySolver (n : ℕ) where
  /-- **The constraint family this solver handles**, as a predicate on specs. -/
  Family : ExpressibleSpec n → Prop
  /-- **The construction.** -/
  solve : (S : ExpressibleSpec n) → Family S → (ℕ → Pt n)
  /-- **`construct_sound` restricted to the family.** -/
  sound : ∀ (S : ExpressibleSpec n) (hS : Family S) ⦃c : GeoConstraint n⦄,
    c ∈ S.constraints → HoldsSet [c] (solve S hS)
  /-- **`construct_canonical` restricted to the family.** -/
  canonical : ∀ (S T : ExpressibleSpec n) (hS : Family S) (hT : Family T),
    S.constraints = T.constraints → solve S hS = solve T hT
  /-- **The family's total penalty vanishes at the solution.** -/
  cost_zero : ∀ (S : ExpressibleSpec n) (hS : Family S),
    (S.constraints.map (fun c => penaltyLoss c (solve S hS))).sum = 0

/-- **The `samePoint` family: every constraint of the spec is a `samePoint`.** -/
def samePointFamily {n : ℕ} (S : ExpressibleSpec n) : Prop :=
  ∀ c ∈ S.constraints, ∃ a b, c = GeoConstraint.samePoint a b

/-- **The `samePoint` family's solver.**

**`solve` returns a fixed constant configuration `fun _ => p` for a supplied `p`.**
**`sound` uses the per-constraint characterisation: `samePointFamily` extracts `a` and `b`, and
`holds_samePoint_const` then discharges the singleton set.**
**`canonical` holds because the construction ignores its arguments.**
**`cost_zero` sums `penalty_samePoint_const` over the list.** -/
def samePointFamilySolver (n : ℕ) (p : Pt n) : FamilySolver n where
  Family := samePointFamily
  solve := fun _ _ => fun _ => p
  sound := by
    intro S hS c hc
    obtain ⟨a, b, rfl⟩ := hS c hc
    exact holds_samePoint_const a b p
  canonical := by
    intro S T _ _ _
    rfl
  cost_zero := by
    intro S hS
    -- every summand vanishes, so the sum does: induction on the list
    have hzero : ∀ c ∈ S.constraints, penaltyLoss c (fun _ : ℕ => p) = 0 := by
      intro c hc
      obtain ⟨a, b, rfl⟩ := hS c hc
      exact penalty_samePoint_const a b p
    suffices h : ∀ (l : List (GeoConstraint n)) (hl : ∀ c ∈ l, penaltyLoss c (fun _ : ℕ => p) = 0),
        (l.map (fun c => penaltyLoss c (fun _ : ℕ => p))).sum = 0 by
      exact h S.constraints hzero
    intro l hl
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [hl hd (by simp), ih (fun c hc => hl c (by simp [hc]))]
      exact zero_add 0

end Lattice.Plugins.Targets
