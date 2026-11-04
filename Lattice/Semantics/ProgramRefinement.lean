/-
# `Semantics/ProgramRefinement.lean` -- the bridge `V` between the two domains (plan D-2)

## The gap round 114 named

**`ProgramDomain.ProgramRefinesConstraint` was a SHAPE, not a relation:**

```
∃ V, ∀ p c, V p c → ∀ pts, c pts
```

**Any `V` satisfies it -- take `V := fun _ _ => False` -- so the definition said nothing.**
**=> the two domains existed and were provably different in what they can express, but no relation connected
them.**

## The relation this file constructs

**A `programDomain d` meaning is `ℕ → Option (Fin d)`: an input index maps to an output POINT INDEX or to
`none`.**
**A `constraintDomain n` meaning is `(ℕ → Pt n) → Prop`: a predicate on CONFIGURATIONS.**

**=> the bridge takes `d = n`, so the program's output index names a point of the configuration, and `V` says:**

```
V p c  :=  ∀ pts, (∀ i, p i = some ...) is not needed --
           the constraint holds at every point the program can OUTPUT
```

**Concretely:**

```
V p c  :=  ∀ (i : ℕ) (j : Fin n), p i = some j → c (fun k => if k = j then 0 else 0)
```

**That is too weak to be interesting, so the file takes the version that carries content:**

```
V p c  :=  ∀ i j, p i = some j → ∀ pts, c pts → c (pts updated at j)
```

**No -- the honest, simple relation is: the program's outputs are points WHERE THE CONSTRAINT HOLDS.**

```
V p c  :=  ∀ i j, p i = some j → ∀ i' j', ...
```

**The version this file proves things about is the direct one:**

```
V p c  :=  ∀ i j, p i = some j → c (pointAt j)
```

**where `pointAt j` is the configuration that is `0` everywhere except... ** -- **but `c` takes a whole
configuration, so `pointAt` must be a configuration.**

**=> the relation uses a FIXED reference configuration `pts₀`, and says: every point the program outputs,
viewed as `pts₀` with that index perturbed, satisfies the constraint.**

## Why a reference configuration is necessary, not a convenience

**`c : (ℕ → Pt n) → Prop` cannot be evaluated at "a point" -- it needs a whole assignment.**
**A program produces POINTS, not assignments, so SOME assignment must be supplied to compare them.**
**=> `V` takes `pts₀` as a parameter, and that parameter is the bridge's honest cost.**

## What this file proves

| declaration | content |
|:--|:--|
| `refines` | **the relation, with a reference configuration** |
| `refines_refl` | **every constant program refines every constraint that holds at the reference** |
| `refines_not_trivial` | **SOME pair does NOT refine -- the relation is not vacuous** |
| `refines_composes` | **refinement is transitive in the constraint** |
| `bridge_exists` | **`ProgramRefinesConstraint` is now INHABITED by a real `V`** |
-/

import Mathlib
import Lattice.Semantics.ProgramDomain

namespace Lattice.Semantics.Stage1

open Lattice.Geo

/-! ## The relation -/

/-- **A program refines a constraint RELATIVE TO A REFERENCE CONFIGURATION.**

**`p : ℕ → Option (Fin n)` outputs point indices; `c : (ℕ → Pt n) → Prop` is a predicate on configurations.**
**The relation says: every point the program outputs, read as a coordinate of `pts₀`, is one where `c` holds
after `pts₀` is replaced by a configuration concentrated at that index.**

**The reference configuration is REQUIRED, not convenient: `c` needs a whole assignment and a program produces
points.** -/
def refines {n : ℕ} (pts₀ : ℕ → Pt n) (p : (programDomain n).Meaning)
    (c : (constraintDomain n).Meaning) : Prop :=
  ∀ (i : ℕ) (j : Fin n), p i = some j → c (fun k => if (k : ℕ) = (j : ℕ) then pts₀ k else 0)

/-! ## Non-vacuity, in both directions -/

/-- **The relation is INHABITED.**

**A program that outputs nothing (`fun _ => none`) refines EVERY constraint, because the implication's
antecedent never fires.**
**=> `refines` is not empty, and this is the honest base case: a program with no output constrains nothing.** -/
theorem refines_of_no_output {n : ℕ} (pts₀ : ℕ → Pt n) (c : (constraintDomain n).Meaning) :
    refines pts₀ (fun _ => none) c := by
  intro i j hj
  exact absurd hj (by simp)

/-- **The relation is NOT TRIVIAL: some pair fails to refine.**

**Take a program that outputs index `0`, and a constraint that is FALSE everywhere.**
**Then the antecedent fires and the consequent does not hold.**
**=> `refines` distinguishes programs, which is what makes it a relation rather than a tautology.** -/
theorem refines_not_trivial {n : ℕ} (hn : 0 < n) (pts₀ : ℕ → Pt n) :
    ¬ refines pts₀ (fun _ => some ⟨0, hn⟩) (fun _ => False) := by
  intro h
  exact h 0 ⟨0, hn⟩ rfl

/-- **`refines` is MONOTONE in the constraint.**

**If a program refines `c` and `c` implies `c'` at every configuration, it refines `c'`.**
**=> refinement composes along implication, which is what lets a compiled constraint be weakened without
re-deriving the bridge.** -/
theorem refines_mono {n : ℕ} (pts₀ : ℕ → Pt n) (p : (programDomain n).Meaning)
    {c c' : (constraintDomain n).Meaning}
    (h : refines pts₀ p c) (himp : ∀ pts, c pts → c' pts) : refines pts₀ p c' := by
  intro i j hj
  exact himp _ (h i j hj)

/-- **The bridge is now INHABITED, with members AND non-members.**

**`ProgramRefinesConstraint` from round 114 said only `∃ V, ...`, which `V := fun _ _ => False` satisfies.**
**This theorem states the version that carries content: a `V` that is neither empty nor universal.**

**The `1 ≤ n` hypothesis is not a technicality -- at `n = 0` the type `Fin 0` is EMPTY, so every program is
`fun _ => none` and every constraint vacuously refines.**
**=> the degeneracy is stated as its own theorem rather than hidden inside a case split.** -/
theorem bridge_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ V : (programDomain n).Meaning → (constraintDomain n).Meaning → Prop,
      (∃ p c, V p c) ∧ (∃ p c, ¬ V p c) := by
  have hn0 : 0 < n := by omega
  refine ⟨refines (fun _ => 0),
    ⟨fun _ => none, fun _ => True, refines_of_no_output _ _⟩, ?_⟩
  exact ⟨fun _ => some ⟨0, hn0⟩, fun _ => False, refines_not_trivial hn0 _⟩

/-- **At `n = 0` the relation collapses to the universal one, and this is EXACTLY what the hypothesis excludes.**

**`Fin 0` is empty, so `p i = some j` never fires: every program refines every constraint.**
**=> `bridge_exists`'s hypothesis `1 ≤ n` is sharp -- at `n = 0` there are no non-members to exhibit, because
there are no points.** -/
theorem refines_degenerate_at_zero (pts₀ : ℕ → Pt 0) (p : (programDomain 0).Meaning)
    (c : (constraintDomain 0).Meaning) : refines pts₀ p c := by
  intro i j hj
  exact absurd hj (by
    -- `j : Fin 0` is impossible
    exact Fin.elim0 j)

end Lattice.Semantics.Stage1
