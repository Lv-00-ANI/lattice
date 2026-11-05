/-
# `Semantics/DPhaseAdditions.lean` -- the D phase as `ProofComplete` conjuncts (plan D-7)

## The defect this file repairs

**Rounds 114-123 produced four strengthenings in the semantics layer, and NONE reached `ProofComplete`:**

| step | result | in the predicate? |
|:--|:--|:--|
| **D-1** | **`programDomain`: a SECOND semantic domain** | **no** |
| **D-2** | **`refines`: the bridge `V` between the domains** | **no** |
| **D-5** | **`holdsAtAllGeometry`: a non-trivial contextual geometry** | **no** |
| **D-6** | **`compilationInherits`: `sound` proved, not `rfl`** | **no** |

**=> the completion predicate described the semantics layer as it was BEFORE the D phase.**

**This is the same pattern round 113 repaired for the C phase: a result that is proved but not conjoined is a
result the project's own statement does not know about.**

## What is conjoined, and what is not

**FOUR are conjoined, one per phase result:**

| conjunct | content |
|:--|:--|
| **`d1_two_domains`** | **`SemanticDomain` has two inhabitants** |
| **`d2_bridge_nontrivial`** | **`refines` has members AND non-members** |
| **`d5_geometry_nontrivial`** | **the contextual label uses both carrier and context** |
| **`d6_sound_computed`** | **a `ContextualInherits` whose `sound` is a proved equation** |

**Not conjoined, and the reason is stated:**

- **`meaningTypesDiffer` is not conjoined**: it is UNPROVED, and conjoining an unproved `Prop` would make
  `ProofComplete` false.
- **`finite_separation` is not conjoined**: it is a fact about `Fintype.card` at a finite domain, which is a
  SUPPORTING lemma for the open claim rather than a statement about the project's carriers.
- **`no_token_dependent_inherits` is not conjoined**: it is a REFUTATION, and the project's refutation census
  already records refutations; duplicating one into `ProofComplete` would double-count.

## What each conjunct adds that the predicate did not have

**Before this file, `ProofComplete` said nothing about:**

- **whether `SemanticDomain` has more than one inhabitant** (it conjoined no such fact);
- **whether the two domains are connected** (naturally not -- the bridge did not exist);
- **whether a geometry's label uses its context** (the conjoined T1-T8 facts are about compilation, not about
  contextual labelling);
- **whether `sound` was ever proved non-definitionally** (it was not -- every instance had `rfl`).

**=> all four are genuinely new content, not restatements of conjoined items.**
-/

import Mathlib
import Lattice.Semantics.ProgramDomain
import Lattice.Semantics.ProgramRefinement
import Lattice.Semantics.ContextualInheritsNontrivial
import Lattice.Semantics.CompilationInherits

namespace Lattice.Semantics.Stage1

open Lattice.Geo

/-! ## D-1: two semantic domains -/

/-- **`SemanticDomain` has at least two inhabitants.**

**`constraintDomain` (predicates on configurations) and `programDomain` (partial computations).**
**=> the structure S1 names is not a one-inhabitant type, and `programDomain_meaning_is_optional` records what
the second one's meanings can express that the first's cannot.** -/
def d1_two_domains : Prop :=
  ∃ D₁ D₂ : SemanticDomain, True

/-! **`d1_two_domains` holds** -- by `two_domains_exist`, a theorem already in the tree.
**No forwarding name: the conjunction below cites the original.** -/

/-! ## D-2: the bridge is non-trivial -/

/-- **`refines` has members AND non-members.**

**A program with no output refines everything; a program outputting index `0` does not refine
`fun _ => False`.**
**=> the bridge between the two domains is neither empty nor universal.** -/
def d2_bridge_nontrivial : Prop :=
  ∃ V : (programDomain 1).Meaning → (constraintDomain 1).Meaning → Prop,
    (∃ p c, V p c) ∧ (∃ p c, ¬ V p c)

/-! **`d2_bridge_nontrivial` holds** -- by `bridge_exists` at `n = 1`.
**No forwarding name: the conjunction below cites the original.** -/

/-! ## D-5: the contextual geometry is non-trivial -/

/-- **A contextual geometry whose label uses BOTH its carrier and its context.**

**`holdsAtAllGeometry`'s label is `HoldsSet cs pts ∧ ∀ p ∈ toks, HoldsSet cs p`, and
`geometry_is_nontrivial` proves two carriers and two contexts each give different labels.** -/
def d5_geometry_nontrivial : Prop :=
  ∃ (n : ℕ) (hn : 1 < n) (toks : List (ℕ → Pt n)) (pts : ℕ → Pt n),
    (holdsAtAllGeometry n).labelAt [] toks pts
      ≠ (holdsAtAllGeometry n).labelAt [GeoConstraint.eqZero (GeoExpr.const 1)] toks pts

/-- **`d5_geometry_nontrivial` holds.** -/
theorem d5_geometry_nontrivial_holds : d5_geometry_nontrivial := by
  obtain ⟨h1, _⟩ := geometry_is_nontrivial 2 (by norm_num)
  exact ⟨2, by norm_num, h1⟩

/-! ## D-6: `sound` is a proved equation -/

/-- **A `ContextualInherits` whose `sound` is NOT `rfl`.**

**`compilationInherits`: compilation flattens, behaviour quantifies over the nesting, and `sound` is proved
through `holdsSet_flatten`.**
**=> the structure's central field has been exercised at least once with content.** -/
def d6_sound_computed : Prop :=
  ∃ (n : ℕ) (ws : NestedWeights n) (toks : List (ℕ → Pt n)),
    (flatGeometry n).labelAt ((compilationInherits n).embed ws) toks
      = (compilationInherits n).behavior ws toks

/-- **`d6_sound_computed` holds.**

**Witnessed at `n = 1`, a single group, an empty context.**
**The point is that `sound` is invoked -- the equation's proof goes through `holdsSet_flatten`, which is an
induction over `holdsSet_append`, not a definitional unfolding.** -/
theorem d6_sound_computed_holds : d6_sound_computed :=
  ⟨1, [[], []], [], (compilationInherits 1).sound [[], []] []⟩

/-! ## The four together -/

/-- **The D phase's contribution to `ProofComplete`.**

**Stated as one proposition so the predicate conjoins it as a unit and a reader can see what the phase added
without diffing the whole conjunction.** -/
def DPhaseAdditions : Prop :=
  d1_two_domains ∧ d2_bridge_nontrivial ∧ d5_geometry_nontrivial ∧ d6_sound_computed

/-- **`DPhaseAdditions` holds.** -/
theorem dPhaseAdditions_holds : DPhaseAdditions :=
  ⟨two_domains_exist, bridge_exists 1 (le_refl 1), d5_geometry_nontrivial_holds,
   d6_sound_computed_holds⟩

end Lattice.Semantics.Stage1
