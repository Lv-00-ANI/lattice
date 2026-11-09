/-
# `Semantics/CompilationInherits.lean` -- `sound` is NOT `rfl`: the compilation gap (plan D-6)

## The gap rounds 120-122 left

**Every `Inherits` / `ContextualInherits` in the tree has `sound` proved by `rfl`, because every instance's
`behavior` IS the geometry's label.**

**=> the structure can say "these weights carry this meaning", but no theorem said that a COMPUTED behaviour
agrees with a geometric label.**
**That agreement is what `sound` is FOR, and it had never been exercised.**

## The instance that exercises it

**`Weights := List (List (GeoConstraint n))` -- a weight is a NESTED constraint list.**
**`embed := List.flatten` -- compilation FLATTENS the nesting.**

**`behavior` does NOT call `labelAt (flatten ws)`.**
**It computes, from `ws` directly, the predicate "every constraint in every GROUP holds at `pts` and at every
configuration in the context".**
**That is a different TERM: it quantifies over the nested structure and never mentions `flatten`.**

**=> `sound` becomes an equation between two independently-defined predicates, and its proof goes through
`holdsSet_flatten`, which is `holdsSet_append` applied inductively -- a library lemma about a DIFFERENT
operation, not definitional unfolding.**

## The bridge lemma

```
holdsSet_flatten : HoldsSet (flatten ws) pts  ↔  ∀ g ∈ ws, HoldsSet g pts
```

**Proved by induction on `ws`, with `holdsSet_append` doing the cons case.**
**=> the equation `sound` asserts is TRUE for a reason, and the reason is stated as its own theorem.**

## What this file does NOT do

**`embed` flattens; it does not produce floats.**
**=> "compilation" here means STRUCTURE-PRESERVING TRANSFORMATION, not numeric training.**
**A reader could otherwise take `sound` for a statement about gradient descent, and it is not.**
**The file says so rather than relying on the word "compilation" to carry the distinction.**
-/

import Mathlib
import Lattice.Semantics.InheritsStructural
import Lattice.Semantics.ContextualInheritsNontrivial
import Lattice.Reference.Geometry.Constraints.ConstraintSet

namespace Lattice.Semantics.Stage1

open Lattice.Geo
open Lattice.Geo.ConstraintSet

/-! ## The geometry: label reads a FLAT constraint list -/

/-- **A geometry whose carrier is a flat constraint list.**

**The label at `(cs, toks)` is "`cs` holds at `pts` and at every configuration in `toks`".**
**=> the carrier and the compilation's OUTPUT have the same type, which is what makes `embed` typecheck.** -/
def flatGeometry (n : ℕ) : ContextualGeometry (constraintDomain n) (ℕ → Pt n) where
  Carrier := List (GeoConstraint n)
  labelAt := fun cs toks => fun pts => HoldsSet cs pts ∧ ∀ p ∈ toks, HoldsSet cs p

/-! ## The compilation and the independent behaviour -/

/-- **The weight carrier: a NESTED constraint list.** -/
abbrev NestedWeights (n : ℕ) := List (List (GeoConstraint n))

/-- **Compilation FLATTENS the nesting.** -/
def flattenCompile {n : ℕ} (ws : NestedWeights n) : List (GeoConstraint n) :=
  ws.flatten

/-- **Behaviour, computed WITHOUT mentioning `flatten`.**

**It quantifies over the nested structure directly: a configuration is accepted when every constraint in every
GROUP holds, and the context's configurations are accepted likewise.** -/
def nestedBehavior {n : ℕ} (ws : NestedWeights n) (toks : List (ℕ → Pt n)) :
    (constraintDomain n).Meaning :=
  fun pts => (∀ g ∈ ws, HoldsSet g pts) ∧ (∀ p ∈ toks, ∀ g ∈ ws, HoldsSet g p)

/-! ## The bridge lemma -/

/-- **`HoldsSet` on a flattened list is the conjunction over the groups.**

**Proved by induction on `ws`, with `holdsSet_append` for the cons case.**
**=> this is why `sound` is not `rfl`: the equation holds for a REASON, and the reason is about `++`, not about
definitional unfolding.** -/
theorem holdsSet_flatten {n : ℕ} (ws : NestedWeights n) (pts : ℕ → Pt n) :
    HoldsSet (flattenCompile ws) pts ↔ ∀ g ∈ ws, HoldsSet g pts := by
  induction ws with
  | nil =>
    simp only [flattenCompile, List.flatten_nil, HoldsSet, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons g gs ih =>
    -- `(g :: gs).flatten = g ++ gs.flatten`
    have hstep : flattenCompile (g :: gs) = g ++ flattenCompile gs := by
      simp [flattenCompile]
    rw [hstep, holdsSet_append, ih]
    -- `∀ a ∈ g :: gs, P a` unfolds to `P g ∧ ∀ a ∈ gs, P a`
    simp only [List.mem_cons, forall_eq_or_imp]

/-! ## The instance -/

/-- **The compilation instance: `sound` is an EQUATION between two independently-defined predicates.**

**`embed := flattenCompile` and `behavior := nestedBehavior`; the proof uses `holdsSet_flatten` twice.**
**=> no `rfl` anywhere: the two sides are different terms and the bridge is a lemma.** -/
def compilationInherits (n : ℕ) :
    ContextualInherits (constraintDomain n) (ℕ → Pt n) (flatGeometry n) where
  Weights := NestedWeights n
  embed := flattenCompile
  behavior := nestedBehavior
  sound := by
    intro ws toks
    funext pts
    show (HoldsSet (flattenCompile ws) pts ∧ ∀ p ∈ toks, HoldsSet (flattenCompile ws) p)
      = ((∀ g ∈ ws, HoldsSet g pts) ∧ ∀ p ∈ toks, ∀ g ∈ ws, HoldsSet g p)
    rw [holdsSet_flatten]
    congr 1
    -- both sides quantify `p ∈ toks`; the bodies agree by `holdsSet_flatten`
    apply propext
    constructor
    · intro h p hp
      exact (holdsSet_flatten ws p).mp (h p hp)
    · intro h p hp
      exact (holdsSet_flatten ws p).mpr (h p hp)

/-! ## The `sound` field carries content -/

/-- **The two sides of `sound` are computed differently.**

**`embed ws` flattens; `nestedBehavior ws` does not.**
**=> the equation `sound` asserts is not a restatement, and `holdsSet_flatten` is the reason it holds.** -/
theorem sound_is_not_definitional (n : ℕ) (ws : NestedWeights n) (toks : List (ℕ → Pt n)) :
    (flatGeometry n).labelAt ((compilationInherits n).embed ws) toks
      = (compilationInherits n).behavior ws toks :=
  (compilationInherits n).sound ws toks

end Lattice.Semantics.Stage1
