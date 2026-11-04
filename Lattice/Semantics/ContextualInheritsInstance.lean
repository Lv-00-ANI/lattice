/-
# `Semantics/ContextualInheritsInstance.lean` -- the corrected structure has a NON-DEGENERATE instance (D-4b)

## What round 121a established

**`Inherits.sound` forces `behavior` to ignore the tokens (`behavior_token_independent`), so round 120's
`tokenDependentBehaviorExists` had NO inhabitant -- the gap was a DESIGN LIMIT.**

**`ContextualGeometry` / `ContextualInherits` in the same file is the correction: `labelAt` takes the token
sequence, so behaviour's token dependence is MIRRORED rather than discarded.**

## Why a correction needs an instance, not only a structure

**A structure that CAN express token dependence is worth nothing unless one does.**
**=> this file builds `lengthContextualInherits`: a contextual inheritance where behaviour reads the token list
and two DIFFERENT lists give DIFFERENT meanings.**

## The instance

**Carrier: `List M` (the token sequence itself).**
**`labelAt toks toks' := toks'` -- the geometry's label is the context it is evaluated in.**
**`Weights := Unit`, `embed := fun _ => []`, `behavior := fun _ toks => toks`.**

**=> `sound` reads `labelAt [] toks = behavior () toks`, i.e. `toks = toks`, which is `rfl`.**
**And `behavior () [m] = [m] ≠ [] = behavior () []`, so the dependence is REAL.**

## What this file proves

| declaration | content |
|:--|:--|
| `lengthContextualGeometry` | **the contextual geometry** |
| `lengthContextualInherits` | **its contextual inheritance** |
| `contextual_behavior_depends` | **two token lists give DIFFERENT meanings** |
| `contextual_inherits_is_nondegenerate` | **the instance is not the identity case** |
| `correction_is_witnessed` | **the structure's expressive gain is REALISED, not merely allowed** |

## What this file does NOT do

**`lengthContextualInherits`'s geometry is TRIVIAL -- `labelAt` ignores the carrier and returns the context.**
**=> it witnesses EXPRESSIVITY, not correspondence: nothing here says the geometry MEANS something.**
**A non-trivial contextual inheritance would need `labelAt` to compute a meaning from the carrier and the
context together, which is the real work and is not in this file.**
-/

import Mathlib
import Lattice.Semantics.InheritsStructural

namespace Lattice.Semantics.Stage1

/-! ## A semantic domain whose meanings ARE token lists

**`constraintDomain`'s `Meaning` is `(ℕ → Pt n) → Prop`, which cannot hold a token list.**
**=> the instance needs its own domain, and `listDomain` is the minimal one: `Meaning := List M`.**
**That is not a dodge -- a meaning that IS a sequence is exactly what "behaviour varies with context" means.** -/

/-- **A semantic domain whose meanings are token lists.**

**`equiv` is list equality, so two contexts are the same meaning exactly when they agree elementwise.**
**=> `refl` is `rfl` and the only content is that this IS a `SemanticDomain`.** -/
def listDomain (M : Type) : SemanticDomain where
  Meaning := List M
  equiv := fun a b => a = b
  refl := fun _ => rfl

/-- **`listDomain`'s `equiv` is symmetric.** -/
theorem listDomain_symmetric (M : Type) : (listDomain M).Symmetric := by
  intro a b h
  exact h.symm

/-- **`listDomain`'s `equiv` is transitive.** -/
theorem listDomain_transitive (M : Type) : (listDomain M).Transitive := by
  intro a b c hab hbc
  exact hab.trans hbc

/-! ## The contextual geometry -/

/-- **A geometry whose label IS its context.**

**`labelAt _ toks := toks`: the carrier point carries nothing, and the meaning is exactly the token sequence.
**=> surjective on meanings by construction, which is enough to witness the dependence.** -/
def listContextualGeometry (M : Type) : ContextualGeometry (listDomain M) M where
  Carrier := Unit
  labelAt := fun _ toks => toks

/-- **The contextual inheritance: behaviour reads the tokens.**

**`Weights := Unit`, `embed := fun _ => ()`, `behavior := fun _ toks => toks`.** -/
def listContextualInherits (M : Type) :
    ContextualInherits (listDomain M) M (listContextualGeometry M) where
  Weights := Unit
  embed := fun _ => ()
  behavior := fun _ toks => toks
  sound := fun _ _ => rfl

/-! ## The dependence is REAL -/

/-- **Two different token lists give different meanings.**

**`behavior () [m] = [m]` and `behavior () [] = []`, and `[m] ≠ []`.**
**=> this is exactly what `Inherits` forbade and `ContextualInherits` allows.** -/
theorem contextual_behavior_depends (M : Type) (m : M) :
    (listContextualInherits M).behavior () [m]
      ≠ (listContextualInherits M).behavior () [] := by
  intro h
  exact List.cons_ne_nil m [] h

/-- **The instance is NON-DEGENERATE: behaviour actually uses its argument.**

**In `identityInherits`, `sound` was `rfl` because `behavior` discarded the tokens.**
**Here `sound` is `rfl` because `labelAt` returns the same context -- but unlike the identity case,
`behavior` USES its argument, so this theorem is provable.**
**=> the structure's expressive gain is REALISED, not merely allowed.** -/
theorem contextual_inherits_is_nondegenerate (M : Type) (m : M) :
    ∃ t₁ t₂ : List M, (listContextualInherits M).behavior () t₁
      ≠ (listContextualInherits M).behavior () t₂ :=
  ⟨[m], [], contextual_behavior_depends M m⟩

/-- **The correction is WITNESSED.**

**`Inherits` forbids token dependence (`no_token_dependent_inherits`); `ContextualInherits` admits it.**
**=> the two theorems together state what the correction buys.** -/
theorem correction_is_witnessed (M : Type) (m : M) :
    (∃ t₁ t₂ : List M, (listContextualInherits M).behavior () t₁
        ≠ (listContextualInherits M).behavior () t₂)
      ∧ ¬ tokenDependentBehaviorExists 0 :=
  ⟨contextual_inherits_is_nondegenerate M m, no_token_dependent_inherits⟩

end Lattice.Semantics.Stage1
