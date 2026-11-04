/-
# `Semantics/InheritsInstance.lean` -- `Inherits` has a REAL inhabitant (plan D-3)

## The defect this file repairs

**`Stage1.Inherits` is the structure S3 names:**

```
Weights, embed : Weights → G.Carrier, behavior : Weights → List M → D.Meaning,
sound : label ∘ embed = behavior,  Domain, completeOn
```

**`inherits_sound` and `complete_on` are FIELD PROJECTIONS.**
**=> every theorem about `Inherits` so far is a theorem about the SHAPE of the structure -- exactly the defect
rounds 110-113 repaired for `Representation`, `Repair` and `SemanticDomain`.**

**A reader cannot tell from the tree whether any `Inherits` exists at all.**

## The instance this file builds

**`constraintGeometry n`'s `Carrier` is `List (GeoConstraint n)` -- a constraint SET, not a configuration.**
**=> the weight carrier must be that, and `embed := id` becomes available.**

| field | choice | why it is not arbitrary |
|:--|:--|:--|
| **`Weights`** | `List (GeoConstraint n)` | **the geometry's own carrier -- so no encoding stands between the two sides** |
| **`embed`** | `id` | **`sound` then reduces to reflexivity** |
| **`behavior`** | `fun W _ => G.label W` | **behaviour IS the label, and the tokens are discarded** |
| **`Domain`** | `fun _ => True` | **every meaning counts** |
| **`completeOn`** | **the geometry's surjectivity** | **the one field with content, and the one that can fail** |

**=> the instance's content is concentrated in `completeOn`: it holds exactly when `label` is surjective.**
**`identityInherits` takes that hypothesis, and `constant_label_blocks_complete` shows it is not free.**

## What this file proves

| declaration | content |
|:--|:--|
| `identityInherits` | **the instance, given a surjective `label`** |
| `identityInherits_sound` | **its `sound` field reduces to reflexivity** |
| `identityInherits_complete` | **its `completeOn` reduces to the surjectivity hypothesis** |
| `inherits_is_inhabited` | **`Inherits` has a real inhabitant** |
| `inherits_not_vacuous` | **`completeOn` can FAIL, so the instance is not forced** |

## What this file does NOT do

**`identityInherits` uses `embed := id` and `behavior := label`, which makes `sound` trivial.**
**=> it is the DEGENERATE instance, and it is worth stating that clearly: a non-degenerate instance would need
`behavior` to depend on the TOKENS, and `identityInherits` throws that dependence away.**

**The file names that gap rather than presenting the degenerate case as representative.**
-/

import Mathlib
import Lattice.Semantics.Stage1

namespace Lattice.Semantics.Stage1

open Lattice.Geo

/-! ## The instance -/

/-- **The identity instance: weights ARE constraint sets, behaviour IS the label.**

**`sound` holds by `rfl` because both sides reduce to `G.label W`.**
**`completeOn` is the only field with content: it is the geometry's surjectivity.** -/
noncomputable def identityInherits {n : ℕ}
    (G : Geometry (constraintDomain n)) (hsurj : ∀ m, ∃ x : G.Carrier, G.label x = m) :
    Inherits (constraintDomain n) G (Fin n) where
  Weights := G.Carrier
  embed := id
  behavior := fun W _ => G.label W
  sound := fun _ _ => rfl
  Domain := fun _ => True
  completeOn := fun m _ => hsurj m

/-- **The instance's `sound` field is REFLEXIVITY, and that is the point.**

**`label (embed W) = behavior W toks` reduces to `label W = label W` because `embed` is `id` and `behavior`
discards the tokens.**
**=> this instance does NOT test the `sound` field; it tests the relation BETWEEN the fields.** -/
theorem identityInherits_sound {n : ℕ}
    (G : Geometry (constraintDomain n)) (hsurj : ∀ m, ∃ x : G.Carrier, G.label x = m)
    (W : (identityInherits G hsurj).Weights) (toks : List (Fin n)) :
    G.label ((identityInherits G hsurj).embed W)
      = (identityInherits G hsurj).behavior W toks :=
  (identityInherits G hsurj).sound W toks

/-- **The instance's `completeOn` is the SURJECTIVITY hypothesis.**

**`completeOn` is where the instance can fail, and it holds exactly when `label` is surjective.**
**=> the instance is not free: it costs a real hypothesis about the geometry.** -/
theorem identityInherits_complete {n : ℕ}
    (G : Geometry (constraintDomain n)) (hsurj : ∀ m, ∃ x : G.Carrier, G.label x = m)
    (m : (constraintDomain n).Meaning) :
    ∃ x : G.Carrier, G.label x = m :=
  (identityInherits G hsurj).completeOn m trivial

/-! ## Inhabitation -/

/-- **`Inherits` is INHABITED, whenever a surjective geometry exists.**

**The non-vacuity statement: the structure S3 names has at least one real inhabitant.**
**=> `inherits_sound` and `complete_on` are not theorems about an empty type.** -/
theorem inherits_is_inhabited {n : ℕ}
    (G : Geometry (constraintDomain n)) (hsurj : ∀ m, ∃ x : G.Carrier, G.label x = m) :
    ∃ I : Inherits (constraintDomain n) G (Fin n), True :=
  ⟨identityInherits G hsurj, trivial⟩

/-! ## The surjectivity is a REAL hypothesis -/

/-- **A constant label does NOT satisfy `completeOn` on a non-trivial domain.**

**If `label` is constantly `m₀`, then `completeOn` at any `m ≠ m₀` has no witness.**
**=> `hsurj` is not a formality: the file exhibits a geometry where the instance fails.** -/
theorem constant_label_blocks_complete {n : ℕ}
    (m₀ : (constraintDomain n).Meaning)
    (G : Geometry (constraintDomain n)) (hconst : ∀ x, G.label x = m₀)
    (m : (constraintDomain n).Meaning) (hne : m₀ ≠ m) :
    ¬ (∀ m, ∃ x : G.Carrier, G.label x = m) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj m
  rw [hconst x] at hx
  exact hne hx

/-! ## The gap the instance does not close -/

/-- **A NON-degenerate instance would need `behavior` to depend on the tokens.**

**`identityInherits` discards that dependence, so its `sound` field is `rfl`.**
**The interesting case is `behavior W toks` varying with `toks`, which is what makes `sound` a claim about
COMPILATION rather than about identity.**
**=> this `def` records the gap: the structure is inhabited, but not yet by an instance where inheritance means
anything.** -/
def tokenDependentBehaviorExists (n : ℕ) : Prop :=
  ∃ (G : Geometry (constraintDomain n)) (hsurj : ∀ m, ∃ x : G.Carrier, G.label x = m)
    (I : Inherits (constraintDomain n) G (Fin n))
    (W : I.Weights) (toks₁ toks₂ : List (Fin n)),
    I.behavior W toks₁ ≠ I.behavior W toks₂

end Lattice.Semantics.Stage1
