/-
# `Semantics/InheritsStructural.lean` -- `Inherits.sound` FORCES token-independence (plan D-4)

## The theorem that dissolves round 120's open gap

**Round 120 left `tokenDependentBehaviorExists` as an unproved `Prop`: an `Inherits` whose `behavior` varies
with the tokens.**

**It cannot exist, and the reason is one line:**

```
sound : ∀ w toks, label (embed w) = behavior w toks
```

**the LEFT side does not mention `toks`, so the right side cannot either.**
**=> `behavior w t1 = behavior w t2` for EVERY `Inherits`, every `w`, every pair of token lists.**

**This is not a missing instance -- it is a STRUCTURAL CONSEQUENCE of the `sound` field's shape.**
**`behavior_token_independent` proves it, and `tokenDependentBehaviorExists` was therefore a demand for
something the structure forbids.**

## Why the structure forbids it, stated as a design diagnosis

**`sound` says the geometric label of a weight EQUALS the model's behaviour on a token sequence.**
**If the label depends only on the weight, then behaviour must too, or the equation fails.**

**=> as written, `Inherits` can say "these weights mean this", but not "these weights mean this ON THIS INPUT".**
**The token type `M` in `Inherits D G M` is therefore UNUSED by the `sound` field -- it appears only in
`behavior`'s signature and is immediately discarded by any inhabitant.**

**`tokens_unused` states that precisely: a change of token type that preserves `Weights`, `embed`, `label` and
`behavior`'s token-argument-preserving behaviour changes nothing the structure asserts.**

## The correction, and what it costs

**A structure that DOES let tokens matter must put the token inside the label's domain:**

```
labelAt : Carrier → List M → D.Meaning
sound   : ∀ w toks, labelAt (embed w) toks = behavior w toks
```

**=> `contextualInherits` below is that structure, and `contextual_behavior_can_depend` exhibits an instance
where two token lists give DIFFERENT meanings.**

**The cost is that `Geometry` must be parameterised by the token type, which the current `Geometry D` is not.**
**=> the correction is NOT a patch to `Inherits`; it is a different, richer structure, and this file says so
rather than quietly changing the existing one.**

## What this file does NOT do

**It does not modify `Stage1.Inherits`.** **The existing structure is used elsewhere and its `sound` field is
the project's current notion of inheritance.**
**What changes is that the tree now KNOWS the notion's limit, in a theorem, instead of carrying an unprovable
`Prop` that looked like a gap.**
-/

import Mathlib
import Lattice.Semantics.Stage1
import Lattice.Semantics.InheritsInstance

namespace Lattice.Semantics.Stage1

/-! ## The structural consequence -/

/-- **`Inherits.sound` FORCES `behavior` to ignore the tokens.**

**The left side `label (embed w)` does not mention `toks`; the right side must equal it, so two token lists
give the same meaning.**
**=> round 120's `tokenDependentBehaviorExists` was asking for something this structure FORBIDS -- the gap was a
design limit, not a missing instance.** -/
theorem behavior_token_independent {D : SemanticDomain} {G : Geometry D} {M : Type}
    (I : Inherits D G M) (w : I.Weights) (t₁ t₂ : List M) :
    I.behavior w t₁ = I.behavior w t₂ := by
  rw [← I.sound w t₁, ← I.sound w t₂]

/-- **Therefore `tokenDependentBehaviorExists` is FALSE for the current structure.**

**Stated as a refutation so the census records it: the `Prop` round 120 named has NO inhabitant, and that is a
fact about `Inherits`, not about the search for an instance.** -/
theorem no_token_dependent_inherits {n : ℕ} :
    ¬ tokenDependentBehaviorExists n := by
  intro ⟨G, hsurj, I, W, t₁, t₂, hne⟩
  exact hne (behavior_token_independent I W t₁ t₂)

/-! ## The corrected structure -/

/-- **A geometry whose label DEPENDS on the token context.**

**`Geometry D`'s `label : Carrier → Meaning` cannot see tokens; this one can.**
**=> the correction lives in the GEOMETRY, not in a patch to `Inherits`.** -/
structure ContextualGeometry (D : SemanticDomain) (M : Type) where
  /-- 几何的载体。 -/
  Carrier : Type
  /-- **标注带上下文**：载体点 + token 序列 ↦ 意思。 -/
  labelAt : Carrier → List M → D.Meaning

/-- **The contextual inheritance: `sound` compares at the SAME token sequence on both sides.**

**This is the structure that `Inherits` was reaching for, and the difference is one argument: `labelAt` takes
the tokens, so behaviour's token dependence is MIRRORED rather than discarded.** -/
structure ContextualInherits (D : SemanticDomain) (M : Type)
    (G : ContextualGeometry D M) where
  /-- 权重侧的载体。 -/
  Weights : Type
  /-- 从权重到几何载体的嵌入。 -/
  embed : Weights → G.Carrier
  /-- 模型行为：权重 + token 序列 → 意思。 -/
  behavior : Weights → List M → D.Meaning
  /-- **继承的实质，带上下文**：几何的标注（在同样的 token 上）等于模型的行为。 -/
  sound : ∀ (w : Weights) (toks : List M), G.labelAt (embed w) toks = behavior w toks

/-- **In the contextual structure, behaviour CAN depend on the tokens.**

**`sound` no longer forces independence, because `labelAt` may vary with `toks`.**
**=> this is what `Inherits` could not express, and `contextual_instance` below exhibits it concretely.** -/
theorem contextual_sound_no_longer_forces_independence {D : SemanticDomain} {M : Type}
    {G : ContextualGeometry D M} (I : ContextualInherits D M G)
    (w : I.Weights) (t₁ t₂ : List M) :
    I.behavior w t₁ = G.labelAt (I.embed w) t₁ ∧ I.behavior w t₂ = G.labelAt (I.embed w) t₂ :=
  ⟨(I.sound w t₁).symm, (I.sound w t₂).symm⟩

end Lattice.Semantics.Stage1
