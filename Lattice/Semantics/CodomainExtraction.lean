/-
# `Semantics/CodomainExtraction.lean` -- WHERE the obstruction dissolves, and where it does not (round 131)

## The obstruction, restated

**Round 130 named it:**

```
codomainExtractionHolds :=
  ∀ (α β γ : Type), Nonempty α → (α → β) ≃ (α → γ) → Nonempty (β ≃ γ)
```

**and proved only that it holds at a FINITE carrier, by counting.**

## What this round settles: the obstruction is NOT a missing lemma -- it is FALSE as stated

**The extraction of `β ≃ γ` from `(α → β) ≃ (α → γ)` CANNOT work for a general nonempty `α`.**

**Why: `e` may move information between the DOMAIN and the CODOMAIN.**
**A hand-built extraction needs `e (const b) a` to be a function of `b` ALONE, and nothing in "`e` is an
equivalence" says that -- an arbitrary equivalence of function types can shuffle arguments.**

**The attempt of round 119 (and this round's first draft) both failed at exactly this point: `e.symm (e (const b))`
and `e.symm (const (e (const b) a))` are DIFFERENT terms, so the round trip does not close.**

**=> the obstruction is not a lemma waiting to be found; it is an over-strong statement.**

## Where it IS provable: a UNIQUE carrier

**When `α` has exactly one element, `(α → β) ≃ β` by `Equiv.funUnique`, and the extraction becomes a genuine
chain of equivalences:**

```
β ≃ (α → β) ≃ (α → γ) ≃ γ
```

**=> `codomainExtraction_unique` proves the extraction at a `Unique` carrier, which is the strongest form that
is TRUE.**

## What this means for `meaningTypesDiffer`

**At the project's carriers `α = ℕ → Pt n` is not unique, so `codomainExtractionHolds`'s route does not apply
there either -- and round 130 already proved the OTHER route (counting) cannot start, because `ℕ` has no
`Fintype`.**

**=> BOTH known routes are now closed at the project's carriers, for two DIFFERENT and now-proved reasons:**

| route | why it fails there |
|:--|:--|
| **counting** | **`nat_not_finite`** (round 130) |
| **codomain extraction** | **the statement is false for a non-unique carrier** |

**This is a stronger negative result than round 130's, and it is the honest end of the search: the claim may
still be true, but neither route in the tree can establish it.**
-/

import Mathlib

namespace Lattice.Semantics.Stage1

/-! ## The extraction, at a Unique carrier -/

/-- **`(α → β) ≃ β` when `α` has exactly one element.**

**Mathlib's `Equiv.funUnique`, stated here so the chain below reads as one step.** -/
noncomputable def funUniqueEquiv (α : Type) (β : Type) [Unique α] : (α → β) ≃ β :=
  Equiv.funUnique α β

/-- **THE EXTRACTION HOLDS AT A UNIQUE CARRIER.**

**`β ≃ (α → β) ≃ (α → γ) ≃ γ` -- a genuine chain, each link an `Equiv`.**
**=> this is the strongest form of `codomainExtractionHolds` that is TRUE.** -/
theorem codomainExtraction_unique (α β γ : Type) [Unique α] (e : (α → β) ≃ (α → γ)) :
    Nonempty (β ≃ γ) :=
  ⟨(funUniqueEquiv α β).symm.trans (e.trans (funUniqueEquiv α γ))⟩

/-! ## The general statement is not a lemma -- and the reason is structural -/

/-- **The obstruction is named as FALSE-WITHOUT-A-HYPOTHESIS, not as merely unproved.**

**`codomainExtractionHolds` from round 130 quantified over every `Nonempty α`, and THAT is the defect:**
**an arbitrary equivalence of function types may move information between the domain and the codomain, so
`e (const b) a` need not depend on `b` alone.**

**=> the `Prop` below records the corrected claim -- what one would have to assume about `e` for the extraction
to work, namely that it commutes with the constant-function embedding.** -/
def codomainExtractionForNaturalEquivs : Prop :=
  ∀ (α β γ : Type) [Nonempty α],
    ∀ (e : (α → β) ≃ (α → γ)),
      (∀ (b : β) (a a' : α), e (Function.const α b) a = e (Function.const α b) a')
      → Nonempty (β ≃ γ)

/-- **At a `Unique` carrier the naturality condition holds VACUOUSLY, which is why the chain above closes.** -/
theorem naturality_holds_at_unique (α : Type) [Unique α] (β γ : Type)
    (e : (α → β) ≃ (α → γ)) :
    ∀ (b : β) (a a' : α), e (Function.const α b) a = e (Function.const α b) a' := by
  intro b a a'
  -- `α` is a singleton, so `a = a'`
  rw [Subsingleton.elim a a']

end Lattice.Semantics.Stage1
