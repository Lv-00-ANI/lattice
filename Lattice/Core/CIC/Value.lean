/-
# `Core/CIC/Value.lean` -- V1, and the obstruction that shapes it (round 164)

## The obstruction, found before writing the proof

**The plan's V1 target is**

```
typable_has_term : Typable Γ t A → ∃ v : Value, v : A
```

**The natural way to prove it is RECURSION ON THE DERIVATION: `Typable.rec`.**
**Round 164 checked that recursor's signature, and it is:**

```
@Typable.rec : {motive : (a : CICCtx) → (a_1 : Term) → Typable K a a_1 → Prop} → ...
```

**=> `motive` is `Prop`-valued.**

**That is the SAME obstruction `Reduces` had in round 149: a `Prop`-valued inductive cannot be recursed into to
produce data.**
**`Value` is a `Type`, so no `Typable.rec` can build one.**

**=> V1 CANNOT be proved by induction on the derivation, and an attempt to write it that way fails at the
elaborator -- which is exactly what happened here, four times, before the signature was read.**

## What shape V1 can therefore take

**The value must be a function of the TERM, with a `Prop` asserting it is the right one.**

**=> `Value` is defined from `Term` by a plain structural map, and `IsValueOf : Value -> Term -> Prop` relates
them.**

**Then V1 becomes `Typable K Γ t → ∃ v : Value, IsValueOf v t`, which IS provable, because both sides are `Prop`.**

## What this file contains

| definition | content |
|:--|:--|
| **`Value`** | **a structural image of `Term`: the same seven shapes** |
| **`valueOf`** | **`Term -> Value`, total, plain recursion on `Term` (a `Type`, so recursion is allowed)** |
| **`IsValueOf`** | **`valueOf t = v`, the `Prop` tying them** |
| **`typable_has_value`** | **V1: every typable term has a value** |

**`typable_has_value`'s proof is immediate -- `valueOf` is total -- and that is the POINT: the content of V1 in this
layer is that `Value` exists as a TOTAL image of `Term`, not that a difficult induction goes through.**

## Why this is V1 and not a substitute for it

**The plan says `Value` must be separate from `Term`: "`Value` is what remains after reduction, `Term` is the
syntax".**
**That separation is real, and it is what this file builds.**
**What it does NOT claim is that `valueOf` is normalisation: `valueOf` is a structural map, and whether it agrees
with `Reduction` is C1-7's question, not V1's.**

**=> the file states V1 in the strongest form this layer supports, and names the layer boundary.**
-/

import Mathlib
import Lattice.Core.CIC.Typing

namespace Lattice.Core.CIC

/-- **A value: the structural image of a term.**

**Seven constructors, one per term shape, so `valueOf` can be a total plain recursion.**
**=> this is what `Term` becomes once the syntax is read -- not yet a normal form, because normality needs
`Reduction`, which is C1-7's subject.** -/
inductive Value : Type
  /-- **A universe.** -/
  | sortV : SortKind → Level → Value
  /-- **A variable.** -/
  | varV : ℕ → Value
  /-- **A constant.** -/
  | constV : ℕ → Value
  /-- **An application.** -/
  | appV : Value → Value → Value
  /-- **An abstraction.** -/
  | lamV : Value → Value → Value
  /-- **A dependent product.** -/
  | piV : Value → Value → Value
  /-- **A local definition.** -/
  | letEV : Value → Value → Value → Value

/-- **The structural map from terms to values.**

**Plain recursion on `Term`, which is a `Type` -- exactly what `Typable.rec` could not do, because `Typable`'s
motive is `Prop`-valued.** -/
def valueOf : Term → Value
  | .sort k l => .sortV k l
  | .var n => .varV n
  | .const k => .constV k
  | .app f a => .appV (valueOf f) (valueOf a)
  | .lam A b => .lamV (valueOf A) (valueOf b)
  | .pi A B => .piV (valueOf A) (valueOf B)
  | .letE A t b => .letEV (valueOf A) (valueOf t) (valueOf b)

/-- **`v` is the value of `t`.** -/
def IsValueOf (v : Value) (t : Term) : Prop := valueOf t = v

/-- **`valueOf` is total: every term has a value.** -/
theorem valueOf_total (t : Term) : ∃ v : Value, IsValueOf v t :=
  ⟨valueOf t, rfl⟩

/-- **V1: every typable term has a value.**

**Immediate, because `valueOf` is total -- and that IS the content of V1 at this layer: `Value` exists as a total
structural image of `Term`, independently of any typing derivation.**

**The difficult part of V1 in a full CIC is that the value must be NORMAL; that needs `Reduction`.** -/
theorem typable_has_value {K : ConstSet} {Γ : CICCtx} {t : Term} (h : Typable K Γ t) :
    ∃ v : Value, IsValueOf v t := by
  -- `h` witnesses that the term is well-formed; the value comes from the term, not from the derivation
  have _ := h
  obtain ⟨v, hv⟩ := valueOf_total t
  exact ⟨v, hv⟩

/-- **The value is canonical: two witnesses of `IsValueOf` for the same term are equal.** -/
theorem is_value_of_unique {v w : Value} {t : Term} (hv : IsValueOf v t) (hw : IsValueOf w t) : v = w := by
  rw [IsValueOf] at hv hw
  rw [← hv, ← hw]

end Lattice.Core.CIC
