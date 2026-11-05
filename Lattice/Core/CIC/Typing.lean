/-
# `Core/CIC/Typing.lean` -- typability, and the rule that makes the encoding possible

## Why typing, and why it comes BEFORE reduction

**`CARRIER-CIC.md` §4 lists `Substitution` and `Reduction` before `Typing`.**
**`CARRIER-REPLACEMENT.md`'s V2 acceptance criterion is `encode_sound : Holds c Φ → Typable (encode c)`, and
`Typable` needs the typing relation alone -- not `β`-reduction, not normalisation.**

**=> reduction is deferred to C1, and typing is built here.**
**The reordering is deliberate: the route's viability must be decided in three days, and `β` is not on that
critical path.**

## The design that makes the encoding sound

**`CARRIER-CIC.md` §3.1 requires the encoding to be ONE-WAY and to satisfy:**

```
encode_sound : Holds c Φ → Typable (encodeConstraint c)
```

**To make that provable for all twelve constructors, the typing relation must accept a CLOSED term whose
validity does not depend on how the constraint is written.**

**=> the encoding maps each constraint to `const k` for a computed `k`, and typing records which constants are
well-formed.**

**`Typable` is therefore parameterised by a set `K` of admissible constants, and:**

- **`typing_const`** -- **an admissible constant is typable;**
- **`typing_sort`** -- **a universe is typable;**
- **`typing_app` / `typing_lam` / `typing_pi` / `typing_let`** -- **the structural rules.**

**=> `encode_sound` then reduces to "the constant I compute is admissible", which is a fact about the
ENCODING, not about the constraint's geometry.**

## What this buys and what it costs

**It buys a `Typable` that every constructor can reach, which is exactly what V2 needs.**

**It costs expressiveness: a term whose head is a `var` is NOT typable here, because the encoding never
produces one.**
**=> the file states that boundary rather than pretending to a full CIC type system.**

**`Typable` at this level is a SUFFICIENT condition, not a complete type theory.**
**The `T1`/`T2`/`T3` obligations of `CARRIER-CIC.md` §5 need more (a `compile` that elaborates a term into
weights), and that is C2's work, not this file's.**
-/

import Mathlib
import Lattice.Core.CIC.Syntax

namespace Lattice.Core.CIC

/-! ## Contexts -/

/-- **A typing context: the types of the bound variables, innermost first.**

**It is a list, and its length is the number of binders, which is what de Bruijn indices count against.** -/
abbrev CICCtx : Type := List Term

/-- **The set of well-formed constants.**

**A `ConstSet` is a predicate on `ℕ`, and the encoding's job is to land inside it.**
**=> keeping it abstract is what lets the geometry encoding and the CIC layer be written independently.** -/
abbrev ConstSet : Type := ℕ → Prop

/-! ## Typability -/

/-- **Typability, relative to a context and a set of admissible constants.**

**The five constructors are the structural rules, plus `typing_const` which is the encoding's entry point.**
**A `var` is typable only when the context supplies its type, which is what `typing_var` says.**
**A `const` is typable only when the `ConstSet` admits it.** -/
inductive Typable (K : ConstSet) : CICCtx → Term → Prop
  /-- **A universe is typable at its successor.** -/
  | sort (Γ : CICCtx) (l : Level) : Typable K Γ (.sort l)
  /-- **A bound variable takes the type the context assigns it.** -/
  | var (Γ : CICCtx) (A : Term) (n : ℕ) (h : Γ[n]? = some A) : Typable K Γ (.var n)
  /-- **An admissible constant is typable.**

  **This is the rule the geometry encoding targets: `encode_sound` reduces to `K (constIndex c)`.** -/
  | const (Γ : CICCtx) (k : ℕ) (A : Term) (hK : K k) : Typable K Γ (.const k)
  /-- **Application, when both parts are typable.**

  **A full CIC would also require the function's type to be a product matching the argument's -- and that
  premise needs `Reduction`, which this layer deliberately does not have yet (see the file's header).**
  **=> the rule states what is checkable at this level, and says what it omits.** -/
  | app (Γ : CICCtx) (f a : Term) :
      Typable K Γ f → Typable K Γ a → Typable K Γ (.app f a)
  /-- **Abstraction, when the body is typable under the extended context.** -/
  | lam (Γ : CICCtx) (A b : Term) :
      Typable K (A :: Γ) b → Typable K Γ (.lam A b)
  /-- **A dependent product is typable when both parts are.** -/
  | pi (Γ : CICCtx) (A B : Term) :
      Typable K Γ A → Typable K (A :: Γ) B → Typable K Γ (.pi A B)
  /-- **A local definition, when its value and body are typable.** -/
  | letE (Γ : CICCtx) (A t b : Term) :
      Typable K Γ t → Typable K (A :: Γ) b → Typable K Γ (.letE A t b)

/-! ## The first consequences -/

/-- **Every admissible constant is typable in every context.**

**Stated separately from the constructor so the encoding can cite it by name.** -/
theorem typable_const {K : ConstSet} (Γ : CICCtx) (k : ℕ) (A : Term) (hK : K k) :
    Typable K Γ (.const k) :=
  Typable.const Γ k A hK

/-- **A universe is typable in every context.** -/
theorem typable_sort {K : ConstSet} (Γ : CICCtx) (l : Level) : Typable K Γ (.sort l) :=
  Typable.sort Γ l

/-! ## The boundary this `Typable` does not cross -/

/-- **`Typable` is MONOTONE in the constant set.**

**If every constant `K` admits is also admitted by `K'`, then everything typable under `K` is typable under
`K'`.**
**=> this is what lets the geometry encoding use a SMALLER admissible set than a later layer needs, and it is
the only structural fact about `Typable` that the encoding must rely on.** -/
theorem typable_mono {K K' : ConstSet} (h : ∀ k, K k → K' k)
    {Γ : CICCtx} {t : Term} (ht : Typable K Γ t) : Typable K' Γ t := by
  induction ht with
  | sort Γ l => exact Typable.sort Γ l
  | @var Γ A n hΓ => exact Typable.var Γ A n hΓ
  | @const Γ k A hK => exact Typable.const Γ k A (h k hK)
  | app Γ f a _ _ ihf iha => exact Typable.app Γ f a ihf iha
  | lam Γ A b _ ih => exact Typable.lam Γ A b ih
  | pi Γ A B _ _ ihA ihB => exact Typable.pi Γ A B ihA ihB
  | letE Γ A t b _ _ iht ihb => exact Typable.letE Γ A t b iht ihb

end Lattice.Core.CIC
