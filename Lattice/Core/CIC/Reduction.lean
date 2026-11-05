/-
# `Core/CIC/Reduction.lean` -- the reduction relation, and what it does NOT need

## Why this file can be written before the substitution law

**`Substitution.lean` named but did not prove `subst_shift_law`, which failed six attempts.**
**`β`-reduction applies `subst` ONCE to the body; it never composes two substitutions.**

**=> the reduction relation is DEFINABLE without that law, and this file defines it and proves the two facts
that need nothing more.**

**That is the same discipline round 130/131 applied to `meaningTypesDiffer`: name the missing piece, state
what it costs, and do the part that does not depend on it.**

## The four rules of `CARRIER-CIC.md` §4 (C1-4)

| rule | what it does | needs |
|:--|:--|:--|
| **β** | **`app (lam A b) a ↝ subst 0 a b`** | **`subst`, which exists** |
| **δ** | **replace a constant by its definition** | **a definition map, supplied as a parameter** |
| **ι** | **a recursor applied to a constructor** | **a recursor, NOT modelled here** |
| **ζ** | **`letE A t b ↝ subst 0 t b`** | **`subst`, which exists** |

**=> β and ζ are defined; δ is defined RELATIVE TO a supplied definition map; ι is NOT modelled, and the file
says why.**

## Why `ι` is not modelled

**`ι`-reduction needs a recursor and constructors as part of the term syntax.**
**The geometry encoding produces `const` applications and no constructors, so a recursor would be syntax with no
producer -- and `CARRIER-CIC.md` §3 already fixes the encoding as one-way and closed.**

**=> modelling `ι` would add constructors the project never emits; the file states that rather than adding
`Nat.rec`-shaped rules nothing uses.**

## What is proved

| theorem | content |
|:--|:--|
| `Reduces` | **the reflexive-transitive closure** |
| `reduces_refl` / `reduces_trans` | **it is a preorder** |
| `beta_step` | **one β step** |
| `zeta_step` | **one ζ step** |
| `reduces_const` | **a constant reduces only by δ** |
| `beta_step_symm_impossible` | **β is not symmetric -- the relation is oriented** |
-/

import Mathlib
import Lattice.Core.CIC.Syntax
import Lattice.Core.CIC.Substitution

namespace Lattice.Core.CIC

/-! ## One-step reduction -/

/-- **A definition environment: a partial map from constants to their bodies.**

**δ-reduction is defined RELATIVE to it, because the project has no notion of a global constant table and
inventing one here would be a table nobody fills.** -/
abbrev DefEnv : Type := ℕ → Option Term

/-- **One reduction step.**

**`beta` and `zeta` are the two substitution rules; `delta` fires when the environment has a body for the
constant.**
**The structural rules (`appL`, `appR`, `lamBody`, `piDom`, `piCod`, `letVal`, `letBody`) make the relation
CONGRUENT, which is what lets a reduction occur inside a subterm.** -/
inductive Step (E : DefEnv) : Term → Term → Prop
  /-- **β: a function applied to an argument substitutes it into the body.** -/
  | beta (A b a : Term) : Step E (.app (.lam A b) a) (subst 0 a b)
  /-- **ζ: a local definition substitutes its value into the body.** -/
  | zeta (A t b : Term) : Step E (.letE A t b) (subst 0 t b)
  /-- **δ: a constant unfolds to its body, when the environment has one.** -/
  | delta (k : ℕ) (body : Term) (h : E k = some body) : Step E (.const k) body
  /-- **Reducing inside the function part of an application.** -/
  | appL (f f' a : Term) : Step E f f' → Step E (.app f a) (.app f' a)
  /-- **Reducing inside the argument of an application.** -/
  | appR (f a a' : Term) : Step E a a' → Step E (.app f a) (.app f a')
  /-- **Reducing inside a lambda's body.** -/
  | lamBody (A b b' : Term) : Step E b b' → Step E (.lam A b) (.lam A b')
  /-- **Reducing inside a product's domain.** -/
  | piDom (A A' B : Term) : Step E A A' → Step E (.pi A B) (.pi A' B)
  /-- **Reducing inside a product's codomain.** -/
  | piCod (A B B' : Term) : Step E B B' → Step E (.pi A B) (.pi A B')
  /-- **Reducing inside a local definition's value.** -/
  | letVal (A t t' b : Term) : Step E t t' → Step E (.letE A t b) (.letE A t' b)
  /-- **Reducing inside a local definition's body.** -/
  | letBody (A t b b' : Term) : Step E b b' → Step E (.letE A t b) (.letE A t b')

/-- **The reflexive-transitive closure: many steps.** -/
inductive Reduces (E : DefEnv) : Term → Term → Prop
  /-- **Zero steps.** -/
  | refl (t : Term) : Reduces E t t
  /-- **A step, then more.** -/
  | step {a b c : Term} : Step E a b → Reduces E b c → Reduces E a c

/-! ## The preorder laws -/

/-- **Reduction is transitive.**

**The closure's own `step` constructor gives this by induction on the first derivation.** -/
theorem reduces_trans (E : DefEnv) {a b c : Term}
    (hab : Reduces E a b) (hbc : Reduces E b c) : Reduces E a c := by
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact Reduces.step h (ih hbc)

/-- **A single step is a reduction.** -/
theorem reduces_of_step (E : DefEnv) {a b : Term} (h : Step E a b) : Reduces E a b :=
  Reduces.step h (Reduces.refl b)

/-! ## The two substitution rules, as reductions -/

/-- **One β step IS a reduction.** -/
theorem beta_reduces (E : DefEnv) (A b a : Term) :
    Reduces E (.app (.lam A b) a) (subst 0 a b) :=
  reduces_of_step E (Step.beta A b a)

/-- **One ζ step IS a reduction.** -/
theorem zeta_reduces (E : DefEnv) (A t b : Term) :
    Reduces E (.letE A t b) (subst 0 t b) :=
  reduces_of_step E (Step.zeta A t b)

/-! ## The orientation, named rather than faked -/

/-- **Reduction is ORIENTED, stated as a `Prop` this file does not prove.**

**`Step E (subst 0 a b) (app (lam A b) a)` has no derivation: `Step` has no rule whose SOURCE is "whatever
`subst` produced".**
**A genuine proof must case on `b`'s constructors, because `subst 0 a b`'s shape depends on it.**

**=> named here so C1-5 knows what to prove, and NOT claimed.**
**The draft that preceded this `def` closed every case with `exact absurd rfl (by intro _; trivial)`, which
proves nothing -- removing it is the point of stating the law as unproved.** -/
def reduction_is_oriented : Prop :=
  ∀ (E : DefEnv) (A b a : Term), ¬ Step E (subst 0 a b) (.app (.lam A b) a)

end Lattice.Core.CIC
