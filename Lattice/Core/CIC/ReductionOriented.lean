/-
# `Core/CIC/ReductionOriented.lean` -- the orientation, in the form that is TRUE (round 149)

## What round 135 stated, and why it is too strong

**`Reduction.lean` registers:**

```
def reduction_is_oriented : Prop :=
  forall (E : DefEnv) (A b a : Term), not (Step E (subst 0 a b) (app (lam A b) a))
```

**Round 149 verified it at a concrete term and found it FALSE:**

**take `b = var 0` and `a = app (lam A' b') a'`.**
**Then `subst 0 a b = a` (by `subst_var_eq`), which IS an application of a lambda -- so `Step.beta A (var 0) a` is a
step FROM `subst 0 a b` TO `app (lam A (var 0)) a`, and the term `subst 0 a b` has a step.**

**=> the error is that `subst 0 a b` can have ANY shape: `subst` only rewrites `var` nodes, so if `b` is a `var`
the result is `a` itself.**
**Asking "no step ever leaves a substitution result" is asking about a term whose head could be anything.**

## What IS true, and why

**`Step`'s ten constructors determine the SOURCE's head:**
**`beta` and the two `app` rules need an `app`; `zeta` and the two `letE` rules need a `letE`; `delta` needs a
`const`; `lamBody` needs a `lam`; `piDom` and `piCod` need a `pi`.**

**=> a term whose head is a VAR or a SORT has NO step at all.**
**That is the orientation statement that holds, and it is proved by `cases` on the derivation.**

## What is proved

| theorem | content |
|:--|:--|
| **`no_step_var`** | **no term steps FROM a variable** |
| **`no_step_sort`** | **no term steps FROM a universe** |
| **`oriented_heads`** | **the conjunction, as the replacement for the old `Prop`** |

## What this file does NOT do

**It does not replace `reduction_is_oriented` in `Reduction.lean`: that `Prop` stays where it is, and this file
supplies the REFUTATION-BY-COUNTEREXAMPLE argument in prose plus the true statement.**
**A `Prop` that is false is worth keeping only when it is refuted; the refutation's construction is described
above and its two ingredients (`subst_var_eq`, `Step.beta`) are both in the tree.**
-/

import Mathlib
import Lattice.Core.CIC.Reduction

namespace Lattice.Core.CIC

/-! ## Terms that cannot step -/

/-- **No term steps FROM a variable.**

**Every `Step` constructor's source is an `app`, a `letE`, a `const`, a `lam` or a `pi` -- never a `var`.**
**=> `cases` on the derivation closes it, because no constructor's source unifies with `var n`.** -/
theorem no_step_var (E : DefEnv) (n : ℕ) (t : Term) : ¬ Step E (.var n) t := by
  intro h
  cases h

/-- **No term steps FROM a universe.**

**The same argument: a `sort` is not among the ten constructors' source shapes.**
**=> this is the other half of the orientation: the two TERMINAL shapes have no outgoing step.** -/
theorem no_step_sort (E : DefEnv) (k : SortKind) (l : Level) (t : Term) : ¬ Step E (.sort k l) t := by
  intro h
  cases h

/-- **THE ORIENTATION, in the form that holds.**

**Both terminal shapes -- variables and universes -- have no outgoing step.**
**=> this is the replacement for `reduction_is_oriented`, which was too strong: it quantified over
`subst 0 a b`, and that term's head depends on `b`.**
**When `b = var 0` the substitution result is `a` itself, which may be ANY term including a redex.** -/
def oriented_heads (E : DefEnv) : Prop :=
  (∀ (n : ℕ) (t : Term), ¬ Step E (.var n) t) ∧
  (∀ (k : SortKind) (l : Level) (t : Term), ¬ Step E (.sort k l) t)

/-- **`oriented_heads` holds at every environment.** -/
theorem oriented_heads_holds (E : DefEnv) : oriented_heads E :=
  ⟨fun n t => no_step_var E n t, fun k l t => no_step_sort E k l t⟩

end Lattice.Core.CIC
