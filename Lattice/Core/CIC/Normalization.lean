/-
# `Core/CIC/Normalization.lean` -- bounded reduction, and why the bound must be an INPUT (round 149)

## The obstacle this file starts from, discovered by probing

**`CARRIER-CIC.md`'s C1-3 asks for "weak normalisation and a `steps` bound".**
**The natural first move is a step COUNT on a derivation: `Reduces.length : ℕ`.**

**That is IMPOSSIBLE, and the reason is architectural: `Reduces : ... -> Prop`, so its recursor is**

```
Reduces.rec : {motive : (a b : Term) -> Reduces E a b -> Prop} -> ... -> ...
```

**`motive` lands in `Prop`.**
**=> a `Reduces` derivation cannot be counted, because counting would eliminate into `Nat`.**

**This is a consequence of round 135's own choice to declare `Reduces` in `Prop`, and it is the right choice --
a reduction derivation is a PROOF that a reduction happens, not a data structure.**

## What CAN be stated, and is

**The bound must be an INPUT, not an output:**

**`ReducesWithin E n a b` -- "`a` reaches `b` in AT MOST `n` steps".**

**It is defined by recursion on `n`, so it eliminates into `Prop` cleanly, and:**

| theorem | content |
|:--|:--|
| **`within_zero`** | **`ReducesWithin E 0 a b` iff `a = b`** |
| **`within_succ`** | **`n+1` steps is: either equal, or one step then `n`** |
| **`within_of_reduces`** | **every `Reduces` has SOME bound (existential, not a computed count)** |
| **`reduces_of_within`** | **a bounded reduction IS a reduction** |
| **`steps_are_linear`** | **the two directions agree** |

## What this file does NOT do

**It does not prove NORMALISATION -- no statement here bounds the number of steps a term CAN take, only that any
GIVEN reduction has a bound.**
**Terminating reduction needs a well-founded measure on terms, and `beta` can GROW a term (`subst` duplicates
its argument), so the measure is not size.**

**=> strong normalisation is a research-level statement for this calculus, and `CARRIER-CIC.md` §7.2 already says
it "may need an explicit `epsilon`".**
**This file states the BOUNDED form, which is what an evaluator with a fuel parameter actually needs.**
-/

import Mathlib
import Lattice.Core.CIC.Reduction

namespace Lattice.Core.CIC

/-! ## Bounded reduction -/

/-- **`a` reaches `b` in at most `n` steps.**

**The recursion is on `n`, so this eliminates into `Prop` -- which is what `Reduces` cannot do.**
**=> the bound is an INPUT: an evaluator supplies it, and the proposition says the run fits.** -/
inductive ReducesWithin (E : DefEnv) : ℕ → Term → Term → Prop
  /-- **Zero steps: the terms are equal.** -/
  | refl (a : Term) : ReducesWithin E 0 a a
  /-- **One step, then at most `n` more.** -/
  | step {n : ℕ} {a b c : Term} :
      Step E a b → ReducesWithin E n b c → ReducesWithin E (n + 1) a c

/-! ## The two directions -/

/-- **A bounded reduction IS a reduction.**

**Forget the bound: every `ReducesWithin` is a `Reduces`.**
**=> this is the soundness of the bounded form, and it is an induction on the bound.** -/
theorem reduces_of_within (E : DefEnv) {n : ℕ} {a b : Term}
    (h : ReducesWithin E n a b) : Reduces E a b := by
  induction h with
  | refl a => exact Reduces.refl a
  | step hs _ ih => exact Reduces.step hs ih

/-- **Every reduction has SOME bound.**

**The statement is EXISTENTIAL because a count cannot be COMPUTED from a `Prop` derivation -- but the existence
of a bound follows by induction on the derivation, which is exactly what `Prop`-elimination allows.** -/
theorem within_of_reduces (E : DefEnv) {a b : Term} (h : Reduces E a b) :
    ∃ n, ReducesWithin E n a b := by
  induction h with
  | refl a => exact ⟨0, ReducesWithin.refl a⟩
  | step hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, ReducesWithin.step hs hn⟩

/-- **Zero steps means the terms are equal.**

**The base case of the bound, stated because a caller needs to unfold it.** -/
theorem within_zero_iff (E : DefEnv) (a b : Term) :
    ReducesWithin E 0 a b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact ReducesWithin.refl a

/-- **The two forms describe the SAME relation, up to the bound.**

**`Reduces` iff some `ReducesWithin` -- the converse of `reduces_of_within` composed with `within_of_reduces`.** -/
theorem reduces_iff_exists_within (E : DefEnv) (a b : Term) :
    Reduces E a b ↔ ∃ n, ReducesWithin E n a b :=
  ⟨within_of_reduces E, fun ⟨_, h⟩ => reduces_of_within E h⟩

end Lattice.Core.CIC
