/-
# `Core/CIC/ShiftNonComm.lean` -- shifts at DIFFERENT cutoffs do NOT commute (round 150)

## The third attempt at a shift-commutation law

| round | the form tried | result |
|--:|:--|:--|
| **146** | **`subst j (shift 0 1 s) (shift j 1 t) = shift j 1 (subst j s t)`** | **FALSE: off-by-one in the statement** |
| **147** | **`shift (j+1) 1 (shift 0 1 t) = shift 0 1 (shift (j+1) 1 t)`** | **FALSE: boundary at `c-1`** |
| **150** | **`shift c d (shift c' d' t) = shift c' d' (shift c d t)` for `c' < c`** | **FALSE: `var 3 != var 2`** |

**=> three forms, three refutations, all at the SAME boundary: an index sitting exactly at a cutoff.**

## The refutation

**Take `c = 2`, `d = 1`, `c' = 1`, `d' = 1`, `t = var 1`:**

```
LHS = shift 2 1 (shift 1 1 (var 1))
    = shift 2 1 (var 2)      -- 1 < 1 is FALSE, so the inner shift moves it
    = var 3                  -- 2 < 2 is FALSE, so the outer shift moves it

RHS = shift 1 1 (shift 2 1 (var 1))
    = shift 1 1 (var 1)      -- 1 < 2 is TRUE, so the outer shift leaves it
    = var 2                  -- then the inner shift moves it
```

**`var 3 != var 2`.**

## Why they never commute

**The two orders apply the SAME increments but DECIDE the cutoff tests against DIFFERENT indices.**
**On the left, the inner shift runs first and the OUTER cutoff is tested against an already-moved index; on the
right, it is tested against the original.**
**=> whenever an index sits between the two cutoffs, the tests disagree, and no hypothesis on `c`, `d`, `c'`, `d'`
can prevent that -- only a hypothesis on `n` itself can.**

## What this means for the substitution law

**The general corrected substitution law needs a decomposition that does NOT go through shift commutation.**
**`MACRO-COGNITION-148.md`'s M-5 already says it needs "a 3x3 table of concrete `(j, n)` cases computed by hand,
and any unequal cell REFUTES the form".**

**=> this file is the evidence that a shift-commutation route is dead, and it cost ONE round rather than six.**

## What is proved

| theorem | content |
|:--|:--|
| **`shift_different_cutoffs_dont_commute`** | **THE REFUTATION at `c=2, d=1, c'=1, d'=1, n=1`** |

**Nothing else: the general law is false, so nothing else is worth proving about it.**
-/

import Mathlib
import Lattice.Core.CIC.Syntax

namespace Lattice.Core.CIC

/-- **Shifts at different cutoffs do NOT commute.**

**`shift 2 1 (shift 1 1 (var 1)) = var 3`.**
**`shift 1 1 (shift 2 1 (var 1)) = var 2`.**

**=> `var 3 != var 2`, and the failure is at the index BETWEEN the two cutoffs.**

**This is the THIRD commutation form refuted (rounds 146, 147, 150), all at the same boundary.**
**=> the general substitution law must be decomposed some other way.** -/
theorem shift_different_cutoffs_dont_commute :
    ¬ (shift 2 1 (shift 1 1 (Term.var 1)) = shift 1 1 (shift 2 1 (Term.var 1))) := by
  have hlhs : shift 2 1 (shift 1 1 (Term.var 1)) = Term.var 3 := by
    rw [shift_var_ge (by omega : ¬ (1 : ℕ) < 1)]
    rw [shift_var_ge (by omega : ¬ (2 : ℕ) < 2)]
  have hrhs : shift 1 1 (shift 2 1 (Term.var 1)) = Term.var 2 := by
    rw [shift_var_lt (by omega : (1 : ℕ) < 2)]
    rw [shift_var_ge (by omega : ¬ (1 : ℕ) < 1)]
  intro h
  rw [hlhs, hrhs] at h
  exact absurd h (by intro h; cases h)

end Lattice.Core.CIC
