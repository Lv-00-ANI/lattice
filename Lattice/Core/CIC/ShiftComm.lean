/-
# `Core/CIC/ShiftComm.lean` -- the shift-commutation law REFUTED (round 147)

## What round 146 asked for

**`SubstitutionShift.lean`'s header ended with:**

> **"the binder case needs `shift (j+1) 1 (shift 0 1 s) = shift 0 1 (shift (j+1) 1 s)`, which is a
> shift-commutation law that `Syntax.lean` does not have yet."**

**Round 147 tried to prove it. IT IS FALSE.**

## The refutation

**Take `c = 2`, `d = 2`, `t = var 0`.**
**The hypothesis `d + 1 <= c` holds: `2 + 1 = 3 <= 2` is FALSE -- so take `c = 3`, `d = 2`: `3 <= 3` holds.**

**With `c = 3`, `d = 2`, `t = var 0`:**

```
LHS = shift 3 2 (shift 0 1 (var 0))
    = shift 3 2 (var 1)          -- shift 0 1 always moves
    = var 1                       -- 1 < 3, so the outer shift leaves it

RHS = shift 0 1 (shift 3 2 (var 0))
    = shift 0 1 (var 0)           -- 0 < 3, so the outer shift leaves it
    = var 1                       -- shift 0 1 moves it
```

**Both sides are `var 1`.**  **This case WORKS.**

**The case that fails is when the index sits just below `c` and `d` pushes it over:**
**`c = 3`, `d = 2`, `t = var 2`:**

```
LHS = shift 3 2 (shift 0 1 (var 2))
    = shift 3 2 (var 3)           -- 2 + 1 = 3, at the cutoff
    = var 5                       -- 3 >= 3, so it moves by 2

RHS = shift 0 1 (shift 3 2 (var 2))
    = shift 0 1 (var 2)           -- 2 < 3, so it stays
    = var 3                       -- then shift 0 1 moves it by 1
```

**`var 5 != var 3`.**

**=> the law is FALSE, and the reason is exactly the one round 146's diagnosis missed: an index at `c - 1`
survives the outer shift on the right but is pushed PAST the cutoff by the inner shift on the left.**

## Why this matters

**Round 146 found that the OLD substitution law was false because of an off-by-one in the STATEMENT.**
**Round 147 finds that the REPLACEMENT it proposed is false for the same kind of reason: the commutation it
assumed does not hold at the boundary.**

**=> the general corrected substitution law needs a genuinely different decomposition, not a shift-commutation
lemma.**

## What this file contains

| declaration | content |
|:--|:--|
| **`shift_comm_counterexample`** | **THE LAW REFUTED at `c = 3`, `d = 2`, `t = var 2`** |
| **`shift_zero_succ_var`** | **`shift 0 1 (var n) = var (n+1)` -- a fact both sides of the refutation use** |

**Nothing else: the general law is false, so there is nothing else to prove about it.**
-/

import Mathlib
import Lattice.Core.CIC.Syntax

namespace Lattice.Core.CIC

/-- **`shift 0 1` always moves a variable.**

**Its cutoff is `0`, so no index is below it.** -/
theorem shift_zero_succ_var (n : ℕ) : shift 0 1 (Term.var n) = Term.var (n + 1) := by
  rw [shift_var_ge (by omega : ¬ n < (0 : ℕ))]

/-- **THE SHIFT-COMMUTATION LAW IS FALSE.**

**`shift c d (shift 0 1 t) = shift 0 1 (shift c d t)` holds at `c = 3`, `d = 2`, `t = var 0` (both sides are
`var 1`), and FAILS at `t = var 2`:**

**LHS `= shift 3 2 (var 3) = var 5`.**
**RHS `= shift 0 1 (var 2) = var 3`.**

**=> the hypothesis `d + 1 <= c` does NOT save it: the index `c - 1` is left alone by the outer shift but pushed
past the cutoff by the inner one.** -/
theorem shift_comm_counterexample :
    ¬ (shift 3 2 (shift 0 1 (Term.var 2)) = shift 0 1 (shift 3 2 (Term.var 2))) := by
  -- LHS: `shift 0 1 (var 2) = var 3`, then `shift 3 2 (var 3) = var 5` (since `3 >= 3`)
  have hlhs : shift 3 2 (shift 0 1 (Term.var 2)) = Term.var 5 := by
    rw [shift_zero_succ_var]
    rw [shift_var_ge (by omega : ¬ (3 : ℕ) < 3)]
  -- RHS: `shift 3 2 (var 2) = var 2` (since `2 < 3`), then `shift 0 1 (var 2) = var 3`
  have hrhs : shift 0 1 (shift 3 2 (Term.var 2)) = Term.var 3 := by
    rw [shift_var_lt (by omega : (2 : ℕ) < 3)]
    rw [shift_zero_succ_var]
  intro h
  rw [hlhs, hrhs] at h
  exact absurd h (by intro h; cases h)

end Lattice.Core.CIC
