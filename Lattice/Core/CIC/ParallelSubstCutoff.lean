/-
# `Core/CIC/ParallelSubstCutoff.lean` -- the cutoff commutation FAILS (round 160)

## What round 159 proposed, and what round 160 found

**Round 159 proved the bridge between the two representations and proposed to transport `subst_shift_law` into
`inst` vocabulary:**

> **"`subst_shift_law` can now be RESTATED as a statement about `inst`, where the composition theorem is the
> natural route."**

**Round 160 tried exactly that, and the transport requires a commutation that turns out to be FALSE.**

## The candidate

**`inst_lift_shift_flat` (round 154) is stated at cutoff `0`:**

```
inst (lift sigma) (shift 0 1 t) = shift 0 1 (inst sigma t)
```

**The `subst`-side law needs the SAME statement at an ARBITRARY cutoff `j`, because its left side is
`shift j 1 t`.**

```
candidate : inst (lift sigma) (shift j 1 t) = shift j 1 (inst sigma t)
```

## The refutation, computed

**Take `j = 1`, `sigma = fun _ => var 5`, `t = var 0`.**

**`shift 1 1 (var 0) = var 0`, because `0 < 1`.**

**Then:**

```
LHS = inst (lift sigma) (var 0) = lift sigma 0 = var 0
RHS = shift 1 1 (inst sigma (var 0)) = shift 1 1 (var 5) = var 6
```

**`var 0 != var 6`.**

## Why it fails, and why this is the same failure as always

**`lift sigma 0 = var 0` BY DEFINITION.**
**That is `lift`'s design: the binder's own variable is untouched.**

**But `shift j 1` at cutoff `j > 0` leaves index `0` alone, so the left side reaches `lift sigma 0 = var 0` while
the right side reaches `shift j 1 (sigma 0)`, which MOVES.**

**=> the two sides agree only when `sigma 0 = var 0`, exactly the hypothesis round 155 already isolated for
`binderCommutation`.**

**This is the SIXTH substitution statement refuted in this development (146, 147, 150, 152, 159, 160), and every
one of them fails at the same place: index `0` under `lift`, or index `j`/`j+1` under `shift`.**

## What this means for `subst_shift_law`

**The transport is not free: it needs the hypothesis `sigma 0 = var 0`.**
**Whether `singleSubst j s` satisfies that hypothesis depends on `j`: at `j = 0` it maps `0` to `s`, NOT to
`var 0`.**
**=> `subst_shift_law` CANNOT be transported at `j = 0`, and round 146 already refuted it there independently.**

**The two refutations are the SAME obstruction seen from two vocabularies, which is exactly what round 159's
bridge was built to reveal.**

## What is proved here

| theorem | content |
|:--|:--|
| **`cutoff_commutation_false`** | **THE REFUTATION, at `j = 1`, `sigma = const (var 5)`, `t = var 0`** |

**Nothing else: the general statement is false, so nothing else is worth proving about it.**
-/

import Mathlib
import Lattice.Core.CIC.SubstBridge

namespace Lattice.Core.CIC

/-- **The commutation at an arbitrary cutoff is FALSE.**

**At `j = 1`, `sigma = fun _ => var 5`, `t = var 0`:**

**LHS `= inst (lift sigma) (var 0) = lift sigma 0 = var 0`.**
**RHS `= shift 1 1 (var 5) = var 6`.**

**=> `shift j 1` at `j > 0` leaves index `0` alone, so the left reaches `lift sigma 0 = var 0` while the right
MOVES `sigma 0`.**

**The two agree only when `sigma 0 = var 0` -- round 155's hypothesis, here reappearing one vocabulary over.**

**=> this is the obstruction that stops `subst_shift_law` from being transported to `inst` at `j = 0`.** -/
theorem cutoff_commutation_false :
    ¬ (inst (lift (fun _ => (Term.var 5 : Term))) (shift 1 1 (Term.var 0))
      = shift 1 1 (inst (fun _ => (Term.var 5 : Term)) (Term.var 0))) := by
  rw [shift_var_lt (by omega : (0 : ℕ) < 1)]
  show Term.var 0 ≠ Term.var 6
  intro h
  cases h

end Lattice.Core.CIC
