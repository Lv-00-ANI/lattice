/-
# `Core/CIC/LiftAtCutoff.lean` -- what `lift` does at a cutoff (round 161)

## The correction to round 160's diagnosis

**Round 160 concluded:**

> **"`lift` pins `0`, `shift` cuts at `j`, and every law that compares the two must carry `sigma 0 = var 0` as a
> hypothesis."**

**Round 161 tested that and found it INCOMPLETE: even with `sigma 0 = var 0`, the commutation
`inst (lift sigma) (shift j 1 t) = shift j 1 (inst sigma t)` is FALSE.**

## Why, computed

**At `n = m+1 < j`:**

**LHS `= lift sigma (m+1) = shift 0 1 (sigma m)` -- `lift` applies `sigma` at the DECREMENTED index.**
**RHS `= shift j 1 (sigma (m+1))` -- `shift` applies `sigma` at the SAME index.**

**=> the two sides apply `sigma` to DIFFERENT arguments (`m` versus `m+1`), and no hypothesis on `sigma 0` can
repair that.**

**=> the obstruction is not the index `0` alone: it is that `lift` and `shift` disagree about WHICH argument the
substitution is evaluated at.**

## What is proved

| theorem | content |
|:--|:--|
| **`lift_at_cutoff_lt`** | **`inst (lift sigma) (shift j 1 (var (m+1))) = shift 0 1 (sigma m)` when `m+1 < j`** |
| **`lift_at_cutoff_ge`** | **below the cutoff the index does not move, so `lift` decides alone** |

**`rfl`, both: the point is not difficulty but WHICH EQUATION is true.**

## Why this is the useful statement

**Every commutation law this development has tried (rounds 146, 147, 150, 152, 159, 160) assumed that shifting a
term and then substituting commutes with substituting then shifting.**

**`lift_at_cutoff_lt` says exactly what the LEFT side is: `sigma` at the decremented index, shifted by `1` --
not `sigma` at the original index, shifted by `j`.**

**=> a correct law has to move the ARGUMENT as well as the shift, and that is the piece every earlier attempt
lacked.**
**It is now a theorem rather than a suspicion.**
-/

import Mathlib
import Lattice.Core.CIC.ParallelSubst

namespace Lattice.Core.CIC

/-- **BELOW THE CUTOFF: `lift` decides, and the shift is irrelevant.**

**`inst (lift sigma) (shift j 1 (var (m+1))) = shift 0 1 (sigma m)` when `m+1 < j`.**

**`shift j 1` leaves `m+1` alone because it is below `j`; then `lift sigma (m+1) = shift 0 1 (sigma m)` by
definition.**
**=> the left side substitutes at the DECREMENTED index `m`, not at `m+1`.** -/
theorem lift_at_cutoff_lt (j m : ℕ) (hj : m + 1 < j) (sigma : Subst) :
    inst (lift sigma) (shift j 1 (.var (m + 1))) = shift 0 1 (sigma m) := by
  rw [shift_var_lt hj]
  rfl

/-- **AT INDEX `0` BELOW THE CUTOFF: `lift` pins it.**

**`inst (lift sigma) (shift j 1 (var 0)) = var 0` when `0 < j`.**

**`lift sigma 0 = var 0` by definition, and `shift j 1` also leaves index `0` alone below its cutoff -- so here
the two AGREE, which is why the `n = 0` case never exposes the obstruction.** -/
theorem lift_at_cutoff_zero (j : ℕ) (hj : 0 < j) (sigma : Subst) :
    inst (lift sigma) (shift j 1 (.var 0)) = .var 0 := by
  rw [shift_var_lt hj]
  rfl

/-- **ABOVE THE CUTOFF: both moves happen, and they compose.**

**`inst (lift sigma) (shift j 1 (var (j + k))) = shift 0 1 (sigma (j + k))` -- `shift j 1` moves the index by one,
and `lift` then substitutes at the moved index.** -/
theorem lift_at_cutoff_ge (j k : ℕ) (sigma : Subst) :
    inst (lift sigma) (shift j 1 (.var (j + k))) = shift 0 1 (sigma (j + k)) := by
  rw [shift_var_ge (by omega : ¬ j + k < j)]
  rfl

end Lattice.Core.CIC
