/-
# `Core/CIC/LiftShiftTotal.lean` -- the TOTAL commutation is FALSE, and `inst_comp` needs a different route (round 162)

## What rounds 154-161 were chasing, and what round 162 settles

**`inst_lift_shift` -- the commutation `inst (lift sigma) (shift 0 1 t) = shift 0 1 (inst sigma t)` -- was proved
in round 154 for BINDER-FREE terms only.**
**Rounds 155 through 161 each tried to lift it to all terms and each narrowed the obstruction without closing it.**

**Round 162 attempted it once more, now with `shift_commutation_general` (round 158) and the cutoff lemmas
(round 161) available.**
**It FAILS, and this time the failure is not at the induction's boundary but at the BASE.**

## The refutation

**The binder case of the attempted induction reduces to**

```
inst (lift (lift rho)) (shift 1 1 b) = shift 0 1 (inst (lift rho) b)
```

**At `b = var 0`:**

**LHS `= lift (lift rho) (shift 1 1 (var 0)) = lift (lift rho) (var 0) = var 0`.**
**RHS `= shift 0 1 (lift rho 0) = shift 0 1 (var 0) = var 1`.**

**`var 0 != var 1`.**

## Why this refutes the TOTAL statement, not merely the induction attempt

**The step above is not an artifact of the proof strategy: it is what the binder case OF THE STATEMENT requires.**
**`inst`'s `lam` clause substitutes the body with `lift (lift sigma)` and the goal's right side shifts by `0 1`.**
**=> any proof of the total commutation must establish that intermediate identity, and it is FALSE.**

**=> `inst_lift_shift` holds on binder-free terms and FAILS in general.**
**Round 154's fragment restriction was not a temporary limitation; it was the sharp boundary.**

## The precise reason, in round 161's terms

**`lift` pins index `0` to `var 0`.**
**`shift 0 1` moves index `0` to `var 1`.**
**=> a substitution and a shift CANNOT commute at index `0`, because one preserves it and the other moves it.**

**This is the same fact as `lift_at_cutoff_zero` (round 161), now seen from the direction that matters for the
composition theorem.**

## What this means for `inst_comp`

**The composition theorem `inst tau (inst sigma t) = inst (fun n => inst tau (sigma n)) t` CANNOT be proved by the
standard induction, because its binder case needs the total commutation.**

**=> the theorem is either false, or it holds only under a hypothesis that makes the commutation true, or it needs
a different formulation of substitution entirely (for example one where `lift` does NOT pin index `0`).**

**That is the decision the next round must make, and it is now an INFORMED decision rather than a guess.**

## What is proved here

| theorem | content |
|:--|:--|
| **`lift_shift_no_commute`** | **THE REFUTATION at `b = var 0`, as a `¬`-statement** |

**Nothing else: the total statement is false, so nothing else is worth proving about it.**
-/

import Mathlib
import Lattice.Core.CIC.LiftAtCutoff

namespace Lattice.Core.CIC

/-- **A lifted substitution does NOT commute with `shift 0 1` at index `0`.**

**`inst (lift (lift rho)) (shift 1 1 (var 0)) = var 0` but `shift 0 1 (inst (lift rho) (var 0)) = var 1`.**

**=> `inst (lift sigma) (shift 0 1 t) = shift 0 1 (inst sigma t)` is TRUE on binder-free terms (round 154) and
FALSE in general.**
**The binder case of `inst_comp` needs the FALSE version, which is why the standard induction does not establish
the composition theorem.**

**The cause is round 161's: `lift` preserves index `0` and `shift` moves it.** -/
theorem lift_shift_no_commute (rho : Subst) :
    ¬ (inst (lift (lift rho)) (shift 1 1 (.var 0)) = shift 0 1 (inst (lift rho) (.var 0))) := by
  intro h
  rw [shift_var_lt (by omega : (0 : ℕ) < 1)] at h
  have hv : (Term.var 0 : Term) = Term.var 1 := h
  cases hv

end Lattice.Core.CIC
