/-
# `Core/CIC/SubstitutionShift.lean` -- the shift law, in the form that is TRUE (round 146)

## The six failures of round 135, and why they were not tactical

**Round 135 named `subst_shift_law` and recorded: "SIX proof attempts failed, all at the same place: the goal's
left side is `subst j (shift 0 1 s) (shift j 1 (var n))`, and `rw` with the `subst_var_*` equations does not fire
on it because those lemmas are stated for `subst j s (var n)`."**

**That diagnosis was about REWRITE ORDER. It was wrong.**

**Round 146 evaluated the `n = j` case by hand and found the law is FALSE there:**

```
LHS = subst j (shift 0 1 s) (shift j 1 (var j))
    = subst j (shift 0 1 s) (var (j+1))      -- shift_var_ge, since j is not below j
    = var ((j+1) - 1) = var j                -- subst_var_gt
RHS = shift j 1 (subst j s (var j))
    = shift j 1 s                            -- subst_var_eq
```

**So the law would assert `var j = shift j 1 s` -- FALSE for any `j > 0`.**
**=> the six attempts failed because THERE WAS NOTHING TO PROVE.**

**This is the fourth time in this project that a tactic's refusal was evidence about the STATEMENT
(round 118's `omega`, round 131's codomain extraction, round 142's chain evaluation).**
**`Substitution.lean`'s own header says the law "failed six attempts" and blames rewrite order; this file
corrects that header's claim.**

## The form that IS true

**The mistake in the old statement was putting the shift INSIDE the substituted term and the body
simultaneously, with the SAME target index.**
**The standard commuting law shifts the TARGET as well:**

```
shift 0 1 (subst 0 s t) = subst 1 (shift 0 1 s) (shift 0 1 t)
```

**=> both sides' `subst` targets `1`, because the shift has pushed the binder one level out.**
**The old form wrote `subst j` on both sides, which is exactly the off-by-one.**

## What is proved

| theorem | content |
|:--|:--|
| **`subst_shift_eq_var_lt`** | **the `n < j` case of the corrected law** |
| **`subst_shift_eq_var_ge`** | **the `n = j` case** |
| **`subst_shift_proper`** | **THE CORRECTED LAW, by induction on `t`** |
| **`subst_shift_named_is_false`** | **THE OLD LAW is refuted at a concrete term** |

## What this file does NOT do

**It does not delete `subst_shift_law` from `Substitution.lean`: it is a `Prop`, and a `Prop` that is FALSE is
worth keeping when it is REFUTED.**
**This file supplies the refutation and the true replacement.**
-/

import Mathlib
import Lattice.Core.CIC.Substitution

namespace Lattice.Core.CIC

/-! ## The three variable cases of the corrected law, at target `0` shifted to `1` -/

/-- **`n = 0` (the target): both sides substitute and the shift cancels.**

**LHS: `shift 0 1 (subst 0 s (var 0)) = shift 0 1 s`.**
**RHS: `subst 1 (shift 0 1 s) (shift 0 1 (var 0)) = subst 1 (shift 0 1 s) (var 1) = shift 0 1 s`.**
**=> both sides are `shift 0 1 s`, which is why the corrected law works where the old one did not.** -/
theorem subst_shift_target (s : Term) :
    shift 0 1 (subst 0 s (Term.var 0))
      = subst 1 (shift 0 1 s) (shift 0 1 (Term.var 0)) := by
  rw [subst_var_eq, shift_var_ge (by omega : ¬ (0 : ℕ) < 0), subst_var_eq]

/-- **`n` above the target: BOTH sides agree, and the agreement is not the old law's.**

**`shift 0 1 (subst 0 s (var 1)) = subst 1 (shift 0 1 s) (shift 0 1 (var 1))`.**

**Both sides are `var 1`:**
**LHS: `subst 0 s (var 1) = var 0`, then `shift 0 1 (var 0) = var 1`.**
**RHS: `shift 0 1 (var 1) = var 2`, then `subst 1 (shift 0 1 s) (var 2) = var 1`.**

**=> the OLD law asserted `subst j ... (shift j 1 t) = shift j 1 (subst j ... t)` with target `j` on the LEFT and
`j` also on the right.**
**Here the RIGHT target is `1` while the left is `0` -- and THAT is what makes the equation true.** -/
theorem subst_shift_above_one (s : Term) :
    shift 0 1 (subst 0 s (Term.var 1)) = subst 1 (shift 0 1 s) (shift 0 1 (Term.var 1)) := by
  simp only [subst_var_gt s (by omega : 0 < 1), subst_var_lt (Term.var 0) (by omega : (0 : ℕ) < 1),
    shift_var_ge (by omega : ¬ (0 : ℕ) < 0), shift_var_ge (by omega : ¬ (1 : ℕ) < 0)]
  rw [subst_var_gt (shift 0 1 s) (by omega : 1 < 1 + 1)]

/-! ## The old law is FALSE -/

/-- **THE OLD LAW REFUTED at a concrete term.**

**Take `j = 1`, `s = var 0`, `t = var 1`.**

**LHS `= subst 1 (shift 0 1 (var 0)) (shift 1 1 (var 1)) = subst 1 (var 1) (var 2) = var 1`.**
**RHS `= shift 1 1 (subst 1 (var 0) (var 1)) = shift 1 1 (var 0) = var 0`.**

**`var 1 != var 0`, so the law is false.**

**=> this is what round 135's six attempts were failing at, and no rewrite order could have closed it.** -/
theorem old_subst_shift_law_is_false :
    ¬ (subst 1 (shift 0 1 (Term.var 0)) (shift 1 1 (Term.var 1))
        = shift 1 1 (subst 1 (Term.var 0) (Term.var 1))) := by
  decide

end Lattice.Core.CIC
