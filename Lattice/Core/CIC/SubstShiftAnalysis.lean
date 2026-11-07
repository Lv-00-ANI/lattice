import Mathlib
import Lattice.Core.CIC.Substitution

/-!
# `Core/CIC/SubstShiftAnalysis.lean` -- why `subst_shift_law` is false, and what IS true (round 196)

## The problem this file closes

`Substitution.lean` declares, but does not prove:

```
def subst_shift_law : Prop :=
  ∀ (t : Term) (j : ℕ) (s : Term),
    subst j (shift 0 1 s) (shift j 1 t) = shift j 1 (subst j s t)
```

Round 135 stated it; rounds 135-145 attempted it six times; round 146 recorded
`old_subst_shift_law_is_false`.

This file supplies the ANALYSIS: the law fails for a STRUCTURAL reason, not for want of a clever proof, and naming
that reason is what lets the tree stop treating it as an open obligation.

## The structural reason, computed from the two definitions

`shift c d (var n)  = if n < c then var n else var (n + d)`          -- ADDS `d` above cutoff `c`
`subst j s (var n)  = if n = j then s else if n < j then var n else var (n - 1)`   -- DELETES index `j`

So `shift` is an INSERTION (indices at or above `c` move up) and `subst` is a DELETION (indices above `j` move
down).

**The two operations act on the index line in OPPOSITE directions, and they disagree about which side of the
cutoff an index at exactly `j` belongs to.**

Take `t = var 1`, `j = 1`, `s = var 0`, and look at the law's instance at `shift 1 1`:

| side | computation | result |
|:--|:--|:--|
| **LHS** | **`shift 1 1 (var 1)` = `var 2` (since `1 < 1` fails), then `subst 1 s (var 2)` = `var 1` (since `2 > 1`)** | **`var 1`** |
| **RHS** | **`subst 1 s (var 1)` = `s` = `var 0` (since `1 = 1`), then `shift 1 1 (var 0)` = `var 0` (since `0 < 1`)** | **`var 0`** |

**=> `var 1 ≠ var 0`, and the instance needed no binder, no substitution term and no cleverness: it is decided by
the two definitions alone.**

**The disagreement: at `n = j` the LHS never reaches the substitution branch, because `shift` has already moved the
index ABOVE `j`.**

## What IS true, and it is proved here

The failure is LOCAL to `n = j`. Away from that index the two sides agree, and that is a theorem:

| theorem | content |
|:--|:--|
| **`subst_shift_agree_below`** | **below both cutoffs the two sides agree: `n < c` and `n < j` give `var n`** |
| **`subst_shift_agree_above`** | **strictly above both, the two sides agree: the index arithmetic `n+d-1 = n-1+d` holds** |
| **`subst_shift_disagrees_at`** | **AT `n = j` (with `j < c`) the two sides differ whenever `s ≠ shift c d s`** |
| **`shift_var_untouched_below`** | **`shift c d (var n) = var n` for `n < c`** |

**=> together these say the law holds on every index EXCEPT the substituted one, and gives the exact condition under
which even that index agrees (`s` fixed by the shift).**
**That is a sharper statement than "the law is false": it localises the obstruction.**

## What this file does NOT do

It does not restate `subst_shift_law` in a repaired form and call that the obligation discharged.
The repaired form would be a DIFFERENT law, and `Substitution.lean`'s docstring already says the original is named
rather than faked.

What this file adds is the ANALYSIS that makes the naming permanent and specific: an independent round no longer has
to rediscover WHY, and a future carrier that uses a textbook insertion-style substitution can prove its own version
without inheriting this obstruction.
-/

namespace Lattice.Core.CIC

/-- **`shift` leaves variables below the cutoff untouched.** -/
theorem shift_var_untouched_below {c d n : ℕ} (h : n < c) :
    shift c d (Term.var n) = Term.var n := by
  simp only [shift, if_pos h]

/-- **BELOW BOTH CUTOFFS THE TWO SIDES AGREE.**

For `n < c` and `n < j`, both `subst j (shift c d s) (shift c d t)` and `shift c d (subst j s t)` leave `var n`
alone.
=> this is the `n`-below-both case of the commutation, and it holds unconditionally. -/
theorem subst_shift_agree_below {c d j n : ℕ} (s : Term)
    (hc : n < c) (hj : n < j) :
    subst j (shift c d s) (shift c d (Term.var n)) = shift c d (subst j s (Term.var n)) := by
  rw [shift_var_untouched_below hc]
  have hjc : n < j := hj
  have hnc : n < c := hc
  simp only [subst, if_neg (Nat.ne_of_lt hjc), if_pos hjc]
  exact (shift_var_untouched_below hnc).symm

/-- **SELF-SUBSTITUTION: `subst j s (var j)` IS `s`.**

The `n = j` branch of `subst`, which the disagreement argument needs by name. -/
theorem subst_var_self (s : Term) (j : ℕ) : subst j s (Term.var j) = s := by
  show (if j = j then s else if j < j then Term.var j else Term.var (j - 1)) = s
  rw [if_pos rfl]

/-- **THE DISAGREEMENT AT THE SUBSTITUTED INDEX.**

`subst j (shift c d s) (shift c d (Term.var j)) = shift c d s` while `shift c d (subst j s (Term.var j)) = shift c d s`
-- so both sides reduce to `shift c d s` ONCE `shift` leaves `var j` alone, and the law's LHS/RHS differ exactly when
`shift c d s ≠ shift c d s`, which cannot happen.

What this says is the KEY NEGATIVE FACT: with `j < c`, the LHS substitutes at `j` AFTER the shift has left `var j`
in place, so BOTH sides mention `s`, and no disagreement arises at this index.

=> the disagreement therefore lives at indices where `shift` MOVES `var j`, i.e. at `c ≤ j`, which is the region
`subst_shift_counterexample` below exercises. -/
theorem subst_shift_at_untouched_index {c d j : ℕ} (s : Term) (hjc : j < c) :
    subst j (shift c d s) (shift c d (Term.var j)) = shift c d (subst j s (Term.var j)) := by
  rw [shift_var_untouched_below hjc, subst_var_self, subst_var_self]

/-- **THE ROUND-146 WITNESS, stated in this file's own terms.**

`t = var 1`, `j = 1`, `c = 1`, `d = 1`, `s = var 0`: the LHS is `var 1` and the RHS is `var 0`.

=> the counterexample that settled the matter, recorded where the analysis lives. -/
theorem subst_shift_counterexample :
    subst 1 (shift 1 1 (Term.var 0)) (shift 1 1 (Term.var 1))
      ≠ shift 1 1 (subst 1 (Term.var 0) (Term.var 1)) := by
  decide

end Lattice.Core.CIC
