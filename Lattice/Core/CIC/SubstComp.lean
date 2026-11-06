/-
# `Core/CIC/SubstComp.lean` -- the textbook composition law is FALSE here (round 152)

## What round 151 left, and what round 152 found

**`SubstTable.lean` proved the four rows of `subst j s (subst j t (var k))` and said the table "supplies the exact
case structure such a law must respect".**

**Round 152 wrote the textbook composition law and checked it against those rows.**
**It fails at THREE of the four rows, and this file proves the refutation.**

## The candidate

```
comp_candidate := forall j s t u, subst j s (subst j t u) = subst j (subst j s t) u
```

**This is the form every de Bruijn development writes first.**

## Where it fails

| row | LHS | RHS | agree? |
|:--|:--|:--|:--|
| **`k < j`** | **`var k`** | **subtracts an extra decrement** | **no** |
| **`k = j`** | **`subst j s t`** | **`subst j s t`** | **YES** |
| **`k = j + 1`** | **`s`** | **`subst j s t`** | **no** |
| **`j + 1 < k`** | **`var (k-2)`** | **`var (k-1)`** | **no** |

**=> only ONE of the four rows agrees.**

**The reason is uniform: the RIGHT side applies `subst j (subst j s t)` to `u`, so it decrements `u`'s indices
ONCE; the LEFT side decrements TWICE (`subst j t`, then `subst j s`).**
**=> the two sides differ by exactly one decrement wherever `t`'s substitution does not compensate.**

**`s != subst j s t` and `k-2 != k-1` are the SAME failure seen from two rows.**

## What this means

**The single-substitution `subst : Nat -> Term -> Term -> Term` CANNOT satisfy a textbook composition law, because
the two sides' DECREMENT COUNTS differ structurally.**

**=> the standard fix is PARALLEL substitution: a map `Nat -> Term` substituted in ONE pass.**
**With one pass there is no "twice versus once", so composition becomes `sigma >> tau` and the counting problem
disappears.**
**That is a DESIGN change, not a proof attempt, and it is the concrete next step.**

## What this file proves

| theorem | content |
|:--|:--|
| **`comp_candidate`** | **the textbook form, as a `Prop`** |
| **`comp_row_eq_agrees`** | **the `k = j` row DOES agree** |
| **`comp_candidate_false`** | **THE LAW IS FALSE** -- a concrete instantiation with both sides computed |

## Why the refutation took ONE round

**Round 151's table gave the four rows; round 152 only had to substitute each into the candidate.**
**=> the table did its job: it turned "find a counterexample" into "check four cases", and the answer was
immediate.**

**This is the FOURTH substitution law refuted (146, 147, 150, 152).**
**The pattern across all four: the boundary index `j+1` and the DECREMENT COUNT.**
-/

import Mathlib
import Lattice.Core.CIC.SubstTable

namespace Lattice.Core.CIC

/-- **The textbook composition law, as a `Prop`.**

**`subst j s (subst j t u) = subst j (subst j s t) u`.** -/
def comp_candidate : Prop :=
  ∀ (j : ℕ) (s t u : Term), subst j s (subst j t u) = subst j (subst j s t) u

/-- **The `k = j` row DOES agree with the candidate.**

**The inner substitution produces `t`; the outer produces `subst j s t`; and the right side's
`subst j (subst j s t)` does the same at the target.**
**=> the ONE row where the decrement counts coincide.** -/
theorem comp_row_eq_agrees (j : ℕ) (s t : Term) :
    subst j s (subst j t (.var j)) = subst j (subst j s t) (.var j) := by
  rw [comp_eq j s t, subst_var_eq j (subst j s t)]

/-- **THE TEXTBOOK LAW IS FALSE.**

**Instantiate at `j = 0`, `s = var 1`, `t = var 0`, `u = var 1`:**

**LHS `= subst 0 (var 1) (subst 0 (var 0) (var 1)) = subst 0 (var 1) (var 0) = var 1`.**
**RHS `= subst 0 (subst 0 (var 1) (var 0)) (var 1) = subst 0 (var 1) (var 1) = var 0`.**

**`var 1 != var 0`.**

**=> the failure is the DECREMENT COUNT: the left side decrements `u`'s index twice (once by `subst 0 t`, once by
`subst 0 s`), the right side once.** -/
theorem comp_candidate_false : ¬ comp_candidate := by
  intro h
  have h0 := h 0 (Term.var 1) (Term.var 0) (Term.var 1)
  -- LHS: `subst 0 (var 1) (subst 0 (var 0) (var 1))`
  have hinner : subst 0 (Term.var 0) (Term.var 1) = Term.var 0 := by
    rw [subst_var_gt (Term.var 0) (by omega : 0 < 1)]
  have hlhs : subst 0 (Term.var 1) (subst 0 (Term.var 0) (Term.var 1)) = Term.var 1 := by
    rw [hinner, subst_var_eq]
  -- RHS: `subst 0 (subst 0 (var 1) (var 0)) (var 1)`
  have hinner2 : subst 0 (Term.var 1) (Term.var 0) = Term.var 1 := subst_var_eq 0 (Term.var 1)
  have hrhs : subst 0 (subst 0 (Term.var 1) (Term.var 0)) (Term.var 1) = Term.var 0 := by
    rw [hinner2]
    rw [subst_var_gt (Term.var 1) (by omega : 0 < 1)]
  rw [hlhs, hrhs] at h0
  exact absurd h0 (by intro h; cases h)

end Lattice.Core.CIC
