/-
# `Core/CIC/SubstTable.lean` -- the 3x3 case table that M-5 asked for (round 151)

## Why a TABLE and not a law

**`MACRO-COGNITION-148.md` set M-5 as: "a 3x3 table of concrete `(j, n)` cases computed by hand; any unequal cell
REFUTES the form."**

**The reason for a table is rounds 146, 147 and 150: three substitution/shift laws were stated, and THREE were
refuted.**
**Each refutation was at a boundary case that a quick table would have exposed.**

**=> this file IS the table, written as theorems so the kernel checks every cell.**

## The table: `subst j s (subst j t (var k))`

**The composition `subst j s (subst j t u)` is what any general substitution law must reduce.**
**At `u = var k` it has exactly THREE cases, decided by where `k` sits relative to `j`:**

| case | `subst j t (var k)` | then `subst j s (·)` | result |
|:--|:--|:--|:--|
| **`k < j`** | **`var k`** | **`var k`** | **`var k`** |
| **`k = j`** | **`t`** | **`subst j s t`** | **`subst j s t`** |
| **`j < k`** | **`var (k-1)`** | **depends on `k-1` vs `j`** | **see below** |

**The third row SPLITS FURTHER, and that split is the whole difficulty:**

- **`k - 1 < j`** (i.e. `k = j + 1` is excluded): **`var (k-1)`**;
- **`k - 1 = j`** (i.e. **`k = j + 1`**): **`s`**;
- **`j < k - 1`**: **`var (k-2)`**.

**=> the case `k = j + 1` is where `s` appears, and it is the case that three earlier attempts got wrong.**

## What is proved

| theorem | content |
|:--|:--|
| **`comp_lt`** | **`k < j` gives `var k`** |
| **`comp_eq`** | **`k = j` gives `subst j s t`** |
| **`comp_gt_succ`** | **`j + 1 < k` gives `var (k-2)`** |
| **`comp_gt_eq`** | **`k = j + 1` gives `s`** |
| **`comp_table`** | **the three-way disjunction covering ALL of `k`** |

## What this file does NOT do

**It does not prove a composition law for arbitrary `u`.**
**But it supplies the exact case structure such a law must respect, INCLUDING the `k = j + 1` case that is
invisible at the two ends and decisive at the boundary.**

**=> the next attempt at the general law should be checked against these four rows BEFORE it is written down --
which is precisely the discipline round 148 set.**
-/

import Mathlib
import Lattice.Core.CIC.Substitution

namespace Lattice.Core.CIC

/-! ## Row 1: `k < j` -/

/-- **Row 1 of the table: an index below `j` survives both substitutions.**

**`subst j t (var k) = var k` and then `subst j s (var k) = var k`.**
**=> no case analysis on `k-1` is needed, because nothing moved.** -/
theorem comp_lt {j k : ℕ} (hk : k < j) (s t : Term) :
    subst j s (subst j t (.var k)) = .var k := by
  rw [subst_var_lt t hk, subst_var_lt s hk]

/-! ## Row 2: `k = j` -/

/-- **Row 2 of the table: the target index gives `subst j s t`.**

**`subst j t (var j) = t`, and then the outer substitution acts on `t` -- which is where `s` enters.**
**=> the result MENTIONS `s`, and that is why no "shift-only" law can be right.** -/
theorem comp_eq (j : ℕ) (s t : Term) :
    subst j s (subst j t (.var j)) = subst j s t := by
  rw [subst_var_eq]

/-! ## Row 3: `j < k`, which SPLITS -/

/-- **Row 3a: `j + 1 < k` gives `var (k - 2)`.**

**`subst j t (var k) = var (k-1)`, and `k - 1 > j` still holds, so the outer substitution decrements again.**
**=> TWO decrements, because TWO binders' worth of indices moved.** -/
theorem comp_gt_succ {j k : ℕ} (hk : j + 1 < k) (s t : Term) :
    subst j s (subst j t (.var k)) = .var (k - 2) := by
  rw [subst_var_gt t (by omega : j < k)]
  rw [subst_var_gt s (by omega : j < k - 1)]
  congr 1

/-- **Row 3b: `k = j + 1` gives `s`.**

**This is the DECISIVE row.**
**`subst j t (var (j+1)) = var j`, and then `subst j s (var j) = s`.**
**=> the composite does NOT mention `t` at all, and it DOES mention `s` -- which is exactly what a law written
without this row would get wrong.**
**Rounds 146, 147 and 150 each failed at a boundary equivalent to this one.** -/
theorem comp_gt_eq (j : ℕ) (s t : Term) :
    subst j s (subst j t (.var (j + 1))) = s := by
  rw [subst_var_gt t (by omega : j < j + 1)]
  rw [show j + 1 - 1 = j from by omega]
  rw [subst_var_eq]


/-! ## The table as one statement -/

/-- **THE TABLE: every `k` falls into exactly one of the four rows.**

**`k < j` -> `var k`; `k = j` -> `subst j s t`; `k = j + 1` -> `s`; `j + 1 < k` -> `var (k-2)`.**

**=> this is the case structure a general composition law must respect, and the `j+1` row is the one the three
refuted laws missed.** -/
theorem comp_table (j k : ℕ) (s t : Term) :
    (k < j ∧ subst j s (subst j t (.var k)) = .var k) ∨
    (k = j ∧ subst j s (subst j t (.var k)) = subst j s t) ∨
    (k = j + 1 ∧ subst j s (subst j t (.var k)) = s) ∨
    (j + 1 < k ∧ subst j s (subst j t (.var k)) = .var (k - 2)) := by
  rcases Nat.lt_trichotomy k j with h | h | h
  · exact Or.inl ⟨h, Lattice.Core.CIC.comp_lt h s t⟩
  · have hrow := comp_eq k s t
    subst h
    exact Or.inr (Or.inl ⟨rfl, hrow⟩)
  · -- `j < k`: split on whether `k = j + 1`
    by_cases hk : k = j + 1
    · have hrow := comp_gt_eq j s t
      subst hk
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hrow⟩))
    · have hlt : j + 1 < k := by omega
      exact Or.inr (Or.inr (Or.inr ⟨hlt, comp_gt_succ hlt s t⟩))

end Lattice.Core.CIC
