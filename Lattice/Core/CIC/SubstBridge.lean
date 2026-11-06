/-
# `Core/CIC/SubstBridge.lean` -- the two substitution representations MEET (round 159)

## Why a bridge

**The tree now has TWO substitution representations:**

| representation | where | what it is |
|:--|:--|:--|
| **`subst : Nat -> Term -> Term -> Term`** | **`Substitution.lean` (round 135)** | **one index at a time** |
| **`inst : Subst -> Term -> Term`** | **`ParallelSubst.lean` (round 153)** | **a whole map `Nat -> Term` at once** |

**They coexist, and their relationship was never stated.**
**That is a real defect: `Reduction.lean` uses `subst`, the composition work uses `inst`, and nothing says they
agree.**

## The bridge

**`singleSubst j s : Subst` maps index `j` to `s`, leaves indices below `j` alone, and decrements those above --
which is EXACTLY what `subst j s` does, index by index.**

**=> `inst (singleSubst j s) t = subst j s t` connects them.**

## What is proved

| theorem | content |
|:--|:--|
| **`singleSubst_var`** | **the map's three cases match `subst`'s three lemmas** |
| **`inst_singleSubst`** | **`inst (singleSubst j s) t = subst j s t`, for EVERY term** |

**The `var` case is the three-way split that `subst_var_eq` / `subst_var_lt` / `subst_var_gt` already specify; the
structural cases are definitionally the same recursion on both sides.**

## What this file does NOT do

**It does not derive one representation's laws from the other's.**
**The point is the opposite: the bridge lets a fact proved with `inst` be USED against `subst` and vice versa, so
`Reduction.lean`'s `subst`-based statements are now connected to the parallel-substitution development.**

**It also makes `subst_shift_law` -- the one registered unproved obligation -- expressible as a statement about
`inst`, where the composition theorem (still open) may be the cleaner route.**
-/

import Mathlib
import Lattice.Core.CIC.ParallelSubst
import Lattice.Core.CIC.Substitution

namespace Lattice.Core.CIC

/-- **The substitution map that matches `subst j s`.**

**Index `j` maps to `s`; below it, indices stay; above it, they decrement -- exactly `subst`'s three cases.** -/
def singleSubst (j : ℕ) (s : Term) : Subst :=
  fun n => if n = j then s else if n < j then .var n else .var (n - 1)

/-- **The map's three cases ARE `subst`'s three lemmas.**

**`subst_var_eq`, `subst_var_lt` and `subst_var_gt` each match one branch, so the map is pointwise equal to what
`subst` does at a variable.** -/
theorem singleSubst_var (j n : ℕ) (s : Term) : singleSubst j s n = subst j s (.var n) := by
  unfold singleSubst
  rcases Nat.lt_trichotomy n j with h | h | h
  · -- `n < j`: the second branch, and `subst_var_lt`
    rw [if_neg (by omega : ¬ n = j), if_pos h, subst_var_lt s h]
  · -- `n = j`: the first branch, and `subst_var_eq`
    rw [if_pos h, h, subst_var_eq]
  · -- `j < n`: the third branch, and `subst_var_gt`
    rw [if_neg (by omega : ¬ n = j), if_neg (by omega : ¬ n < j), subst_var_gt s h]

/-- **Lifting the single-substitution map IS the single-substitution map at `j+1`.**

**`lift (singleSubst j s) = singleSubst (j+1) (shift 0 1 s)`.**

**This is what makes the BINDER case of the bridge work: `subst`'s binder step changes the parameters to
`(j+1, shift 0 1 s)`, and `inst`'s binder step LIFTS the map -- so the two agree exactly when lifting matches
that parameter change.**

**At index `0` both sides are `var 0`; at `k+1` the three branches must each correspond, and the third needs
`shift 0 1 (var (k-1)) = var (k+1-1)`.** -/
theorem lift_singleSubst (j : ℕ) (s : Term) :
    lift (singleSubst j s) = singleSubst (j + 1) (shift 0 1 s) := by
  funext n
  cases n with
  | zero =>
    show Term.var 0
      = (if (0 : ℕ) = j + 1 then shift 0 1 s
         else if (0 : ℕ) < j + 1 then Term.var 0 else Term.var (0 - 1))
    rw [if_neg (by omega : ¬ (0 : ℕ) = j + 1), if_pos (by omega : (0 : ℕ) < j + 1)]
  | succ k =>
    show shift 0 1 (singleSubst j s k)
      = (if k + 1 = j + 1 then shift 0 1 s
         else if k + 1 < j + 1 then Term.var (k + 1) else Term.var (k + 1 - 1))
    unfold singleSubst
    by_cases h1 : k = j
    · subst h1
      rw [if_pos rfl, if_pos rfl]
    · by_cases h2 : k < j
      · rw [if_neg h1, if_pos h2]
        rw [if_neg (by omega : ¬ k + 1 = j + 1), if_pos (by omega : k + 1 < j + 1)]
        exact shift_var_ge (by omega : ¬ k < (0 : ℕ))
      · rw [if_neg h1, if_neg h2]
        rw [if_neg (by omega : ¬ k + 1 = j + 1), if_neg (by omega : ¬ k + 1 < j + 1)]
        rw [shift_var_ge (by omega : ¬ k - 1 < (0 : ℕ))]
        congr 1
        omega
/-- **THE BRIDGE: instantiating with `singleSubst j s` IS `subst j s`.**

**`inst (singleSubst j s) t = subst j s t` for every term.**

**The `var` case is `singleSubst_var`; the four structural cases are the two recursions meeting definitionally,
because `subst` and `inst` both recurse into `app`, `lam`, `pi` and `letE` in the same shape.**

**=> the two representations are now PROVABLY the same where they should be, which lets a result about one be
cited about the other.** -/
theorem inst_singleSubst :
    ∀ (t : Term) (j : ℕ) (s : Term),
      inst (singleSubst j s) t = subst j s t := by
  intro t
  induction t with
  | sort k l => intro j s; rfl
  | const k => intro j s; rfl
  | var n => intro j s; exact singleSubst_var j n s
  | app f a ihf iha =>
    intro j s
    simp only [inst, subst, ihf j s, iha j s]
  | lam A b ihA ihb =>
    intro j s
    simp only [inst, subst, ihA j s]
    rw [lift_singleSubst, ihb (j + 1) (shift 0 1 s)]
  | pi A B ihA ihB =>
    intro j s
    simp only [inst, subst, ihA j s]
    rw [lift_singleSubst, ihB (j + 1) (shift 0 1 s)]
  | letE A t b ihA iht ihb =>
    intro j s
    simp only [inst, subst, ihA j s, iht j s]
    rw [lift_singleSubst, ihb (j + 1) (shift 0 1 s)]

end Lattice.Core.CIC
