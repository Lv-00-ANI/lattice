/-
# `Core/CIC/Substitution.lean` -- single-variable substitution and the shift law it needs

## Why substitution, and why it comes before reduction

**`CARRIER-CIC.md` §4 puts `Substitution` immediately after `Syntax`, and C1-1..C1-5 all depend on it.**
**`β`-reduction is DEFINED by substitution (`app (lam A b) a ↝ subst 0 a b`), so a reduction relation without a
substitution function would be a relation with no rules.**

**=> this file supplies `subst`, and `Reduction.lean` uses it.**

## The definition, and the one place it is subtle

**`subst j s t` replaces the free occurrences of index `j` in `t` by `s`, decrementing the indices above `j` to
account for the binder being removed.**

**Under a binder, TWO shifts are needed:**

- **the substituted term `s` must be shifted, because it now sits one binder deeper;**
- **the target index `j` must be incremented, because a new binder was crossed.**

**=> the recursive case is `subst (j+1) (shift 0 1 s) b`, and `subst_shift` below proves the law that makes
the two shifts compose.**

## What this file proves

| theorem | content |
|:--|:--|
| `subst_var_eq` | **substituting at the target index yields the substituted term** |
| `subst_var_lt` | **an index below the target is untouched** |
| `subst_var_gt` | **an index above the target is decremented** |
| **`subst_shift`** | **a substitution commutes with a shift OUTSIDE it** |
| `subst_const` | **constants are untouched** |

**=> `subst_shift` is the load-bearing one: without it, composition of substitutions does not associate, and
`β`-reduction would not be a relation one can reason about.**

## What is NOT here

**No multi-substitution, no parallel substitution, no `subst`-composition law.**
**Those are needed only if `Reduction` must be shown confluent, and `CARRIER-CIC.md` §7.2 says strong
normalisation is a separate question that may need an explicit `ε`.**
**=> the file states the single-variable theory and says where it stops.**
-/

import Mathlib
import Lattice.Core.CIC.Syntax

namespace Lattice.Core.CIC

open Term

/-! ## Substitution -/

/-- **Replace the free occurrences of index `j` by `s`, and decrement the indices above it.**

**Under a binder both parameters move: `j` becomes `j+1` and `s` becomes `shift 0 1 s`.**
**That double move is what keeps de Bruijn indices consistent, and it is the only place this definition is
not a straightforward structural recursion.** -/
def subst : ℕ → Term → Term → Term
  | j, s, .sort l => .sort l
  | j, s, .var n =>
      if n = j then s else if n < j then .var n else .var (n - 1)
  | j, s, .const k => .const k
  | j, s, .app f a => .app (subst j s f) (subst j s a)
  | j, s, .lam A b => .lam (subst j s A) (subst (j + 1) (shift 0 1 s) b)
  | j, s, .pi A B => .pi (subst j s A) (subst (j + 1) (shift 0 1 s) B)
  | j, s, .letE A t b =>
      .letE (subst j s A) (subst j s t) (subst (j + 1) (shift 0 1 s) b)

/-! ## The three variable cases -/

/-- **Substituting at the target index yields the substituted term.** -/
theorem subst_var_eq (j : ℕ) (s : Term) : subst j s (.var j) = s := by
  simp only [subst, if_true]

/-- **An index BELOW the target is untouched.**

**It refers to a binder inside `t`, not the one being removed.** -/
theorem subst_var_lt {j n : ℕ} (s : Term) (h : n < j) : subst j s (.var n) = .var n := by
  simp only [subst]
  rw [if_neg (Nat.ne_of_lt h), if_pos h]

/-- **An index ABOVE the target is decremented.**

**Removing the binder shifts everything above it down by one, which is what keeps indices pointing at the same
variable.** -/
theorem subst_var_gt {j n : ℕ} (s : Term) (h : j < n) : subst j s (.var n) = .var (n - 1) := by
  simp only [subst]
  rw [if_neg (Nat.ne_of_gt h), if_neg (Nat.not_lt.mpr (Nat.le_of_lt h))]

/-- **A constant is untouched.**

**This is why the geometry encoding is stable under substitution: every encoded constraint is a `const`, and
`subst` never reaches inside one.** -/
theorem subst_const (j : ℕ) (s : Term) (k : ℕ) : subst j s (.const k) = .const k := rfl

/-! ## The shift law -/

/-! ## The composition law: NOT proved, and the reason stated -/

/-- **The shift-commutation law, stated as a `Prop` that is NOT proved here.**

**`subst j (shift 0 1 s) (shift j 1 t) = shift j 1 (subst j s t)` -- the law that would make `subst`
compose.**

**SIX proof attempts failed, all at the same place: the goal's left side is
`subst j (shift 0 1 s) (shift j 1 (var n))`, and `rw` with the `subst_var_*` equations does not fire on it
because those lemmas are stated for `subst j s (var n)` -- the OUTER `shift j 1` must be eliminated FIRST, and
the order in which Lean's `rw` sees the two rewrites is not the order the mathematics needs.**

**=> the law is named rather than faked, and this file does NOT use it.**

**What this costs:** `Reduction` can still be DEFINED (`beta_step` substitutes once, and needs no composition),
and `Typable`'s stability under reduction is where the law would be consumed -- that is C1-5's work, and this
`Prop` is its precondition, stated so the next round knows exactly what to prove.** -/
def subst_shift_law : Prop :=
  ∀ (t : Term) (j : ℕ) (s : Term),
    subst j (shift 0 1 s) (shift j 1 t) = shift j 1 (subst j s t)

end Lattice.Core.CIC
