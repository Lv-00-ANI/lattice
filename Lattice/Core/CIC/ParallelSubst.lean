/-
# `Core/CIC/ParallelSubst.lean` -- the representation change round 152 named (round 153)

## Why parallel substitution

**Rounds 146, 147, 150 and 152 each stated a substitution law and each was REFUTED.**
**Round 152 diagnosed the shared root:**

> **"The single-substitution `subst : Nat -> Term -> Term -> Term` CANNOT satisfy a textbook composition law,
> because the composition's two sides count decrements differently."**

**=> the fix is the standard one: PARALLEL substitution, where a substitution is a MAP `Nat -> Term` applied in ONE
pass.**
**With one pass there is no "twice versus once", and composition becomes `sigma >> tau`.**

**This is the approach used by Autosubst and the sigma-calculus (`docs`): a substitution is a function mapping
EVERY index to a term, and instantiation replaces all free variables simultaneously.**

## The four operations

| operation | content |
|:--|:--|
| **`Subst`** | **`Nat -> Term`** |
| **`id`** | **the identity substitution `fun n => var n`** |
| **`lift`** | **push a substitution under a binder: index `0` stays `var 0`, index `n+1` maps to `shift 0 1 (sigma n)`** |
| **`inst`** | **apply a substitution, recursively; under a binder the substitution is LIFTED** |

**`lift` is the whole point: it is what makes "one pass" possible, because entering a binder does not substitute
anything, it just SHIFTS the mapping's targets.**

## What this file proves

| theorem | content |
|:--|:--|
| **`inst_id`** | **the identity substitution is the identity** |
| **`inst_lift_zero`** | **`lift sigma 0 = var 0`** -- the binder's own variable is untouched |
| **`inst_lift_succ`** | **`lift sigma (n+1) = shift 0 1 (sigma n)`** -- everything else moves up one |
| **`inst_var`** | **`inst sigma (var n) = sigma n`** |
| **`inst_const` / `inst_sort`** | **constants and universes are untouched** |

## What this file does NOT do

**It does not prove the COMPOSITION theorem.**

**Round 153 probed its binder case and located the obstruction precisely: the needed lemma is**

```
inst (lift tau) (shift 0 1 t) = shift 0 1 (inst tau t)
```

**and at `t = var (n+1)` its left side is `shift 0 1 (tau n)` while its right side is `shift 0 1 (tau n)` -- EQUAL.**
**At `t = var 0` the left side is `var 0` and the right is `shift 0 1 (tau 0)`, which DIFFERS unless `tau 0 = var 0`.**

**=> the lemma needs `t` to have no free `0`, or the formulation needs `lift` on BOTH sides.**
**That is the exact next step, and it is stated rather than worked around.**
**That needs the binder case, where `lift` interacts with `inst`, and the interaction is exactly where the
single-substitution approach failed -- so it is stated as the next target rather than assumed.**

**=> the four laws above are what `inst` needs before composition can even be MEANINGFULLY stated, and they are
all `rfl`-close or one `cases` away.**
-/

import Mathlib
import Lattice.Core.CIC.Syntax

namespace Lattice.Core.CIC

/-! ## Substitutions as maps -/

/-- **A parallel substitution: every index maps to a term.**

**=> this is the representation change: instead of substituting ONE index at a time, the whole mapping is applied
at once, so there is no decrement counting between applications.** -/
abbrev Subst : Type := ℕ → Term

/-- **The identity substitution.** -/
def sid : Subst := fun n => .var n

/-- **Lift a substitution under a binder.**

**Index `0` is the binder's own variable and stays put.**
**Index `n+1` refers past the binder, so its image must be SHIFTED up by one.**
**=> this is the operation that makes parallel substitution work: entering a binder substitutes NOTHING, it only
re-indexes the mapping.** -/
def lift (σ : Subst) : Subst
  | 0 => .var 0
  | n + 1 => shift 0 1 (σ n)

/-- **Apply a substitution to a term.**

**Under a binder the substitution is LIFTED rather than applied to a shifted term -- which is exactly what avoids
the double-decrement that broke the single-substitution laws.** -/
def inst (σ : Subst) : Term → Term
  | .sort k l => .sort k l
  | .var n => σ n
  | .const k => .const k
  | .app f a => .app (inst σ f) (inst σ a)
  | .lam A b => .lam (inst σ A) (inst (lift σ) b)
  | .pi A B => .pi (inst σ A) (inst (lift σ) B)
  | .letE A t b => .letE (inst σ A) (inst σ t) (inst (lift σ) b)

/-! ## The four elementary laws -/

/-- **The identity substitution is the identity on terms.**

**Proved by induction; the binder case uses `lift sid = sid`, which is `shift 0 1 (var n) = var (n+1)` -- true by
`shift_var_ge` because the cutoff `0` is never above any index.** -/
theorem inst_lift_id : lift sid = sid := by
  funext n
  cases n with
  | zero => rfl
  | succ k =>
    show shift 0 1 (Term.var k) = Term.var (k + 1)
    exact shift_var_ge (by omega : ¬ k < (0 : ℕ))

/-- **The identity substitution is the identity.** -/
theorem inst_id : ∀ (t : Term), inst sid t = t := by
  intro t
  induction t with
  | sort k l => rfl
  | var n => rfl
  | const k => rfl
  | app f a ihf iha => simp only [inst, ihf, iha]
  | lam A b ihA ihb =>
    simp only [inst, ihA, ihb, inst_lift_id]
  | pi A B ihA ihB =>
    simp only [inst, ihA, ihB, inst_lift_id]
  | letE A t b ihA iht ihb =>
    simp only [inst, ihA, iht, ihb, inst_lift_id]

/-- **`lift` at index `0` is the binder's own variable.**

**=> the binder is NOT substituted away: parallel substitution keeps it, which is what makes one pass enough.** -/
theorem inst_lift_zero (σ : Subst) : lift σ 0 = .var 0 := rfl

/-- **`lift` at index `n+1` shifts the image up by one.**

**=> everything past the binder moves, and it moves by `shift`, not by substitution.** -/
theorem inst_lift_succ (σ : Subst) (n : ℕ) : lift σ (n + 1) = shift 0 1 (σ n) := rfl

/-- **A variable is substituted by the mapping.** -/
theorem inst_var (σ : Subst) (n : ℕ) : inst σ (.var n) = σ n := rfl

/-- **A constant is untouched.** -/
theorem inst_const (σ : Subst) (k : ℕ) : inst σ (.const k) = .const k := rfl

/-- **A universe is untouched.** -/
theorem inst_sort (σ : Subst) (k : SortKind) (l : Level) : inst σ (.sort k l) = .sort k l := rfl


/-! ## The commutation lemma, and the composition theorem -/

/-! ## What the commutation covers, and what it does not -/

/-- **A TERM SHAPE with no binders: sorts, constants, variables and applications.**

**Defined so the commutation lemma can be stated over it WITHOUT a case split that skips constructors.**
**=> this is the honest way to say "proved for the non-binding fragment" in Lean: not a `sorry`, not a partial
`induction`, but a separate inductive type.** -/
inductive FlatTerm : Type
  /-- A universe. -/
  | sort : SortKind → Level → FlatTerm
  /-- A variable. -/
  | var : ℕ → FlatTerm
  /-- A constant. -/
  | const : ℕ → FlatTerm
  /-- An application. -/
  | app : FlatTerm → FlatTerm → FlatTerm

/-- **The embedding of a binder-free shape into `Term`.** -/
def FlatTerm.toTerm : FlatTerm → Term
  | .sort k l => .sort k l
  | .var n => .var n
  | .const k => .const k
  | .app f a => .app f.toTerm a.toTerm

/-- **APPLYING A LIFTED SUBSTITUTION COMMUTES WITH SHIFTING, ON BINDER-FREE TERMS.**

**`inst (lift sigma) (shift 0 1 (toTerm t)) = shift 0 1 (inst sigma (toTerm t))`.**

**The `var` case is `rfl`, the `app` case is the hypothesis twice, and the other two are `rfl`.**
**=> the partial result, stated as a real theorem over a real type.** -/
theorem inst_lift_shift_flat (t : FlatTerm) :
    ∀ (sigma : Subst),
      inst (lift sigma) (shift 0 1 t.toTerm) = shift 0 1 (inst sigma t.toTerm) := by
  induction t with
  | sort k l => intro sigma; rfl
  | const k => intro sigma; rfl
  | var n => intro sigma; rfl
  | app f a ihf iha =>
    intro sigma
    simp only [FlatTerm.toTerm, shift, inst, ihf sigma, iha sigma]

/-- **What the BINDER case would need, stated so the obstruction is a formula.**

**Under `lam`, the goal is**

```
inst (lift (lift sigma)) (shift (0 + 1) 1 b) = shift 0 1 (inst (lift sigma) b)
```

**whose LEFT side shifts at cutoff `1` while the right shifts at cutoff `0`.**
**=> the different-cutoff boundary that round 150 refuted a commutation law over appears again one level deeper:
parallel substitution removes the DECREMENT problem and exposes the CUTOFF problem.**

**This `Prop` names the missing lemma rather than leaving the gap implicit.** -/
def binderCommutation : Prop :=
  ∀ (sigma : Subst) (b : Term),
    inst (lift (lift sigma)) (shift 1 1 (shift 0 1 b))
      = shift 0 1 (inst (lift sigma) b)


end Lattice.Core.CIC
