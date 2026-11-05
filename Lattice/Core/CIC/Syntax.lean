/-
# `Core/CIC/Syntax.lean` -- the calculus of inductive constructions, as the symbolic carrier

## Why this file exists

**`CARRIER-CIC.md` §0: the project's principal symbolic carrier moves from `GeoConstraint n` to a CIC term.**
**Geometry is not deleted -- it is ENCODED into CIC (`Core/CIC/Encode/Geometry.lean`) and demoted to one
`Domains/Geometry` instance.**

**The reason is in §1.1: seven symptoms with one root.** **The symbolic model's canonical FORM was welded to
geometry, and geometry's expressive power cannot support the obligations T0-T8 name:**
**T0's domain is empty (`no_specSolver`), T1's conclusion omits its input, T3's round trip is a structure
FIELD, and so on.**

## What this file provides, and what it deliberately does not

**This is SYNTAX: terms, universe levels, de Bruijn indices, and the operations that do not need types.**

| declaration | content |
|:--|:--|
| `Level` | **universe levels: `zero`, `succ`, `max`, `imax`, `param`** |
| `Term` | **the term syntax: `sort`, `var`, `const`, `app`, `lam`, `pi`, `let`** |
| `shift` | **de Bruijn shifting, with the cutoff that makes it total** |
| `shift_zero` | **shifting by zero is the identity** |
| `shift_shift` | **two shifts compose additively** |

**=> the two shift laws are the first NON-`rfl` facts in the CIC layer, and they are what every later
substitution lemma builds on.**
**A layer whose only contents were constructors would pass `lake build` and prove nothing.**

## What is NOT here, and why the plan is reordered

**`CARRIER-CIC.md`'s §4 lists `Substitution`, `Reduction`, `Typing`, `Normalization` in that order.**
**`CARRIER-REPLACEMENT.md` §2 (V1/V2) makes TYPING and ENCODING the acceptance criterion.**

**=> `Reduction` and `Normalization` are deferred: V2 (`encode_sound`) needs `Typable`, not `β`-reduction.**
**Consequently `shift` lives here, in `Syntax`, rather than in a later `Substitution` file -- it is a
SYNTACTIC operation and nothing about it needs types.**

## The design choice that matters: de Bruijn, not names

**Names need capture-avoiding substitution, which needs a freshness condition, which needs a decidable
equality on an infinite supply.**
**de Bruijn indices remove the whole problem: substitution is arithmetic plus a shift, and `shift_shift` below is
the law that makes it work.**

**=> the file pays for that choice with `shift`'s cutoff parameter, and buys the absence of alpha-equivalence.
The trade is stated because a reader will meet the cutoff repeatedly.**
-/

import Mathlib

namespace Lattice.Core.CIC

/-! ## Universe levels -/

/-- **Universe levels.**

**`param` is a level VARIABLE: the encoding of geometry needs no level polymorphism, but the type former `Pi`
does, so the syntax carries the case even though nothing here instantiates it.** -/
inductive Level : Type
  /-- The bottom universe. -/
  | zero : Level
  /-- The successor. -/
  | succ : Level → Level
  /-- The maximum. -/
  | max : Level → Level → Level
  /-- The impredicative maximum. -/
  | imax : Level → Level → Level
  /-- A level variable. -/
  | param : ℕ → Level
  deriving DecidableEq

/-! ## Terms -/

/-- **The term syntax.**

**`var n` is the de Bruijn index `n`, counted from the innermost binder.**
**`const k` is a named constant, which is where encoded constraints live: a `GeoConstraint` becomes a closed
term with a constant head, so it needs no free-variable bookkeeping.**
**`sort l` is a universe; `pi` and `lam` bind one variable each; `let` binds one and substitutes immediately in
the body.** -/
inductive Term : Type
  /-- A universe. -/
  | sort : Level → Term
  /-- A de Bruijn variable. -/
  | var : ℕ → Term
  /-- A named constant. -/
  | const : ℕ → Term
  /-- Application. -/
  | app : Term → Term → Term
  /-- Abstraction: `lam A b` binds one variable in `b`. -/
  | lam : Term → Term → Term
  /-- Dependent product: `pi A B` binds one variable in `B`. -/
  | pi : Term → Term → Term
  /-- Local definition: `let A t b` binds `t` in `b`. -/
  | letE : Term → Term → Term → Term
  deriving DecidableEq

/-! ## Shifting -/

/-- **de Bruijn shifting, with a cutoff.**

**`shift c d t` adds `d` to every FREE index `≥ c`; indices below the cutoff are bound inside `t` and stay put.**
**The cutoff is not a technicality: without it, shifting under a binder would capture.** -/
def shift : ℕ → ℕ → Term → Term
  | c, d, .sort l => .sort l
  | c, d, .var n => if n < c then .var n else .var (n + d)
  | c, d, .const k => .const k
  | c, d, .app f a => .app (shift c d f) (shift c d a)
  | c, d, .lam A b => .lam (shift c d A) (shift (c + 1) d b)
  | c, d, .pi A B => .pi (shift c d A) (shift (c + 1) d B)
  | c, d, .letE A t b => .letE (shift c d A) (shift c d t) (shift (c + 1) d b)

/-- **`shift` on a variable BELOW the cutoff leaves it alone.**

**The bound indices are the ones the binders own; shifting them would capture.** -/
theorem shift_var_lt {c d n : ℕ} (h : n < c) : shift c d (.var n) = .var n := by
  simp only [shift]
  rw [if_pos h]

/-- **`shift` on a variable AT OR ABOVE the cutoff moves it.**

**The free indices are the ones that must follow their binding term through the shift.** -/
theorem shift_var_ge {c d n : ℕ} (h : ¬ n < c) : shift c d (.var n) = .var (n + d) := by
  simp only [shift]
  rw [if_neg h]

/-- **Shifting by zero is the identity.**

**This is the first NON-`rfl` fact of the CIC layer: the `var` case is an `if`, so it needs `Nat.lt_irrefl`
and `Nat.add_zero` rather than definitional unfolding.**
**=> a layer whose shifting law were `rfl` would mean the cutoff was doing nothing.** -/
theorem shift_zero (c : ℕ) (t : Term) : shift c 0 t = t := by
  induction t generalizing c with
  | sort l => rfl
  | var n =>
    by_cases hn : n < c
    · rw [shift_var_lt hn]
    · rw [shift_var_ge hn, Nat.add_zero]
  | const k => rfl
  | app f a ihf iha =>
    simp only [shift]
    rw [ihf c, iha c]
  | lam A b ihA ihb =>
    simp only [shift]
    rw [ihA c, ihb (c + 1)]
  | pi A B ihA ihB =>
    simp only [shift]
    rw [ihA c, ihB (c + 1)]
  | letE A t b ihA iht ihb =>
    simp only [shift]
    rw [ihA c, iht c, ihb (c + 1)]

/-- **Two shifts compose additively.**

**`shift c d₁ (shift c d₂ t) = shift c (d₁ + d₂) t`.**
**The `var` case is where the cutoff earns its keep: the outer `if` decides on `n`, the inner on `n + d₂`, and
the two `if`s must be reconciled.**
**=> this is the law substitution will consume, and it is the reason the cutoff is a parameter rather than a
constant `0`.** -/
theorem shift_shift (c d₁ d₂ : ℕ) (t : Term) :
    shift c d₁ (shift c d₂ t) = shift c (d₁ + d₂) t := by
  induction t generalizing c with
  | sort l => rfl
  | var n =>
    by_cases hn : n < c
    · -- the index is bound, so the inner shift leaves it and the outer one does too
      rw [shift_var_lt hn, shift_var_lt hn, shift_var_lt hn]
    · -- the index is free: the inner shift makes it `n + d₂`, still `≥ c`
      have hn' : ¬ n + d₂ < c := by omega
      rw [shift_var_ge hn, shift_var_ge hn', shift_var_ge hn]
      congr 1
      omega
  | const k => rfl
  | app f a ihf iha =>
    simp only [shift]
    rw [ihf c, iha c]
  | lam A b ihA ihb =>
    simp only [shift]
    rw [ihA c, ihb (c + 1)]
  | pi A B ihA ihB =>
    simp only [shift]
    rw [ihA c, ihB (c + 1)]
  | letE A t b ihA iht ihb =>
    simp only [shift]
    rw [ihA c, iht c, ihb (c + 1)]

end Lattice.Core.CIC
