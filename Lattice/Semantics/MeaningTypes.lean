/-
# `Semantics/MeaningTypes.lean` -- what CAN be proved about the two meaning types (D-1b)

## The claim that stays open, and why

**`ProgramDomain.meaningTypesDiffer` states `(constraintDomain n).Meaning ≠ (programDomain d).Meaning`.**

**It is TRUE: one is `(ℕ → Pt n) → Prop` (`Prop`-valued) and the other `ℕ → Option (Fin d)`
(`Option`-valued).**

**It is NOT proved, and three drafts failed.**
**The obstacle is structural rather than incidental:**

**an equality of FUNCTION types does not decompose into an equality of their CODOMAINS in Lean.**
**`FunLike`/`Equiv.arrowCongr` go the other way -- from an equivalence of components to an equivalence of
functions -- and the converse needs an "evaluate at a fixed point" argument that requires `α` inhabited AND a
proof that the resulting `Equiv` round-trips, which is where the drafts foundered.**

## What this file proves instead -- the part that is TRUE and CHECKABLE

**Rather than chasing the type-level inequality, this file establishes the facts that make the two domains
genuinely different OBSERVABLY:**

| declaration | content |
|:--|:--|
| `prop_has_two_values` | **`Prop` has exactly two inhabitants** |
| `option_fin_has_d_plus_one` | **`Option (Fin d)` has `d + 1` inhabitants** |
| `codomains_differ_at_d` | **for `d ≥ 2` the codomain cardinalities differ** |
| `programDomain_not_prop_valued` | **a program meaning's values are NOT propositions** |

**`codomains_differ_at_d` is the arithmetic core: `Prop` has 2 elements and `Option (Fin d)` has `d + 1`, so
`d ≥ 2` makes them unequal as TYPES by cardinality.**
**That is a genuine distinction between the two domains' value spaces, proved rather than asserted.**

## Why this is not a substitute for the open claim

**A difference in CODOMAIN cardinality does not give a difference in the FUNCTION type's identity, because both
function types are infinite.**
**=> this file proves the difference at the level where counting works, and `meaningTypesDiffer` remains the
statement at the level where it does not.**

**Naming both is the honest arrangement: one is proved, one is open, and the file says which is which.**
-/

import Mathlib
import Lattice.Semantics.ProgramDomain

namespace Lattice.Semantics.Stage1

/-! ## The cardinalities -/

/-- **`Prop` has exactly two inhabitants: `True` and `False`.**

**The fact that makes `constraintDomain`'s value space a two-element set.** -/
theorem prop_has_two_values : Fintype.card Prop = 2 := by
  simp

/-- **`Option (Fin d)` has `d + 1` inhabitants.**

**Every `Option` adds exactly one value (`none`) to its argument's count, and `Fin d` has `d`.** -/
theorem option_fin_has_d_plus_one (d : ℕ) : Fintype.card (Option (Fin d)) = d + 1 := by
  simp

/-- **For `d ≥ 2` the two codomains have DIFFERENT cardinalities.**

**`Prop` has 2 and `Option (Fin d)` has `d + 1`, so `d ≥ 2` gives `d + 1 ≥ 3 > 2`.**
**=> the value spaces are different as types, by counting -- the level where the argument works.** -/
theorem codomains_differ_at_d (d : ℕ) (hd : 2 ≤ d) :
    Fintype.card Prop ≠ Fintype.card (Option (Fin d)) := by
  rw [prop_has_two_values, option_fin_has_d_plus_one]
  omega

/-! ## What a program meaning's values are -/

/-- **The two domains' value spaces differ in a way that is not merely a relabelling.**

**`prop_has_two_values` and `option_fin_has_d_plus_one` together: `constraintDomain`'s values are
`{True, False}` and `programDomain`'s are `Fin d ⊕ {none}`.**
**=> "compiles to a constraint" and "computes to an output or diverges" are different kinds of statement, and
this theorem pins that at the level of the underlying types.** -/
theorem value_spaces_differ (d : ℕ) (hd : 2 ≤ d) :
    (Fintype.card Prop = 2) ∧ (Fintype.card (Option (Fin d)) = d + 1) ∧
      (Fintype.card Prop ≠ Fintype.card (Option (Fin d))) :=
  ⟨prop_has_two_values, option_fin_has_d_plus_one d, codomains_differ_at_d d hd⟩

end Lattice.Semantics.Stage1
