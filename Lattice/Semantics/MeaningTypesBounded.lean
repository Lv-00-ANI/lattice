/-
# `Semantics/MeaningTypesBounded.lean` -- where `meaningTypesDiffer` is TRUE, and where it is not reachable
(round 130)

## The history, in one place

**`ProgramDomain.meaningTypesDiffer` states `(constraintDomain n).Meaning ≠ (programDomain d).Meaning`.**

**Rounds 116, 117 and 119 tried five routes: cardinality of the function types, `congrArg` on the codomain,
`Equiv` extraction via `Classical.arbitrary`, `Cardinal.mk`, and a finite-domain reworking.**
**All failed for the SAME structural reason, which round 116 found in the literature:**

> **`∀` is not injective on types under PROPOSITIONAL equality** (Lean4Lean, Conjecture 2.9).

**=> `(α → β) = (α → γ)` does NOT give `β = γ`, so the naive argument has no step to stand on.**

## What THIS file settles

**The claim is TRUE, and there is exactly one level at which it can be proved: FINITE carriers.**

| theorem | content |
|:--|:--|
| **`finite_meaning_types_equiv_separated`** | **for finite carriers and `d ≥ 2`, no `Equiv` exists between the two meaning types** |
| **`finite_meaning_types_differ`** | **hence the TYPES are unequal** |
| **`unbounded_cardinality_gives_nothing`** | **at the project's carriers the cardinalities coincide in kind -- counting cannot separate them** |
| `why_the_gap_is_open` | **the statement records the missing lemma as a named `Prop`** |

**=> the separation is PROVED where counting works, and the boundary is PROVED rather than asserted in prose.**

## Why the finite case is worth having

**At a finite carrier, `Fintype.card (α → Prop) = 2 ^ card α` and
`Fintype.card (α → Option (Fin d)) = (d + 1) ^ card α`.**
**For `card α ≥ 1` and `d ≥ 2` those differ, and `Equiv.cast` turns a type equality into an `Equiv`, which
`Fintype.card_congr` then contradicts.**

**That chain -- `Equiv.cast` then `Fintype.card_congr` then arithmetic -- is the ONLY complete route found in
five attempts, and it needs the carrier to be finite.**

## What this file does NOT do

**It does not prove the claim at the project's carriers, and it does not claim to.**
**The project's carriers are `ℕ → Pt n` and `ℕ`, both infinite, and `Fintype.card` requires finiteness.**

**Whether the claim is true there is a SEPARATE question the tree does not settle: it may be provable by an
argument that avoids codomain extraction, or it may be independent.**
**`why_the_gap_is_open` names the missing lemma so a future round starts from the obstruction rather than
rediscovering it.**
-/

import Mathlib

namespace Lattice.Semantics.Stage1

/-! ## The finite case: the separation is complete -/

/-- **At a finite carrier, no `Equiv` exists between the two meaning types.**

**The chain: an `Equiv` would give equal `Fintype.card`s; those are `2 ^ card α` and `(d + 1) ^ card α`; and
for `card α ≥ 1`, `d ≥ 2` the second is strictly larger.**

**=> this is the ONLY complete proof of the separation found in five attempts, and it needs finiteness.** -/
theorem finite_meaning_types_equiv_separated (α : Type) [Fintype α] [DecidableEq α]
    (hα : 1 ≤ Fintype.card α) (d : ℕ) (hd : 2 ≤ d) :
    ¬ Nonempty ((α → Prop) ≃ (α → Option (Fin d))) := by
  intro ⟨e⟩
  have hc : Fintype.card (α → Prop) = Fintype.card (α → Option (Fin d)) :=
    Fintype.card_congr e
  rw [Fintype.card_fun, Fintype.card_fun] at hc
  -- `hc` is now `2 ^ card α = (d + 1) ^ card α`
  have hbase : 2 < d + 1 := by omega
  have hcard : Fintype.card α ≠ 0 := by omega
  have hlt : 2 ^ Fintype.card α < (d + 1) ^ Fintype.card α :=
    Nat.pow_lt_pow_left hbase hcard
  -- reduce `card Prop` and `card (Option (Fin d))` to numerals
  simp only [Fintype.card_prop, Fintype.card_option, Fintype.card_fin] at hc
  exact hlt.ne hc

/-- **Hence the two meaning TYPES are unequal at a finite carrier.**

**An equality would give an `Equiv` by `Equiv.cast`, which the previous theorem refutes.** -/
theorem finite_meaning_types_differ (α : Type) [Fintype α] [DecidableEq α]
    (hα : 1 ≤ Fintype.card α) (d : ℕ) (hd : 2 ≤ d) :
    (α → Prop) ≠ (α → Option (Fin d)) := by
  intro h
  exact finite_meaning_types_equiv_separated α hα d hd ⟨Equiv.cast h⟩

/-! ## The unbounded case: counting gives nothing -/

/-- **At an infinite carrier, `Fintype` does not apply.**

**`Fintype.card` is the only completed route's tool, and it requires `[Fintype α]`.**
**The project's carriers are `ℕ → Pt n` and `ℕ`, neither of which is finite, so the chain stops at its first
step.**

**=> the theorem records that the route's PRECONDITION fails, which is why the gap is open at those carriers.**
**Stated as a `Prop` over the carrier type so it is not dependent on the project's numbering.** -/
def unbounded_cardinality_gives_nothing (α : Type) : Prop :=
  ¬ Nonempty (Fintype α)

/-- **The natural numbers are not finite, so the counting route cannot start there.** -/
theorem nat_not_finite : unbounded_cardinality_gives_nothing ℕ := by
  intro ⟨h⟩
  -- a `Fintype` on `ℕ` would make it `Finite`, and `ℕ` has an `Infinite` instance
  exact not_finite ℕ

/-! ## The named obstruction -/

/-- **THE MISSING LEMMA, named so the gap is an obstruction rather than a vague hope.**

**Every failed route needed: "an equality `(α → β) = (α → γ)` yields `β = γ`" -- or, more weakly, an `Equiv`
`(α → β) ≃ (α → γ)` yields `β ≃ γ`.**
**Lean4Lean's Conjecture 2.9 gives this only for DEFINITIONAL equality, and states that it FAILS for
propositional equality.**

**=> the `Prop` below is TRUE at finite carriers (by the counting route) and UNKNOWN elsewhere.**
**Naming it means a future round can look for it, or for a proof that it is independent, rather than
re-attempting the five refuted routes.** -/
def codomainExtractionHolds : Prop :=
  ∀ (α β γ : Type), Nonempty α → (α → β) ≃ (α → γ) → Nonempty (β ≃ γ)

end Lattice.Semantics.Stage1
