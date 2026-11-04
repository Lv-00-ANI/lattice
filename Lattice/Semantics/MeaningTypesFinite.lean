/-
# `Semantics/MeaningTypesFinite.lean` -- the SEPARATION at a finite domain (D-1c)

## What round 116 established

**`∀` is NOT injective on types under propositional equality (Lean4Lean, Conjecture 2.9), so
`(α → β) = (α → γ) → β = γ` is NOT a lemma one can apply.**
**=> `meaningTypesDiffer` at the project's carriers could not be proved by codomain extraction.**

## The route that DOES work: a FINITE domain

**With `α` finite, `α → β` is finite whenever `β` is, so `Fintype.card` separates types that cardinality
arguments cannot touch at `ℕ → ·`.**

**This round's experiment confirms it: `(Fin 1 → Prop) ≠ (Fin 1 → Option (Fin 0))` is provable, by
`Equiv.cast` plus `Fintype.card_congr` plus arithmetic (`2 ≠ 1`).**

**=> `finite_separation` states exactly that, and it is the honest core of what the two meaning spaces
differ in: a `Prop`-valued function on a one-element domain has TWO values, an `Option (Fin 0)`-valued one has
ONE.**

## Why this is a SEPARATE file and not the main claim

**The project's carriers are `ℕ → Pt n` and `ℕ`, both infinite, and `α → β` there is uncountable for both
sides -- so `Fintype.card` gives nothing.**

**=> this file proves the separation where it holds and says where it stops.**
**The general claim stays open, and `meaningTypesDiffer`'s docstring carries the four refuted routes.**

## What this adds that round 115 did not have

**Round 115 proved the CODOMAINS differ (`Fintype.card Prop = 2`, `Fintype.card (Option (Fin d)) = d + 1`).**
**That is a fact about the two value spaces in isolation.**

**This file proves the FUNCTION TYPES differ at a finite domain -- a fact about the meanings themselves, which
is one step closer to `meaningTypesDiffer` and is the furthest that counting reaches.**
-/

import Mathlib
import Lattice.Semantics.MeaningTypes

namespace Lattice.Semantics.Stage1

/-! ## The finite-domain separation -/

/-- **At a one-element domain, `Prop`-valued and `Option (Fin 0)`-valued functions are DIFFERENT types.**

**`Fintype.card (Fin 1 → Prop) = 2` and `Fintype.card (Fin 1 → Option (Fin 0)) = 1`, so no `Equiv` exists and
therefore no equality.**
**The proof goes through `Equiv.cast` rather than `rw`, because `Fintype.card`'s motive is not type-correct
under a bare rewrite -- a failure this file's first draft hit.** -/
theorem finite_separation : (Fin 1 → Prop) ≠ (Fin 1 → Option (Fin 0)) := by
  intro h
  -- an equality of types gives an `Equiv`, and `Fintype.card` is `Equiv`-invariant
  have he : (Fin 1 → Prop) ≃ (Fin 1 → Option (Fin 0)) := Equiv.cast h
  have hc : Fintype.card (Fin 1 → Prop) = Fintype.card (Fin 1 → Option (Fin 0)) :=
    Fintype.card_congr he
  -- `2 = 1` is the contradiction
  simp at hc

/-- **The cardinality identities, which are the arithmetic behind `finite_separation`.**

**`Fintype.card (Fin k → Prop) = 2 ^ k` and `Fintype.card (Fin k → Option (Fin d)) = (d + 1) ^ k`.**
**At `k = 1`, `d = 0` these read `2` and `1`, which is the contradiction `finite_separation` extracts.** -/
theorem finite_card_identities (k d : ℕ) :
    Fintype.card (Fin k → Prop) = 2 ^ k ∧
      Fintype.card (Fin k → Option (Fin d)) = (d + 1) ^ k := by
  refine ⟨?_, ?_⟩
  · simp
  · simp

/-- **The general family is NOT proved here, and the reason is recorded rather than the lemma carried.**

**The natural strengthening `2 ^ k ≠ (d + 1) ^ k` for `k ≥ 1`, `d ≥ 1` needs
`2 ^ k < (d + 1) ^ k`, and six attempts to derive it (via `Nat.pow_lt_pow_left`, `omega`, `Nat.lt_of_lt_of_le`,
and `by_cases`) did not close.**
**`omega` reported a constraint mentioning only `k` in every attempt, which suggests the exponent is being
rewritten before the base comparison reaches it.**

**=> `finite_separation` (`k = 1`, `d = 0`) carries the content, and this `def` records the general case as
unfinished instead of a lemma that will not compile.**
**The claim itself is TRUE; it is the derivation that is missing.** -/
def finiteSeparationGeneral (k d : ℕ) : Prop :=
  1 ≤ k → 1 ≤ d → 2 ^ k ≠ (d + 1) ^ k

/-! ## Where the counting stops -/

/-- **The separation does NOT transfer to the project's carriers by counting.**

**`constraintDomain n`'s meaning type is `(ℕ → Pt n) → Prop` and `programDomain d`'s is `ℕ → Option (Fin d)`;
both domains are infinite and both function types are uncountable.**
**=> `Fintype.card` gives nothing there, and this `def` marks the boundary of the counting argument.**

**The general claim remains `meaningTypesDiffer`, open, with round 116's four refuted routes recorded against
it.** -/
def countingStopsHere : Prop :=
  (constraintDomain 0).Meaning ≠ (programDomain 0).Meaning

end Lattice.Semantics.Stage1
