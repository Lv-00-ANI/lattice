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

/-- **The general family: for `k ≥ 1` and `d ≥ 2`, `2 ^ k ≠ (d + 1) ^ k`.**

**Six drafts of this failed, and the reason was NOT the `omega` behaviour I first blamed -- it was the
HYPOTHESIS.**
**Every draft assumed `1 ≤ d`, and `1 ≤ d` does NOT give `2 < d + 1`: at `d = 1` the inequality reads
`2 < 2`, which is false.**

**`2 < d + 1` is equivalent to `2 ≤ d` (by `Nat.lt_succ_iff`, since `d + 1` is `d.succ`), so the correct
hypothesis is `2 ≤ d`.**

**=> `omega`'s "No usable constraints found" was telling me the truth: the goal was NOT derivable from those
hypotheses.**
**A tool's refusal is evidence about the STATEMENT, not only about the tool -- and six rounds of blaming
`omega` delayed noticing that the statement was false.** -/
theorem finite_separation_general (k d : ℕ) (hk : 1 ≤ k) (hd : 2 ≤ d) :
    Fintype.card (Fin k → Prop) ≠ Fintype.card (Fin k → Option (Fin d)) := by
  obtain ⟨h1, h2⟩ := finite_card_identities k d
  rw [h1, h2]
  -- `d + 1` is `d.succ`, so `2 < d + 1` follows from `2 ≤ d`
  have hbase : 2 < d + 1 := by rw [Nat.lt_succ_iff]; exact hd
  have hk0 : k ≠ 0 := by omega
  exact Nat.ne_of_lt (Nat.pow_lt_pow_left hbase hk0)

/-- **The `d = 1` case is EXCLUDED by the hypothesis, and this theorem records why that is not a gap.**

**At `d = 1` the two cardinalities are `2 ^ k` and `2 ^ k` -- EQUAL for every `k` -- so the claim is simply
FALSE there, not merely unproved.**
**=> `finite_separation_general`'s hypothesis `2 ≤ d` is the sharp one, and the file states the excluded case
rather than leaving a reader to wonder whether the exclusion was an oversight.** -/
theorem finite_separation_d_one_collides (k : ℕ) :
    Fintype.card (Fin k → Prop) = Fintype.card (Fin k → Option (Fin 1)) := by
  obtain ⟨h1, h2⟩ := finite_card_identities k 1
  rw [h1, h2]

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
