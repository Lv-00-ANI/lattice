/-
# `Core/CastLemmas.lean` -- transports compose, and transports along one equation agree (round 144)

## Why these two lemmas, and why they are worth a file

**Rounds 141, 142 and 143 each failed to prove the general chain evaluation, and round 143's
`CHAIN-EVALUATION.md` diagnosed the obstruction as "transport does not reduce".**

**Round 144 took that file's route 2 and found that the diagnosis was HALF RIGHT:**

- **`cast` does NOT reduce -- true, and it is why every construction attempt needed a transport;**
- **but two `cast`s along the SAME equation DO collapse, because `Sort`-valued equalities are PROPOSITIONS.**

**=> the second fact is `cast_proof_irrel` below, and it is the lemma the three failed rounds were missing.**
**It does not make the general evaluation go through -- see the file's last section -- but it is true, it is
general, and it will be consumed by whoever writes that proof.**

## The two lemmas

| lemma | content |
|:--|:--|
| **`cast_cast`** | **`cast h₂ (cast h₁ x) = cast (h₁.trans h₂) x`** |
| **`cast_proof_irrel`** | **`cast h₁ x = cast h₂ x` when `h₁ h₂ : α = β`** |

**Both are stated over an arbitrary `Sort u`, so they are facts about Lean's kernel rather than about the
project's types.**

## What this file does NOT do

**It does not prove the general chain evaluation.**
**Round 144 built `toChainNat` and `applyLayers` on top of these lemmas and STILL could not close
`act_toChainNat`: the remaining step needs the equation between the two recursions' endpoints, and writing the
endpoint as `k + fuel` makes the `succ` case's tail `(k+1) + fuel` -- a term that is equal to `k + (fuel+1)` by
`omega` but whose `cast` the recursor cannot eliminate, because `Nat.add` recurses on its LEFT argument.**

**=> the fix that HAS NOT been tried is the ARGUMENT ORDER: write the endpoint as `fuel + k`, which makes
`Nat.add` recurse on `fuel` -- the very variable the recursion decreases.**
**`CHAIN-EVALUATION.md` §4.1 and §4.2 now both have a concrete successor, and this file records which one the
next attempt should take.**

## A note on honesty

**Two files were written and DELETED in round 144 rather than left in a half-built state, and this file is what
survives: two true lemmas and a corrected diagnosis.**
**A round that produces no theorem but corrects the reason for its own failure is worth more than one that
leaves a `sorry` behind.**
-/

import Mathlib

namespace Lattice.Core

/-- **Transports compose.**

**`cast h₂ (cast h₁ x) = cast (h₁.trans h₂) x`.**

**The proof is `subst` on both equations then `rfl`: once both sides are the same type, `cast` is the identity
and the composition is trivial.**
**=> this is the `Eq.rec` fact that lets nested transports be FLATTENED rather than merely related.** -/
theorem cast_cast {α β γ : Sort u} (h₁ : α = β) (h₂ : β = γ) (x : α) :
    cast h₂ (cast h₁ x) = cast (h₁.trans h₂) x := by
  subst h₁
  subst h₂
  rfl

/-- **Transports along the SAME equation agree.**

**`cast h₁ x = cast h₂ x` for any two proofs `h₁ h₂ : α = β`.**

**`Sort u`-valued equalities live in a PROPOSITION, so `Subsingleton.elim` makes the two proofs the same TERM --
not merely equal, but the same term, which is what a `rfl`-level comparison needs.**
**=> this is why a `by omega` at one call site and a `by omega` at another can be identified even though they
have different proof terms SYNTACTICALLY.** -/
theorem cast_proof_irrel {α β : Sort u} (h₁ h₂ : α = β) (x : α) :
    cast h₁ x = cast h₂ x := by
  rw [Subsingleton.elim h₁ h₂]

/-- **A transport along a REFLEXIVE equation is the identity.**

**`cast rfl x = x` -- the base case both lemmas above reduce to.** -/
theorem cast_rfl {α : Sort u} (x : α) : cast rfl x = x :=
  rfl

end Lattice.Core
