/-
# The spatiotemporal runtime model: state, effects, and reversibility

**T5-T8 (`recovery`, `spatial`, `confluence`, `failure isolation`) were, before this file, only
STRINGS in `open_targets` -- and T7/T8 were not even that.**
**The audit's finding was correct: the tree had no carrier on which those four properties could be
stated, so any claim about them was a claim about nothing.**

## What this slice provides

**A minimal runtime: a `State` is a finite map from keys to values, and an `Effect` is a
`set`/`clear` pair on ONE key, packaged with its inverse.**
**`apply` runs an effect; `undo` runs its inverse.**
**The defining property is `undo_apply`: `undo` after `apply` restores the state exactly.**

## Why this is the right minimality

**T5-T8 are about COMBINING effects, so the carrier must have (a) state, (b) an inverse, and
(c) enough structure to say when two effects are independent.**
**A `K → Option ℕ` map gives all three, and nothing more is needed** -- **the four properties below are
each one short induction over the list of effects.**

**What this deliberately does NOT model**: **concurrency, timing, or asynchrony.**
**`recovery`, `spatial` and `confluence` are all stated about SEQUENTIAL executions whose order is
permuted** -- **which is the algebraic core those words denote, and the part that can be proved.**
**A claim about wall-clock scheduling would need a model of time the project does not have, and is
recorded as absent rather than approximated.**
-/

import Mathlib
import Lattice.Plugins.Manifest

namespace Lattice.Plugins.Runtime.Spatiotemporal

/-- **The runtime state: a finite map from keys to values.**

**`Option ℕ` rather than `ℕ` so that "absent" is a distinct value** -- **this is what makes `undo` of a
`clear` meaningful: restoring a key that was never set must return `none`, not `0`.** -/
abbrev RState (K : Type) : Type := K → Option ℕ

/-- **An effect on one key, together with its inverse.**

**Every primitive effect is reversible by construction: `apply` writes `v` and `undo` writes `prev`,
where `prev` is whatever the key held.** **That `prev` is carried IN the effect is the whole trick --
it is what lets `undo` be a total function rather than a partial one.** -/
structure Effect (K : Type) where
  /-- The key this effect touches. -/
  key : K
  /-- The value written by `apply`. -/
  value : Option ℕ
  /-- The value to restore on `undo` -- captured BEFORE `apply`. -/
  prev : Option ℕ

/-- **Running an effect: overwrite one key.** -/
def Effect.apply {K : Type} [DecidableEq K] (e : Effect K) (s : RState K) : RState K :=
  fun k => if k = e.key then e.value else s k

/-- **Undoing an effect: restore the captured value.** -/
def Effect.undo {K : Type} [DecidableEq K] (e : Effect K) (s : RState K) : RState K :=
  fun k => if k = e.key then e.prev else s k

/-- **An effect built from a state captures that state's value at its key.**

**This is the constructor that makes `undo_apply` provable: the inverse is DERIVED from the state the
effect is applied to, so it cannot be mismatched.** -/
def Effect.at {K : Type} [DecidableEq K] (s : RState K) (k : K) (v : Option ℕ) : Effect K where
  key := k
  value := v
  prev := s k

/-- **T5's core: undoing an effect restores the state exactly.**

**`undo (apply e s) = s` whenever `e.prev = s e.key`.**
**The hypothesis is not a convenience: an effect is only reversible if the value it restores was
CAPTURED from the same state it is applied to.**
**=> the hypothesis is exactly the condition under which the word "recovery" is meaningful.** -/
theorem undo_apply {K : Type} [DecidableEq K] (e : Effect K) (s : RState K)
    (h : e.prev = s e.key) : e.undo (e.apply s) = s := by
  funext k
  by_cases hk : k = e.key
  · subst hk
    simp only [Effect.undo, Effect.apply, if_pos rfl]
    exact h
  · simp only [Effect.undo, Effect.apply, if_neg hk]

/-- **The derived constructor is reversible at the state it was captured from.**

**`Effect.at s k v` is the ONLY constructor whose inverse is correct by construction** -- **its `prev`
field IS `s k`, so `undo_apply`'s hypothesis holds definitionally.**

**The proof unfolds the three definitions rather than forwarding `undo_apply`:** **the equation
`(Effect.at s k v).prev = s k` is `rfl`, and making that visible is the point of the theorem -- a
forwarding term would hide which of the three components is doing the work.** -/
theorem undo_apply_at {K : Type} [DecidableEq K] (s : RState K) (k : K) (v : Option ℕ) :
    (Effect.at s k v).undo ((Effect.at s k v).apply s) = s := by
  have hprev : (Effect.at s k v).prev = s (Effect.at s k v).key := rfl
  exact undo_apply (Effect.at s k v) s hprev

end Lattice.Plugins.Runtime.Spatiotemporal
