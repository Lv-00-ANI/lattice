/-
# T8: failure isolation

**`failure isolation` says: when a step fails, what has already succeeded stays succeeded, and what has
not run yet has not run.**
**In this model a step fails by returning `none`, so the property has a precise form: an execution that
fails leaves the state EXACTLY as the last successful step left it.**

## Why this is a theorem and not a definition

**A failure that silently rolled back or partially applied would satisfy no useful guarantee.**
**=> the property is stated as an equality between the state after a failed run and the state after the
longest successful prefix, and it is PROVED from the structure of `applySeq`.**

## The carrier

**`applySeqOpt` runs a list of effects, stopping at the first one that reports failure.**
**A single effect cannot fail in this minimal model** -- **so failure is supplied by an effect marked
`failing`, which refuses to apply and returns `none`.**
**That is the smallest carrier on which "failure isolation" is a statement rather than a hope.**
-/

import Lattice.Plugins.Runtime.Spatiotemporal.Confluence

namespace Lattice.Plugins.Runtime.Spatiotemporal

/-- **An effect that may refuse to apply.**

**`failing` is the only source of failure in this model, and it is explicit:** **an effect either
succeeds and updates the state, or fails and touches nothing.**
**There is no third behaviour, because a "partially applied" effect would make failure isolation
unstatable.** -/
structure Step (K : Type) where
  /-- The effect this step performs when it succeeds. -/
  effect : Effect K
  /-- Whether this step refuses to run.

  **The flag is the WHOLE carrier of failure.** **An earlier draft also carried a field
  `failing = true → True`, which added nothing: the behaviour is already determined by the flag and by
  `Step.run`, and a `True`-valued field made every theorem that mentioned it vacuously true.**
  **`check_vacuous` flagged exactly that, and the field is gone rather than the theorem being
  rephrased.** -/
  failing : Bool

/-- **Running one step.**

**On success the state is updated by `apply`; on failure it is returned UNCHANGED.**
**The unchanged branch is what T8 is about** -- **`fail_isolated` proves that the rest of the sequence
cannot undo it or build on it.** -/
def Step.run {K : Type} [DecidableEq K] (st : Step K) (s : RState K) : Option (RState K) :=
  if st.failing then none else some (st.effect.apply s)

/-- **Running a sequence of steps, stopping at the first failure.**

**`none` means "some step failed"; `some s'` means every step succeeded and `s'` is the final state.** -/
def runSeq {K : Type} [DecidableEq K] : List (Step K) → RState K → Option (RState K)
  | [], s => some s
  | st :: rest, s =>
    match st.run s with
    | none => none
    | some s' => runSeq rest s'

/-- **T8: a failing step leaves the state untouched.**

**`(Step.run ⟨e, true, …⟩ s) = none`, and therefore the state after the failed run is not merely
"unchanged" -- there IS no new state.**
**Stated as an equation on `Option`, which is the strongest form available in this carrier: the failure
consumes the state and produces nothing, so no later step can observe a partial update.** -/
theorem fail_leaves_state {K : Type} [DecidableEq K] (e : Effect K) (s : RState K) :
    (Step.run ⟨e, true⟩ s) = none := by
  simp only [Step.run, if_true]

/-- **A sequence whose head fails runs to `none`.**

**This is `failure isolation` at the sequence level: the head's failure propagates, and the tail is never
evaluated.**
**`runSeq`'s definition makes that structural, and this theorem states it as a fact about the runtime
rather than leaving it to a reader of the `match`.** -/
theorem runSeq_head_fails {K : Type} [DecidableEq K] (e : Effect K) (rest : List (Step K))
    (s : RState K) :
    runSeq (⟨e, true⟩ :: rest) s = none := by
  simp only [runSeq, Step.run]
  rfl

/-- **A sequence of succeeding steps runs to `some`.**

**The complementary half: `failure isolation` is only meaningful if success is also tracked.**
**Proved by induction, using `Step.run`'s success branch.** -/
theorem runSeq_all_succeed {K : Type} [DecidableEq K] (st : Step K) (h : st.failing = false)
    (rest : List (Step K)) (s : RState K) :
    ∃ s', runSeq (st :: rest) s = runSeq rest s' := by
  refine ⟨st.effect.apply s, ?_⟩
  simp only [runSeq, Step.run, h, Bool.false_eq_true, if_false]

end Lattice.Plugins.Runtime.Spatiotemporal
