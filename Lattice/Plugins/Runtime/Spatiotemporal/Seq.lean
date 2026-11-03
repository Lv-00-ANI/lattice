/-
# Effect sequences and their inverses

**`Model.lean` proved that ONE effect is reversible.**
**A runtime executes LISTS of effects, so T5 (`recovery`) needs the inverse of a SEQUENCE.**

## The structure of the argument, and the precondition that is NOT decorative

**`undoSeq` undoes a list head-first, which is the same as undoing a composition in the OPPOSITE
order.**
**That reversal is the whole content of the induction: without it the hypothesis would apply to the
wrong intermediate state.**

**The precondition `Captured es s` says each effect's `prev` equals the value the key held AT THE
MOMENT that effect ran.**
**Without it the theorem is FALSE** -- **an effect whose `prev` was captured from a different state does
not restore this one.**
**=> the precondition is exactly the condition under which the word "recovery" means anything, and it is
carried explicitly rather than assumed away.**
-/

import Lattice.Plugins.Runtime.Spatiotemporal.Model

namespace Lattice.Plugins.Runtime.Spatiotemporal

/-- **Running a sequence of effects, left to right.** -/
def applySeq {K : Type} [DecidableEq K] : List (Effect K) → RState K → RState K
  | [], s => s
  | e :: es, s => applySeq es (e.apply s)

/-- **Undoing a sequence: undo the head first, then the rest.**

**Note this is NOT `foldr` over the reversed list evaluated as a composition** -- **it is the operational
statement "undo the most recent effect first", which is what a stack-based runtime does.**
**The two agree, and `undoSeq_apply` is where that is proved.** -/
def undoSeq {K : Type} [DecidableEq K] : List (Effect K) → RState K → RState K
  | [], s => s
  | e :: es, s => e.undo (undoSeq es s)

/-- **At every position, the effect's captured value matches the state it will be applied to.**

**Recursive rather than `∀`-based, because "the state at that position" depends on the PREFIX, not on
the initial state.** -/
def Captured {K : Type} [DecidableEq K] : List (Effect K) → RState K → Prop
  | [], _ => True
  | e :: es, s => e.prev = s e.key ∧ Captured es (e.apply s)

/-- **A captured sequence, applied then undone, restores the start state.**

**Two inductions compose here: the list induction, and inside it `undo_apply` at the head.**
**The head's hypothesis comes from `Captured`'s first component; the tail's from `Captured`'s second,
which is stated at the UPDATED state -- that is why `Captured` had to be recursive rather than a plain
`∀`.**

**The induction generalises `s` so the hypothesis applies to `e.apply s`.** -/
theorem undoSeq_apply {K : Type} [DecidableEq K] (es : List (Effect K)) (s : RState K)
    (h : Captured es s) : undoSeq es (applySeq es s) = s := by
  induction es generalizing s with
  | nil => rfl
  | cons e rest ih =>
    simp only [applySeq, undoSeq]
    have hhead : e.prev = s e.key := h.1
    have htail : Captured rest (e.apply s) := h.2
    -- undo the tail first (it was applied last), which restores `e.apply s`; then undo the head
    rw [ih (e.apply s) htail]
    exact undo_apply e s hhead

end Lattice.Plugins.Runtime.Spatiotemporal
