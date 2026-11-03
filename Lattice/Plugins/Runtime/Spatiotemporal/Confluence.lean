/-
# T6 and T7: independent effects commute, and reordering is harmless

**`spatial` (T6) and `confluence` (T7) are both about ONE fact: two effects on DIFFERENT keys do not
interfere.**
**This file states that fact once (`apply_comm`) and derives both properties from it.**

## Why one theorem serves two targets

**`spatial` asks that independent sub-computations do not interfere** -- **`apply_comm` says applying A
then B equals applying B then A, which IS non-interference.**
**`confluence` asks that the ORDER of independent effects does not matter** -- **the same equation, read
as a statement about two orderings of one set.**

**=> the two targets share a witness because they are two readings of one algebraic fact.**
**This is recorded rather than duplicated: a second theorem with the same content would be a `copy`
alias, and the census would (correctly) say so.**

## The hypothesis, and why it is not decoration

**`e₁.key ≠ e₂.key` is REQUIRED.** **Two effects on the SAME key do NOT commute in general: the second
overwrites the first.**
**=> commutativity is a theorem about DISJOINT effects, and a version without the hypothesis would be
false.**
-/

import Lattice.Plugins.Runtime.Spatiotemporal.Seq

namespace Lattice.Plugins.Runtime.Spatiotemporal

/-- **T6 and T7's common core: effects on different keys commute.**

**`b.apply (a.apply s) = a.apply (b.apply s)` when `a.key ≠ b.key`.**

**The proof is pointwise: at the key of `a` the two sides both leave `a.value`; at the key of `b` both
leave `b.value`; elsewhere both leave `s k`.**
**The three cases are exhaustive because the two keys are distinct.** -/
theorem apply_comm {K : Type} [DecidableEq K] (a b : Effect K) (s : RState K)
    (h : a.key ≠ b.key) : b.apply (a.apply s) = a.apply (b.apply s) := by
  funext k
  by_cases hka : k = a.key
  · -- at `a`'s key, `b` does not touch it and `a` writes its own value
    subst hka
    simp only [Effect.apply, if_true, h, Ne.symm h, if_false]
  · by_cases hkb : k = b.key
    · -- at `b`'s key, `a` does not touch it
      subst hkb
      simp only [Effect.apply, hka, if_false, if_true]
    · -- elsewhere neither does
      simp only [Effect.apply, hka, hkb, if_false]

/-- **A two-element list of disjoint effects can be executed in either order.**

**This is `apply_comm` read as a statement about `applySeq`, which is the form the runtime consumes.** -/
theorem applySeq_swap {K : Type} [DecidableEq K] (a b : Effect K) (s : RState K)
    (h : a.key ≠ b.key) :
    applySeq [a, b] s = applySeq [b, a] s := by
  simp only [applySeq]
  exact apply_comm a b s h

/-- **Two disjoint effects, applied and then undone in the same order, restore the state.**

**`spatial` and `confluence` are about ORDER; this records that the DISJOINT list is also fully
recoverable, which is T5 instantiated at length two.**
**It is stated here rather than in `Seq.lean` because it needs the disjointness hypothesis, which is this
file's subject.** -/
theorem undoSeq_apply_pair {K : Type} [DecidableEq K] (a b : Effect K) (s : RState K)
    (ha : a.prev = s a.key) (hb : b.prev = (a.apply s) b.key) :
    undoSeq [a, b] (applySeq [a, b] s) = s := by
  -- `applySeq [a,b] s = b.apply (a.apply s)`, and `undoSeq [a,b]` undoes `b` FIRST
  simp only [applySeq, undoSeq]
  rw [undo_apply b (a.apply s) hb]
  exact undo_apply a s ha

end Lattice.Plugins.Runtime.Spatiotemporal
