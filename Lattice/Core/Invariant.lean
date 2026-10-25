import Mathlib
import Lattice.Core.Repair

/-!
# `Lattice.Core.Invariant` -- what a repair preserves, stated without a carrier-specific structure

## Why this belongs to the core and not to the geometry

`Lattice.Geo.RepairQuality` distinguishes repairs by whether they keep two points apart. That distinction is
meaningful for a carrier made of points, and meaningless for `Lattice.Lib.Linear`'s instances, whose carrier is
`ℚ` or a vector space and which have no points to keep apart.

What generalises is the *question*, not the answer: given any predicate `P` on the carrier, does the repair
preserve it? Stated this way the question is meaningful for every `Repair` inhabitant, and the answer has a
sharp shape -- **a repair preserves `P` exactly on the states it does not have to change**.

## The one theorem worth proving at this level

`Repair.absorbs` says a satisfying state is left alone. Composing that with "`P` holds at `x`" gives: **at a
satisfying state, the repair preserves every predicate whatsoever.** Not just the predicates someone thought
of -- all of them, because the state does not move.

The converse direction is where repairs differ, and it is genuinely a property of the operator rather than of
the framework: a repair may have to *destroy* `P` in order to reach its target. Whether some other way exists
is exactly what `Compatible` below asks, and the geometry's copying operator fails it for the separation
predicate while the projecting one does not.
-/

namespace Lattice.Core

variable {α : Type}

/-- **A repair preserves a predicate** when it does not move a satisfied state out of the predicate.

Only meaningful as an obligation at satisfying states: at an unsatisfying state the repair *must* move, so no
predicate containing that state can be preserved by an operator that reaches its target. `preserves_free`
below records that the distinction is real. -/
def Preserves (P : α → Prop) (R : Repair α) : Prop :=
  ∀ x : α, P x → P (R.fix x)

/-- **At a satisfying state the repair preserves everything.**

`Repair.absorbs` says `fix` is the identity there, so any predicate is preserved -- not by analysing the
predicate, but because nothing changes. This is the layered statement the geometry's third quality level rests
on: conservativity implies preservation of every invariant at once. -/
theorem preserves_of_sat (R : Repair α) (P : α → Prop) (x : α) (h : R.Sat x) :
    P x → P (R.fix x) := by
  rw [R.absorbs x h]
  exact id

/-- **A satisfied state is a fixed point**, which is the fact `preserves_of_sat` uses. -/
theorem fix_eq_self_of_sat (R : Repair α) (x : α) (h : R.Sat x) : R.fix x = x :=
  R.absorbs x h

/-- **Preservation is not free at unsatisfying states.**

For any unsatisfying state there is a predicate it satisfies that the repair cannot preserve -- namely "being
this state". So the obligation is only meaningful as a conditional, and a framework that demanded
unconditional preservation would have no inhabitants at all. -/
theorem preserves_free (R : Repair α) (x : α) (h : ¬ R.Sat x) :
    ∃ P : α → Prop, P x ∧ ¬ P (R.fix x) := by
  refine ⟨fun y => y = x, rfl, ?_⟩
  intro hfix
  have hdec := R.decreases x h
  rw [hfix] at hdec
  exact absurd hdec (lt_irrefl _)

/-- **A predicate and a target are compatible** when some state satisfies both.

An earlier revision of this file claimed this separates a *good* repair from a merely correct one. It does
not, and the correction is worth recording.

`Compatible P R` asks whether the **target** can be met without leaving `P`. It says nothing about how `R`
gets there: two operators with the same `Sat` have the same `Compatible` verdict whatever their `fix` does.
And when `P` is *inconsistent* with the target -- separation versus a coincidence constraint, say -- no
operator can satisfy it, so the failure is a property of the pair (constraint, predicate) rather than a
weakness of the operator.

So this is an obligation on the **constraint**, checked against a predicate, and it is stated with `R` only
because a `Repair` is where a constraint lives in this project. `compatible_iff_witness` below gives its
content: it is nonemptiness of the intersection.
-/
def Compatible (P : α → Prop) (R : Repair α) : Prop :=
  ∀ x : α, P x → ∃ y : α, R.Sat y ∧ P y

/-- **What `Compatible` actually asserts** (given a `P`-satisfying state to start from): the target and the
predicate have a common point.

Every `x` with `P x` yields the same witness obligation, so the `∀ x` is not doing any work beyond saying
that `P` is inhabited.
-/
theorem compatible_iff_witness (P : α → Prop) (R : Repair α) (x₀ : α) (hx₀ : P x₀) :
    Compatible P R ↔ ∃ y : α, R.Sat y ∧ P y := by
  constructor
  · intro h
    exact h x₀ hx₀
  · intro ⟨y, hsat, hP⟩ _ _
    exact ⟨y, hsat, hP⟩

end Lattice.Core
