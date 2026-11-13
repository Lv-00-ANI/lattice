import Mathlib
import Lattice.Core.Syntax
import Lattice.Core.Semantics
import Lattice.Core.RepairModule.ConstraintProofs
/-!
# `Lattice.Lift.PenaltyEmbedding` -- T2: constraint embedding is sound

## What the legacy theorem actually established

`ConstraintEmbeddingSoundness.embedding_soundness` states, for `Int`-valued linear
constraints,

```
loss c x = 0  ->  ConstraintSat c x        where  loss c x = (a*x + b)^2
```

That is true, and it follows from `sq_eq_zero_iff`. But note what it says: *a point of zero loss
satisfies the constraint*. It does not say that a **stationary point** satisfies it, and a
stationary point is what training actually produces.

So the legacy result is one end of a spectrum, and the general claim needs a design obligation
that was never stated.

## Three layers, and which of them is a theorem

| layer | statement | status here |
|:--|:--|:--|
| A | `loss p x = 0 -> Sat p x` | **proved**, for any instance |
| B | `IsLocalMin (loss p) x -> Sat p x` | an **explicit hypothesis**, plus the nesting theorem |
| C | gradient norm bound + strong convexity gives a distance bound | later |

Layer B is where the content of a penalty design lives, and it is false in general: an embedding
with constant positive loss has a false implication at level A (vacuously) yet is minimised
everywhere and accepts nothing (`sound_not_exact`).

## The nesting, proved

An earlier revision recorded "level B implies level A" as a design remark, on the grounds that
constructing an `IsLocalMin` term needs the filter library. That was half right -- it does need
`Filter` -- but the implication matters: without it, levels A and B would be two unrelated
claims and proving B would not deliver A. `exact_implies_sound` discharges it, while the
algebraic heart (`sq_penalty_eq_zero`) stays topology-free.

## Generality

Nothing fixes the carrier to `Int` and nothing fixes the penalty to squaring. Level A needs only
`sq_eq_zero_iff`'s hypotheses -- `MonoidWithZero` and `NoZeroDivisors` -- so it holds on `Int`,
on every `LinearOrderedRing`, and on `Real` at once.
-/

namespace Lattice.Lift

open Lattice.Core

/-- A penalty embedding: a symbolic constraint is replaced by a real-valued loss.

`X` must be a topological space because the level-B obligation is stated in terms of local
minimisers, and local minimality is topological. Leaving this out would make `PenaltyExact`
unstatable -- the gap the legacy formulation fell into, as it could only ever talk about zeros. -/
structure PenaltyEmbedding (P X : Type) [TopologicalSpace X] where
  /-- The soft loss standing in for the constraint. -/
  loss : P → X → ℝ
  /-- The hard predicate the embedding represents. -/
  Sat : P → X → Prop

/-- **Level A.** Zero loss implies satisfaction. -/
def PenaltySound {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X) : Prop :=
  ∀ p x, E.loss p x = 0 → E.Sat p x

/-- **Level B.** Every local minimiser of the loss satisfies the constraint.

Strictly stronger than `PenaltySound`, and the obligation that turns "training converged" into
"the constraint holds". -/
def PenaltyExact {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X) : Prop :=
  ∀ p (x : X), IsLocalMin (E.loss p) x → E.Sat p x

/-! ## The nesting lemma, at its natural generality

`IsLocalMin f a` unfolds to `IsMinFilter f (nhds a) a`, which is
`∀ᶠ y in nhds a, f a ≤ f y`. A point where a function dominates all others is therefore a local
minimiser, and `Filter.Eventually.of_forall` turns "everywhere" into "eventually". -/

/-- **A point that dominates everything is a local minimiser.**

Stated for an arbitrary topological space and an arbitrary preorder, so it serves `ℝ`-valued
losses and any other ordered carrier without restatement. -/
theorem isLocalMin_of_forall_le {X : Type} [TopologicalSpace X]
    {β : Type} [Preorder β] {f : X → β} {x : X} (h : ∀ y, f x ≤ f y) : IsLocalMin f x :=
  Filter.Eventually.of_forall h

/-- A vanishing non-negative loss makes its point a local minimiser. -/
theorem loss_zero_is_localMin {X : Type} [TopologicalSpace X] {f : X → ℝ} {x : X}
    (hnn : ∀ y, 0 ≤ f y) (hx : f x = 0) : IsLocalMin f x := by
  apply isLocalMin_of_forall_le
  intro y
  rw [hx]
  exact hnn y

/-- **Level B implies level A**, for a non-negative loss.

The non-negativity premise is not removable: without it a zero of the loss need not be a
minimiser, so level A would not follow from level B. -/
theorem exact_implies_sound {P X : Type} [TopologicalSpace X] {E : PenaltyEmbedding P X}
    (hnn : ∀ p (x : X), 0 ≤ E.loss p x) (h : PenaltyExact E) : PenaltySound E :=
  fun p x hx => h p x (loss_zero_is_localMin (hnn p) hx)

/-! ## The algebraic heart, at its natural generality -/

/-- **Square penalties are faithful**: `u ^ 2 = 0 ↔ u = 0`.

The hypotheses are those of `sq_eq_zero_iff` and nothing else, so this covers `Int`, `Real`, and
every `LinearOrderedRing` in between. Deliberately topology-free: this is the part of T2 the
algebraic layer can use without touching `Filter`. -/
theorem sq_penalty_eq_zero {M : Type} [MonoidWithZero M] [NoZeroDivisors M] (u : M) :
    u ^ 2 = 0 ↔ u = 0 :=
  sq_eq_zero_iff

/-! ## Level B as an explicit hypothesis -/

section LevelB

variable {P X : Type} [TopologicalSpace X]

/-- **T2 (conditional).** If the embedding is exact at level B, a trained point -- a local
minimiser of the loss -- satisfies the symbolic constraint.

The hypothesis is the entire content; everything else is definitional. A framework that *hid*
this hypothesis could state the theorem unconditionally and be wrong. -/
theorem embedding_sound_at_minimiser {E : PenaltyEmbedding P X} {p : P} {x : X}
    (hexact : PenaltyExact E) (hmin : IsLocalMin (E.loss p) x) : E.Sat p x :=
  hexact p x hmin

/-- **T2 for a whole program.** If every item of a program is exact, then a point minimising each
item's loss satisfies the whole program.

Program-level, and it does not require the items to share a loss -- which is the form the
compile/extract ladder consumes. -/
theorem program_sound_at_minimiser {P X : Type} [TopologicalSpace X]
    (E : PenaltyEmbedding P X) (ps : List P)
    (hexact : ∀ p ∈ ps, PenaltyExact E)
    (x : X) (hmin : ∀ p ∈ ps, IsLocalMin (E.loss p) x) :
    ∀ p ∈ ps, E.Sat p x :=
  fun p hp => hexact p hp p x (hmin p hp)

end LevelB

/-! ## Necessity: level A does not imply level B -/

section Necessity

/-- An embedding with constant positive loss and an always-false predicate.

Level A holds vacuously -- no point has zero loss -- while level B fails everywhere, because a
constant function is minimised at every point. -/
def constEmbedding : PenaltyEmbedding Unit Unit where
  loss := fun _ _ => 1
  Sat := fun _ _ => False

/-- Level A holds for it, vacuously. -/
theorem const_levelA : PenaltySound constEmbedding := by
  intro _ _ h
  norm_num [constEmbedding] at h

/-- But level B fails. -/
theorem const_not_levelB : ¬ PenaltyExact constEmbedding := by
  intro h
  have hmin : IsLocalMin (constEmbedding.loss ()) () :=
    isLocalMin_of_forall_le (fun _ => by norm_num [constEmbedding])
  exact h () () hmin

/-- **Level A does not imply level B.** The nesting is strict, so T2's conditional form is not a
roundabout way of saying something weaker. -/
theorem sound_not_exact : PenaltySound constEmbedding ∧ ¬ PenaltyExact constEmbedding :=
  ⟨const_levelA, const_not_levelB⟩

/-- The null embedding: constant zero loss, always-true predicate. It satisfies level A and says
nothing, which is why level A alone is not a meaningful correctness claim. -/
def nullEmbedding : PenaltyEmbedding Unit Unit where
  loss := fun _ _ => 0
  Sat := fun _ _ => True

/-- Level A holds for the null embedding too. -/
theorem null_levelA : PenaltySound nullEmbedding :=
  fun _ _ _ => trivial

end Necessity

end Lattice.Lift
