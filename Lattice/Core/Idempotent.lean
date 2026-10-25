import Mathlib

/-!
# `Lattice.Core.Idempotent` -- the shape shared by the round-trip and by absorption

## Two obligations, one statement

Two of the project's four targets carry an obligation of the same form:

* **T3** (extraction equivalence): `∀ p, extract (compile p) = p` -- `extract ∘ compile` is the identity, on
  *everything*;
* **T4** (the loop): `∀ x, Sat x → fix x = x` -- `fix` is the identity, on the *satisfying subset*.

The only difference is which subset. `IdempotentOn S g` says `g` fixes everything in `S`, and both obligations
become instances of it: `S := fun _ => True` for the round-trip, `S := R.Sat` for absorption.

## Why this lives in `Core`

`Lattice.Core.Repair` defines absorption and `Lattice.Lift.Extraction` defines the round-trip, so a statement that covers
both has to sit at or below the lower of the two -- `Core`. Putting it in `Geo` (where it first appeared, in
`RepairBridge`) would have made it unreachable from `Lift`, which is exactly backwards: the unification is supposed
to be *more* general than either party, not a fact about the geometry layer.

## What the unification buys

Not taxonomy -- one theorem:

`IdempotentOn.iterate` says an operator that fixes `S` still fixes `S` after any number of iterations. On the
`Repair` side that is `Core.Repair.iterate_fix_of_sat`, which the project already had and which is now its instance.
On the round-trip side it is new: iterating `extract ∘ compile` any number of times is still the identity.

## What it does *not* buy

A closed loop that returns to the original weight. That needs `compile ∘ extract = id`, a right inverse. The
extraction layer's `semantic_not_injective` shows none exists: two distinct symbolic forms can satisfy the same
constraints, so the semantic quotient forgets which one was compiled. The loop closes at the level of *semantics*,
not of *objects* -- the same layering the objective demands of reversibility itself.
-/

namespace Lattice.Core

/-- **An operator that is the identity on a subset.** `S` selects the subset; `g` is the operator. -/
def IdempotentOn {α : Type} (S : α → Prop) (g : α → α) : Prop :=
  ∀ x, S x → g x = x

/-- **Iterating preserves idempotence on the same subset.**

The induction uses the hypothesis twice: once at `x` (to collapse the last step) and once at the already-fixed
intermediate value. Both applications need `S` to be preserved by `g`, which is why the hypothesis is stated for
*all* elements of `S` rather than for `x` alone. -/
theorem IdempotentOn.iterate {α : Type} {S : α → Prop} {g : α → α}
    (h : IdempotentOn S g) (n : ℕ) :
    IdempotentOn S (g^[n]) := by
  intro x hx
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, h x hx]

/-- **A left inverse makes the composite idempotent everywhere.**

`extract ∘ compile` is the identity on the whole space whenever `extract` is a left inverse of `compile`; this is
the round-trip side's instance, stated without reference to any particular representation. -/
theorem idempotentOn_of_leftInverse {P W : Type} (compile : P → W) (extract : W → P)
    (hround : ∀ p, extract (compile p) = p) :
    IdempotentOn (fun _ => True) (extract ∘ compile) :=
  fun p _ => hround p

/-- **… and so is every iterate of it.** -/
theorem iterate_comp_of_leftInverse {P W : Type} (compile : P → W) (extract : W → P)
    (hround : ∀ p, extract (compile p) = p) (n : ℕ) :
    ∀ p : P, (extract ∘ compile)^[n] p = p :=
  fun p => IdempotentOn.iterate (idempotentOn_of_leftInverse compile extract hround) n p trivial

end Lattice.Core
