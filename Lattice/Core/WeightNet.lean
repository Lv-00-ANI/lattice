import Mathlib
import Lattice.Core.Semantics
import Lattice.Core.Net

/-!
# `Lattice.Core.WeightNet` -- the adopted weight representation

## What "adopted" means, and what it does not mean

`Slots.lean` recorded `core.semantics.weight_exists` as owed: `WeightSemantics` had inhabitants
(`LinearForm`, `LayerParams`, `MLayer`), but none was the project's adopted weight *representation*.

Adopting one is neither a documentation act nor the introduction of a new type. `Lattice.Core.Net` already
defines `AffineLayer n` and the forward pass `netAct`, with the composition laws `netAct_nil` and
`netAct_append`. What was missing is the `WeightSemantics` instance that makes every theorem stated
against that class apply to networks.

So this file adds exactly that instance and nothing else. Introducing a second "network" type would give
the project two notions of the same object -- the defect (`VectorConstraint` declared seven times,
`eval` four times) this project exists to remove.

## Why the instance is the discharge criterion

An instance nobody uses has not been adopted. `Lattice.Lib.Linear.NetPenalty.layer_penalty_exact` is the
theorem that consumes it: a `core`-level statement about a network layer, proved by instantiating the
matrix penalty. The adoption is therefore visible in the proof chain, not only in this comment.

## Namespace

The definitions live in `Lattice.Core.WeightNet` rather than directly in `Lattice.Core`, because `Lattice.Core.Net`
already occupies the latter's namespace with `netAct` and its laws. Two namespaces for two concerns is the
point; a name collision is not.
-/

namespace Lattice.Core.WeightNet

open Lattice.Core

/-- **The adopted weight semantics.** Parameters are stacks of affine layers, inputs and outputs are
vectors, and the action is the forward pass `Lattice.Core.netAct`.

This instance makes `BehaviourallyEquivalent` and every `WeightSemantics`-generic theorem apply to
networks. The composition laws it relies on are `netAct_nil` and `netAct_append` in `Lattice.Core.Net`. -/
noncomputable instance instWeightSemanticsNet {n : Type} [Fintype n] :
    WeightSemantics (List (AffineLayer n)) where
  Input := n → ℝ
  Output := n → ℝ
  act := netAct

/-- **Behavioural equivalence of networks is equality of their forward passes.**

The relation is the functional one and nothing more; the composition laws of `Lattice.Core.Net` then let it
be computed layer by layer. -/
theorem net_behaviourallyEquivalent_iff {n : Type} [Fintype n]
    (ls ms : List (AffineLayer n)) :
    BehaviourallyEquivalent ls ms ↔ netAct ls = netAct ms := by
  constructor
  · intro h
    funext x
    exact h x
  · intro h x
    exact congrFun h x

end Lattice.Core.WeightNet
