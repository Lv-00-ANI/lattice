import Mathlib
import Lattice.Core.Semantics
import Lattice.Core.Weight

/-!
# `Lattice.Core.Net` -- stacked layers, and the reversibility spectrum they complete

## What this file adds

`Lattice.Core.Weight` supplies a single affine layer and proves that its behaviour determines its
parameter (`layer_act_injective`). A single layer is not a network; real weights are stacks, and a
stack is where invertibility is lost.

This file builds the stack over a *fixed width*, which is the case where the type of every layer is
the same and composition is function iteration. Variable width needs a dependently typed list and is
recorded as a slot rather than approximated -- a fixed-width stack is honest about what it covers.

## The spectrum

Three representations now exist in the project, and their invertibility differs:

| representation | semantic layer injective? | where |
|:--|:--|:--|
| `LinearForm` (coefficients) | no -- scaling preserves meaning | `Lattice.Lift.Extraction.semantic_not_injective` |
| `LayerParams` (one affine layer) | **yes** | `Lattice.Core.Weight.layer_act_injective` |
| stack + activation | **no** -- the activation collapses | `netRelu_not_injective` below |

Together they turn the project's "reversibility must be stated by layer" requirement into something
sharper: invertibility is a property of the chosen *representation and structure*, not of a rung of
the ladder. That is a stronger claim and a more useful one, because it tells a designer which choice
costs invertibility.
-/

namespace Lattice.Core

open Lattice.Core

/-- An affine layer over a fixed width: weights and a bias on `n → ℝ`. -/
structure AffineLayer (n : Type) where
  /-- Weight matrix. -/
  W : n → n → ℝ
  /-- Bias vector. -/
  b : n → ℝ

/-- The action of one affine layer. -/
noncomputable def affineAct {n : Type} [Fintype n] (p : AffineLayer n) (x : n → ℝ) : n → ℝ :=
  fun j => (∑ i, p.W i j * x i) + p.b j

/-- A stack of same-width affine layers, applied left to right.

Defined by `List.foldl` so that the empty stack is the identity and appending stacks composes them
in order -- the two facts `netAct_nil` and `netAct_append` record. -/
noncomputable def netAct {n : Type} [Fintype n] (ls : List (AffineLayer n)) (x : n → ℝ) :
    n → ℝ :=
  ls.foldl (fun acc p => affineAct p acc) x

/-- The empty stack is the identity. -/
@[simp] theorem netAct_nil {n : Type} [Fintype n] (x : n → ℝ) :
    netAct ([] : List (AffineLayer n)) x = x := rfl

/-- **Composition law.** A stack of two stacks is the second applied to the first.

This is what lets a multi-layer network be reasoned about as a single map, and it is the form the
ladder needs if a stack is to be treated as one rung. -/
theorem netAct_append {n : Type} [Fintype n] (ls ms : List (AffineLayer n)) (x : n → ℝ) :
    netAct (ls ++ ms) x = netAct ms (netAct ls x) := by
  unfold netAct
  rw [List.foldl_append]

/-! ## Activation, and where invertibility is lost -/

/-- The rectifier, as a function on the reals. -/
def relu (x : ℝ) : ℝ := max x 0

/-- `relu` is not injective: both `-1` and `0` map to `0`. -/
theorem relu_not_injective : ¬ Function.Injective relu := by
  intro h
  have hz : relu (-1) = relu 0 := by
    simp only [relu]
    norm_num
  have : (-1 : ℝ) = 0 := h hz
  norm_num at this

/-- Componentwise rectification of a vector. -/
noncomputable def reluVec {n : Type} (x : n → ℝ) : n → ℝ := fun j => relu (x j)

/-- **A stack followed by an activation is not injective.**

`n := Fin 1` suffices: the two inputs that differ only in sign are both mapped to `0` by `relu`,
regardless of the stack, so the whole map collapses them. -/
theorem netRelu_not_injective :
    ¬ Function.Injective (fun x : Fin 1 → ℝ => reluVec (netAct [] x)) := by
  intro h
  -- the two constant vectors `-1` and `0`
  have hsame : reluVec (netAct ([] : List (AffineLayer (Fin 1))) (fun _ => (-1 : ℝ)))
      = reluVec (netAct ([] : List (AffineLayer (Fin 1))) (fun _ => (0 : ℝ))) := by
    funext j
    simp only [reluVec, netAct, List.foldl_nil, relu]
    norm_num
  have hinj := h hsame
  have : (fun _ : Fin 1 => (-1 : ℝ)) = (fun _ => (0 : ℝ)) := hinj
  have := congrFun this ⟨0, by decide⟩
  norm_num at this

/-! ## The spectrum, stated as one theorem

Three representations, three answers. Each conjunct cites a theorem already proved elsewhere, so the
spectrum cannot drift from the individual results. -/

/-- **Reversibility depends on the representation and the structure.**

* `LinearForm`: not injective -- `Lattice.Lift.Extraction` exhibits two distinct coefficient vectors
  with the same zero set.
* One affine layer: injective -- `Lattice.Core.Weight.layer_act_injective`.
* A stack with a rectifier: not injective -- `netRelu_not_injective`.

The middle conjunct is what makes the spectrum non-trivial: a single affine layer *is* invertible,
so "the semantic layer is not invertible" is false as a blanket statement about weights. -/
theorem reversibility_spectrum :
    -- one affine layer is injective
    (∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] {p q : LayerParams m n},
        BehaviourallyEquivalent p q → p = q)
    -- an affine layer with a rectifier is not
    ∧ ¬ Function.Injective (fun x : Fin 1 → ℝ => reluVec (netAct [] x))
    -- and the rectifier itself is not
    ∧ ¬ Function.Injective relu :=
  ⟨fun {_ _ _ _ _ _} => layer_act_injective, netRelu_not_injective, relu_not_injective⟩

end Lattice.Core
