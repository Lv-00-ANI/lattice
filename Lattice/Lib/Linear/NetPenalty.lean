import Mathlib
import Lattice.Core.WeightNet
import Lattice.Lib.Linear.PenaltyMatrix

/-!
# `Lattice.Lib.Linear.NetPenalty` -- T2 applied to the adopted weight representation

## Why this is in `lib/` and the representation is in `core/`

`Lattice.Core.WeightNet` says what the project's weight representation *is*: a stack of `AffineLayer`s with
a forward pass and an instance of `WeightSemantics`. That is a `core` fact.

This file says that **T2 applies to it**, which consumes `PenaltyMatrix` and therefore belongs in `lib/`.
Splitting along that boundary keeps `core` free of `lib` dependencies -- invariant I4 -- and is also the
honest description of the two claims.

## What is proved

`layer_penalty_exact`: a local minimiser of a layer's squared residual satisfies that layer's
constraint, provided the layer's weight matrix is surjective (the coordinate-free form of full row rank).

Stated over `AffineLayer`, which is the type the adopted representation is made of, so the theorem is
about the network's parameters rather than about linear algebra in the abstract. The proof instantiates
`PenaltyMatrix.sq_penalty_exact_matrix` at `A := l.W`.
-/

namespace Lattice.Lib.Linear.NetPenalty

open Lattice.Core
open Lattice.Lib.Linear.PenaltyMatrix

/-- The residual of a layer `l : AffineLayer n` at a point `x`: `Wᵀx + b`. -/
noncomputable def layerResid {n : ℕ} (l : AffineLayer (Fin n)) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j => (∑ i, l.W i j * x i) + l.b j

/-- The layer residual is the forward pass, so the penalty theorem is about the same object the network
evaluates. -/
theorem layerResid_eq_affineAct {n : ℕ} (l : AffineLayer (Fin n)) (x : Fin n → ℝ) :
    layerResid l x = affineAct l x := rfl

/-- **A layer is surjective** when every target residual is obtainable as a direction.

For finite-dimensional real spaces this is equivalent to the weight matrix having full row rank; it is
the form the penalty argument consumes. -/
def LayerSurjective {n : ℕ} (l : AffineLayer (Fin n)) : Prop :=
  ∀ r : Fin n → ℝ, ∃ d : Fin n → ℝ, ∀ j, ∑ i, l.W i j * d i = r j

/-- **T2 for a network layer.** A local minimiser of `Σⱼ (layerResid l x j)²` satisfies the layer's
constraint, provided the layer is surjective.

Note what the statement mentions: `AffineLayer`, `layerResid`, `IsLocalMin`. The penalty result has
become a statement about the parameters of the adopted representation.
-/
theorem layer_penalty_exact {n : ℕ} (l : AffineLayer (Fin n)) (hsurj : LayerSurjective l) :
    ∀ x : Fin n → ℝ,
      IsLocalMin (fun y => ∑ j, (layerResid l y j) ^ 2) x →
      ∀ j, layerResid l x j = 0 := by
  intro x hmin j
  have hA : Surjective (fun k i => l.W i k) := by
    intro r
    obtain ⟨d, hd⟩ := hsurj r
    exact ⟨d, funext fun k => hd k⟩
  have hresid : ∀ y : Fin n → ℝ, (fun k => residM (fun k i => l.W i k) l.b y k) = layerResid l y := by
    intro y
    funext k
    simp only [residM, layerResid, AMul]
  have hL : ∀ y : Fin n → ℝ,
      lossM (fun k i => l.W i k) l.b y = ∑ j, (layerResid l y j) ^ 2 := by
    intro y
    unfold lossM
    apply Finset.sum_congr rfl
    intro k _
    rw [congrFun (hresid y) k]
  have hmin' : IsLocalMin (lossM (fun k i => l.W i k) l.b) x := by
    have hfun : (lossM (fun k i => l.W i k) l.b) = (fun y => ∑ j, (layerResid l y j) ^ 2) :=
      funext hL
    rw [hfun]
    exact hmin
  have hres := sq_penalty_exact_matrix (fun k i => l.W i k) l.b hA x hmin' j
  rw [← congrFun (hresid x) j]
  exact hres

end Lattice.Lib.Linear.NetPenalty
