/-
# Architectures.GNN Plugin -- assembly

The eleven obligations of `Manifest.lean`, discharged by
`Lattice.Lib.Architectures.RealGNNEquivariance`.

## Why the two group-action laws are obligations and not decoration

**`permActFeat_mul` / `permActFeat_one` and `permActAdj_mul` / `permActAdj_one` say that the two
permutation "actions" really ARE actions in the algebraic sense.**

**Without them, "equivariance" would be a statement about a family of maps indexed by
permutations, not about a GROUP action -- and the word would be doing no work.**
**With them, `msgPass_equivariant` is a genuine naturality square: the diagram
`h ↦ msgPass A h` commutes with the group action.**
**=> the laws are the premise that makes the equivariance statement meaningful, which is why they
sit in the same manifest.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Architectures.GNN.Manifest
import Lattice.Plugins.Architectures.GNN.Proofs
namespace Lattice.Plugins.Architectures.GNN

open Lattice.Plugins

/-- **Equivariance: one message-passing step commutes with node relabelling.** -/
def MsgPassEquivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h : ι → ℝ),
    msgPass (permActAdj π A) (permActFeat π h) = permActFeat π (msgPass A h)

/-- **`MsgPassEquivariantProp` holds** -- by `msgPass_equivariant`. -/
theorem msgPassEquivariantProp_holds : MsgPassEquivariantProp := by
  intro ι _ _ π A h
  exact msgPass_equivariant π A h

/-- **Equivariance: a full layer does too.** -/
def GnnLayerEquivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (h : ι → ℝ),
    gnnLayer (permActAdj π A) W σ (permActFeat π h)
      = permActFeat π (gnnLayer A W σ h)

/-- **`GnnLayerEquivariantProp` holds** -- by `gnnLayer_equivariant`. -/
theorem gnnLayerEquivariantProp_holds : GnnLayerEquivariantProp := by
  intro ι _ _ π A W σ h
  exact gnnLayer_equivariant π A W σ h

/-- **Equivariance composes along depth: any finite stack of layers is equivariant.** -/
def LayerStackEquivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (k : ℕ) (h : ι → ℝ),
    layerStack (permActAdj π A) W σ k (permActFeat π h)
      = permActFeat π (layerStack A W σ k h)

/-- **`LayerStackEquivariantProp` holds** -- by `layerStack_equivariant`. -/
theorem layerStackEquivariantProp_holds : LayerStackEquivariantProp := by
  intro ι _ _ π A W σ k h
  exact layerStack_equivariant π A W σ k h

/-- **Law: the feature action is multiplicative.** -/
def PermActFeatMulProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π σ : Equiv.Perm ι) (h : ι → ℝ),
    permActFeat (π * σ) h = permActFeat π (permActFeat σ h)

/-- **`PermActFeatMulProp` holds** -- by `permActFeat_mul`. -/
theorem permActFeatMulProp_holds : PermActFeatMulProp := by
  intro ι _ _ π σ h
  exact permActFeat_mul π σ h

/-- **Law: the feature action is unital.** -/
def PermActFeatOneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → ℝ), permActFeat 1 h = h

/-- **`PermActFeatOneProp` holds** -- by `permActFeat_one`. -/
theorem permActFeatOneProp_holds : PermActFeatOneProp := by
  intro ι _ _ h
  exact permActFeat_one h

/-- **Law: the adjacency action is multiplicative.** -/
def PermActAdjMulProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π σ : Equiv.Perm ι) (A : ι → ι → ℝ),
    permActAdj (π * σ) A = permActAdj π (permActAdj σ A)

/-- **`PermActAdjMulProp` holds** -- by `permActAdj_mul`. -/
theorem permActAdjMulProp_holds : PermActAdjMulProp := by
  intro ι _ _ π σ A
  exact permActAdj_mul π σ A

/-- **Law: the adjacency action is unital.** -/
def PermActAdjOneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → ι → ℝ), permActAdj 1 A = A

/-- **`PermActAdjOneProp` holds** -- by `permActAdj_one`. -/
theorem permActAdjOneProp_holds : PermActAdjOneProp := by
  intro ι _ _ A
  exact permActAdj_one A

/-- **Invariant: the sum readout does not depend on the labelling.** -/
def ReadoutInvariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (h : ι → ℝ),
    ∑ i, permActFeat π h i = ∑ i, h i

/-- **`ReadoutInvariantProp` holds** -- by `readout_invariant`. -/
theorem readoutInvariantProp_holds : ReadoutInvariantProp := by
  intro ι _ _ π h
  exact readout_invariant π h

/-- **Invariant: an invariant readout survives any depth of equivariant layers.**

Note the right-hand side: `Φ (layerStack A W σ k h)`, NOT `Φ (permActFeat π (layerStack …))` --
because `Φ` is ALREADY assumed permutation-invariant, the relabelling collapses and the statement
becomes an equality between the readout of the permuted input and the readout of the original. -/
def ReadoutInvariantOfLayerStackProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (Φ : (ι → ℝ) → ℝ),
    (∀ (τ : Equiv.Perm ι) (f : ι → ℝ), Φ (permActFeat τ f) = Φ f) →
    ∀ (k : ℕ) (h : ι → ℝ),
      Φ (layerStack (permActAdj π A) W σ k (permActFeat π h))
        = Φ (layerStack A W σ k h)

/-- **`ReadoutInvariantOfLayerStackProp` holds** -- by `readout_invariant_of_layerStack`. -/
theorem readoutInvariantOfLayerStackProp_holds : ReadoutInvariantOfLayerStackProp := by
  intro ι _ _ π A W σ Φ hΦ k h
  exact readout_invariant_of_layerStack π A W σ Φ hΦ k h

/-- **Soundness: sparse message passing agrees with the dense one.** -/
def SparseAgreesDenseProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (E : Finset (ι × ι)) (h : ι → ℝ),
    sparseMsgPass E h = msgPass (indicator E) h

/-- **`SparseAgreesDenseProp` holds** -- by `sparseMsgPass_eq_msgPass`. -/
theorem sparseAgreesDenseProp_holds : SparseAgreesDenseProp := by
  intro ι _ _ E h
  exact sparseMsgPass_eq_msgPass E h

/-- **Approximation: a pointwise bound on one message-passing step.**

The bound is `M * ∑ j, |A (π.symm i) j|` -- **a per-row bound, not a global one**, and the
permutation appears because the adjacency has been relabelled. -/
def MsgPassBoundProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (h : ι → ℝ) (M : ℝ), (∀ j, |h j| ≤ M) →
    ∀ i : ι, |msgPass (permActAdj π A) (permActFeat π h) i|
      ≤ M * ∑ j, |A (π.symm i) j|

/-- **`MsgPassBoundProp` holds** -- by `msgPass_bound_perm`. -/
theorem msgPassBoundProp_holds : MsgPassBoundProp := by
  intro ι _ _ π A h M hM i
  exact msgPass_bound_perm π A h M hM i

/-- **The graph-network carrier's proof bundle.**

Eleven claimed obligations, including the registry's FIRST `equivariance` and FIRST `invariants`
witnesses.
-/
def proof : PluginProof where
  soundness := SparseAgreesDenseProp
  laws := PermActFeatMulProp ∧ PermActFeatOneProp ∧ PermActAdjMulProp ∧ PermActAdjOneProp
  exactness := True
  approximation := MsgPassBoundProp
  recovery := True
  spatial := True
  confluence := True
  equivariance := MsgPassEquivariantProp ∧ GnnLayerEquivariantProp ∧ LayerStackEquivariantProp
  idempotence := True
  invariants := ReadoutInvariantProp ∧ ReadoutInvariantOfLayerStackProp
  completeness := True
  refinement := True

/-- **Every claimed obligation of the graph-network carrier is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨sparseAgreesDenseProp_holds,
         ⟨permActFeatMulProp_holds, permActFeatOneProp_holds,
          permActAdjMulProp_holds, permActAdjOneProp_holds⟩,
         True.intro,
         msgPassBoundProp_holds,
         True.intro, True.intro, True.intro,
         ⟨msgPassEquivariantProp_holds, gnnLayerEquivariantProp_holds,
          layerStackEquivariantProp_holds⟩,
         True.intro,
         ⟨readoutInvariantProp_holds, readoutInvariantOfLayerStackProp_holds⟩,
         True.intro, True.intro⟩

/-- **The verified graph-network carrier.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The carrier claims eleven obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 11 := rfl

end Lattice.Plugins.Architectures.GNN
