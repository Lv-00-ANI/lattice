/-
# Architectures.GNN Plugin -- Manifest

The GRAPH-NEURAL-NETWORK carrier (P6, second of four). It is the plugin that closes the
`equivariance` gap in the registry's mandatory-kind coverage.

## Why equivariance belongs to the GNN carrier and not to Norm

**`Norm` normalises a point cloud's coordinates and has no group action on its inputs beyond
scaling.**
**A GNN acts on a GRAPH: relabelling the nodes is an action of the symmetric group, and the
architecture's defining property is that message passing COMMUTES with that relabelling.**
**=> the group, the action, and the equivariance law all live here; `Norm` correctly does not
claim the kind.**

## What the equivariance story actually is

**The group**: `Equiv.Perm ι`, the permutations of the node set.

**Two actions**: `permActFeat π h i = h (π.symm i)` on NODE FEATURES, and `permActAdj π A` on the
ADJACENCY MATRIX. **Both are genuine actions** -- `*_mul` and `*_one` are proved for each, so this
is a group action in the algebraic sense and not merely a family of maps.

**The equivariance law**: `msgPass (permActAdj π A) (permActFeat π h) = permActFeat π (msgPass A h)`
-- **relabel then pass messages = pass messages then relabel.**

**And the invariances**: `readout_invariant` (the sum readout is permutation-invariant) and
`readout_invariant_of_layerStack` (any invariant readout applied to any number of stacked
equivariant layers is still invariant).

**=> the equivariance composes along depth, and the readout is invariant. That pair is what a GNN
is supposed to be, and it is proved rather than assumed.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Architectures.GNN.Proofs

namespace Lattice.Plugins.Architectures.GNN

open Lattice.Plugins

-- **Round 772 (STAGE 3, final batch): the eleven obligations now CARRY their propositions.**
-- **These are the GNN carrier's equivariance/invariance laws -- the reason a graph network's output
-- does not depend on how the nodes happen to be numbered.**

/-- **`msgPass_equivariant`: 重编号节点后消息传递随之等变。** -/
def msgPass_equivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ) (h : ι → ℝ),
    msgPass (permActAdj π A) (permActFeat π h) = permActFeat π (msgPass A h)

/-- **`gnnLayer_equivariant`: 单层的等变性。** -/
def gnnLayer_equivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (h : ι → ℝ),
    gnnLayer (permActAdj π A) W σ (permActFeat π h) = permActFeat π (gnnLayer A W σ h)

/-- **`layerStack_equivariant`: 任意层数的等变性。** -/
def layerStack_equivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (W : ℝ) (σ : ℝ → ℝ) (k : ℕ) (h : ι → ℝ),
    layerStack (permActAdj π A) W σ k (permActFeat π h) = permActFeat π (layerStack A W σ k h)

/-- **`permActFeat_mul`: 特征置换是群作用。** -/
def permActFeat_mulProp : Prop :=
  ∀ {ι : Type} (π σ : Equiv.Perm ι) (h : ι → ℝ),
    permActFeat (π * σ) h = permActFeat π (permActFeat σ h)

/-- **`permActFeat_one`: 单位元不动。** -/
def permActFeat_oneProp : Prop :=
  ∀ {ι : Type} (h : ι → ℝ), permActFeat 1 h = h

/-- **`permActAdj_mul`: 邻接矩阵的置换也是群作用。** -/
def permActAdj_mulProp : Prop :=
  ∀ {ι : Type} (π σ : Equiv.Perm ι) (A : ι → ι → ℝ),
    permActAdj (π * σ) A = permActAdj π (permActAdj σ A)

/-- **`permActAdj_one`: 单位元不动邻接矩阵。** -/
def permActAdj_oneProp : Prop :=
  ∀ {ι : Type} (A : ι → ι → ℝ), permActAdj 1 A = A

/-- **`readout_invariant`: 读出（求和）在置换下不变。** -/
def readout_invariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (h : ι → ℝ),
    (Finset.univ.sum (fun i : ι => permActFeat π h i)) = Finset.univ.sum (fun i : ι => h i)

/-- **`readout_invariant_of_layerStack`: 置换不变的读出对整栈也不变。** -/
def readout_invariant_of_layerStackProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (A : ι → ι → ℝ) (W : ℝ) (σ : ℝ → ℝ) (Φ : (ι → ℝ) → ℝ),
    (∀ (τ : Equiv.Perm ι) (f : ι → ℝ), Φ (permActFeat τ f) = Φ f) →
      ∀ (k : ℕ) (h : ι → ℝ),
        Φ (layerStack (permActAdj π A) W σ k (permActFeat π h)) = Φ (layerStack A W σ k h)

/-- **`sparseMsgPass_eq_msgPass`: 稀疏与稠密消息传递一致。** -/
def sparseMsgPass_eq_msgPassProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (E : Finset (ι × ι)) (h : ι → ℝ),
    sparseMsgPass E h = msgPass (indicator E) h

/-- **`msgPass_bound_perm`: 置换后消息传递仍有界。** -/
def msgPass_bound_permProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (A : ι → ι → ℝ)
    (h : ι → ℝ) (M : ℝ),
    (∀ (j : ι), |h j| ≤ M) →
      ∀ (i : ι),
        |msgPass (permActAdj π A) (permActFeat π h) i|
          ≤ M * Finset.univ.sum (fun j : ι => |A ((Equiv.symm π) i) j|)

/-- **十一条命题就是十一条定理的类型。** -/
theorem gnn_props_hold :
    msgPass_equivariantProp ∧ gnnLayer_equivariantProp ∧ layerStack_equivariantProp
      ∧ permActFeat_mulProp ∧ permActFeat_oneProp ∧ permActAdj_mulProp
      ∧ permActAdj_oneProp ∧ readout_invariantProp ∧ readout_invariant_of_layerStackProp
      ∧ sparseMsgPass_eq_msgPassProp ∧ msgPass_bound_permProp :=
  ⟨@msgPass_equivariant, @gnnLayer_equivariant, @layerStack_equivariant,
   @permActFeat_mul, @permActFeat_one, @permActAdj_mul, @permActAdj_one,
   @readout_invariant, @readout_invariant_of_layerStack, @sparseMsgPass_eq_msgPass,
   @msgPass_bound_perm⟩

/-- **The graph-network carrier's manifest.**

Layer `architectures`. It requires the graph representation (`domain.graph`) and offers
`arch.messagepass`.
-/
def manifest : PluginManifest where
  name := "Architectures.GNN"
  layer := .architectures
  requires := ["domain.graph"]
  provides := ["arch.messagepass"]
  obligations := [
    -- **Round 772: all eleven go through `verifiedObligation`, so each CARRIES its proposition.**
    verifiedObligation "msgpass_equivariant" .equivariance
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "msgPass_equivariant" msgPass_equivariantProp,
    verifiedObligation "gnn_layer_equivariant" .equivariance
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "gnnLayer_equivariant" gnnLayer_equivariantProp,
    verifiedObligation "layer_stack_equivariant" .equivariance
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "layerStack_equivariant" layerStack_equivariantProp,
    verifiedObligation "perm_act_feat_mul" .laws
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "permActFeat_mul" permActFeat_mulProp,
    verifiedObligation "perm_act_feat_one" .laws
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "permActFeat_one" permActFeat_oneProp,
    verifiedObligation "perm_act_adj_mul" .laws
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "permActAdj_mul" permActAdj_mulProp,
    verifiedObligation "perm_act_adj_one" .laws
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "permActAdj_one" permActAdj_oneProp,
    verifiedObligation "readout_invariant" .invariants
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "readout_invariant" readout_invariantProp,
    verifiedObligation "readout_invariant_of_layer_stack" .invariants
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "readout_invariant_of_layerStack" readout_invariant_of_layerStackProp,
    verifiedObligation "sparse_agrees_dense" .soundness
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "sparseMsgPass_eq_msgPass" sparseMsgPass_eq_msgPassProp,
    verifiedObligation "msgpass_bound" .approximation
      "Lattice/Plugins/Architectures/GNN/Proofs.lean"
      "msgPass_bound_perm" msgPass_bound_permProp
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims eleven obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 11 := rfl

/-- **The manifest carries at least one obligation.**

Derived from `manifest_obligation_count`: if the list were `[]` its length would be `0`, contradicting
the stated count.
**This is what `NonVacuousFor` consumes. Having it as a NAMED lemma per manifest means a future edit
that empties the obligation list breaks HERE, rather than silently reopening the fake-completion
path.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  intro hnil
  have hlen := manifest_obligation_count
  rw [hnil] at hlen
  exact absurd hlen (by decide)

/-- The plugin lives in the `architectures` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.architectures := rfl

/-- It requires the graph representation. -/
theorem manifest_requires : manifest.requires = ["domain.graph"] := rfl

/-- It offers message passing. -/
theorem manifest_provides : manifest.provides = ["arch.messagepass"] := rfl

/-- **It claims EQUIVARIANCE** -- the mandatory kind no other migrated plugin can claim. -/
theorem manifest_claims_equivariance : manifest.claims .equivariance = true := rfl

/-- **It claims INVARIANTS** -- the readout invariances. -/
theorem manifest_claims_invariants : manifest.claims .invariants = true := rfl

/-- It claims laws -- the two group actions. -/
theorem manifest_claims_laws : manifest.claims .laws = true := rfl

/-- It claims soundness -- sparse/dense agreement. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- It claims approximation -- the message-passing bound. -/
theorem manifest_claims_approximation : manifest.claims .approximation = true := rfl

/-- **It does NOT claim idempotence**: a GNN layer is not applied to fix a point. -/
theorem manifest_no_idempotence : manifest.claims .idempotence = false := rfl

/-- **It does NOT claim confluence**: message passing is a function, not a rewriting system. -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- **It does NOT claim recovery.** -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- **It does NOT claim spatial composability.** -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- **It does NOT claim completeness**: not every graph is handled by the dense/sparse pair. -/
theorem manifest_no_completeness : manifest.claims .completeness = false := rfl

end Lattice.Plugins.Architectures.GNN
