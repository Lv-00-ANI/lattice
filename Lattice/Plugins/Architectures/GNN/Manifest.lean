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

namespace Lattice.Plugins.Architectures.GNN

open Lattice.Plugins

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
    -- EQUIVARIANCE: one message-passing step commutes with node relabelling.
    { name := "msgpass_equivariant"
      kind := .equivariance
      theoremName := "msgPass_equivariant"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- EQUIVARIANCE: a full layer (message pass + weights + nonlinearity) does too.
    { name := "gnn_layer_equivariant"
      kind := .equivariance
      theoremName := "gnnLayer_equivariant"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- EQUIVARIANCE: and so does any finite stack of layers -- equivariance composes in depth.
    { name := "layer_stack_equivariant"
      kind := .equivariance
      theoremName := "layerStack_equivariant"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- LAWS: the feature action is a group action (multiplicativity).
    { name := "perm_act_feat_mul"
      kind := .laws
      theoremName := "permActFeat_mul"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- LAWS: and unitality.
    { name := "perm_act_feat_one"
      kind := .laws
      theoremName := "permActFeat_one"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- LAWS: the adjacency action is a group action (multiplicativity).
    { name := "perm_act_adj_mul"
      kind := .laws
      theoremName := "permActAdj_mul"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- LAWS: and unitality.
    { name := "perm_act_adj_one"
      kind := .laws
      theoremName := "permActAdj_one"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- INVARIANTS: the sum readout does not depend on the labelling.
    { name := "readout_invariant"
      kind := .invariants
      theoremName := "readout_invariant"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- INVARIANTS: an invariant readout survives any depth of equivariant layers.
    { name := "readout_invariant_of_layer_stack"
      kind := .invariants
      theoremName := "readout_invariant_of_layerStack"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- SOUNDNESS: sparse message passing agrees with the dense one.
    { name := "sparse_agrees_dense"
      kind := .soundness
      theoremName := "sparseMsgPass_eq_msgPass"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" },
    -- APPROXIMATION: a bound on one message-passing step under a feature bound.
    { name := "msgpass_bound"
      kind := .approximation
      theoremName := "msgPass_bound_perm"
      file := "Lattice/Lib/Architectures/RealGNNEquivariance.lean" }
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
