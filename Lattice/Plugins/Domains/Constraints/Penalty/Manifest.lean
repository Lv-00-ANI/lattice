/-
# Penalty Plugin -- Manifest

The pilot plugin for the migration (P2-2). It is deliberately the FIRST one migrated,
because the penalty carrier is where the project's exactness story is most developed:
`penaltyLoss_eq_zero_iff_holds_*` already says, for each algebraic layer, that a vanishing
loss is EQUIVALENT to the constraint holding. That is the `Exactness/` obligation filled in
by the tree rather than promised by a document.

## What a manifest is for

The manifest is the plugin's claim, and `Registry.VerifiedPlugin` is where the claim is
discharged. Splitting them matters: the manifest can be written (and reviewed) before the
proof bundle is assembled, and the registry refuses to accept a manifest whose obligations
are not backed by theorems that actually exist.

## Where the theorems live

The obligations below name theorems in `Lattice/Domains/Constraints/`, extending
`Lattice.Core.VariableDerivative`'s style of naming: the theorem name states the property,
and the `file` field says where to find it so that an obligation can be checked mechanically
against the tree instead of being taken on trust.

**Round 550 note.** The plugin's `Semantics.lean` and `Plugin.lean` import the domain
modules; the manifest does NOT, because a manifest is data (strings and a taxonomy) and
importing the proofs into it would create the reverse dependency that `PLUGIN-PROOFS.md` §8
forbids.
-/

import Lattice.Plugins.Manifest

namespace Lattice.Plugins.Domains.Constraints.Penalty

open Lattice.Plugins

/-- **The penalty plugin's manifest.**

Layer `domains`, because the penalty carrier is a domain carrier: it turns a geometric
constraint into a real-valued loss. It consumes nothing (`requires = []`) and offers the
single capability `penalty.loss`, which is what a downstream `NetLoss` or `Repair` plugin
would require.
-/
def manifest : PluginManifest where
  name := "Domains.Constraints.Penalty"
  layer := .domains
  requires := []
  provides := ["penalty.loss"]
  obligations := [
    -- Exactness: a vanishing loss is EQUIVALENT to the constraint holding, per algebraic
    -- layer. This is the strongest statement the penalty carrier has, and it is the one
    -- T2 (penalty exactness) is built on.
    { name := "penalty_loss_zero_iff_holds_sq"
      kind := .exactness
      theoremName := "penaltyLoss_eq_zero_iff_holds_sq"
      file := "Lattice/Domains/Constraints/NetLossDerivative.lean" },
    { name := "penalty_loss_zero_iff_holds_leZero"
      kind := .exactness
      theoremName := "penaltyLoss_eq_zero_iff_holds_leZero"
      file := "Lattice/Domains/Constraints/NetLossDerivative.lean" },
    -- Soundness: the loss is well defined and invariant under the substitutions the repair
    -- loop performs, so that a repaired state is judged by the same loss.
    { name := "penalty_loss_congr_of_indicesBelow"
      kind := .soundness
      theoremName := "penaltyLoss_congr_of_indicesBelow"
      file := "Lattice/Domains/Constraints/NetLossDerivative.lean" },
    -- Approximation: each constraint family's loss is Lipschitz in the point cloud, which is
    -- the quantitative half: exactness says WHEN the loss vanishes, this says how fast.
    { name := "penalty_loss_lipschitz_eqZero"
      kind := .approximation
      theoremName := "eqZero_lipschitz"
      file := "Lattice/Domains/Constraints/PenaltyLoss.lean" },
    { name := "penalty_loss_lipschitz_gtZero"
      kind := .approximation
      theoremName := "gtZero_lipschitz"
      file := "Lattice/Domains/Constraints/PenaltyLoss.lean" },
    { name := "penalty_loss_lipschitz_equalLength"
      kind := .approximation
      theoremName := "equalLength_lipschitz"
      file := "Lattice/Domains/Constraints/PenaltyLoss.lean" },
    -- Completeness: the `max_zero` family is how an INEQUALITY constraint is encoded, and
    -- `max_zero_eq_zero_iff` is the totality statement that every inequality is representable.
    { name := "penalty_max_zero_eq_zero_iff"
      kind := .completeness
      theoremName := "max_zero_eq_zero_iff"
      file := "Lattice/Domains/Constraints/PenaltyLoss.lean" }
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims exactly the seven obligations listed above. -/
theorem manifest_obligation_count : manifest.obligations.length = 7 := rfl

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

/-- The manifest belongs to the `domains` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.domains := rfl

/-- The plugin offers exactly one capability. -/
theorem manifest_provides : manifest.provides = ["penalty.loss"] := rfl

/-- The plugin requires no other plugin. -/
theorem manifest_requires_nothing : manifest.requires = [] := rfl

/-- The manifest claims exactness -- the obligation T2 rests on. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- The manifest claims approximation -- the quantitative half. -/
theorem manifest_claims_approximation : manifest.claims .approximation = true := rfl

/-- The manifest does NOT claim refinement: the C backend is out of scope. -/
theorem manifest_no_refinement : manifest.claims .refinement = false := rfl

/-- The manifest does NOT claim recovery: the penalty carrier has no install/uninstall. -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- The manifest does NOT claim spatial: the penalty carrier has no spatial extent. -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- The manifest does NOT claim confluence: the penalty carrier has no effects to order. -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- The manifest does NOT claim idempotence: the penalty carrier is not applied twice. -/
theorem manifest_no_idempotence : manifest.claims .idempotence = false := rfl

end Lattice.Plugins.Domains.Constraints.Penalty
