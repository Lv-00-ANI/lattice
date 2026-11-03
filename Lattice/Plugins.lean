/-
# LATTICE Plugins

Aggregator for the plugin framework and the plugins migrated so far.

## Layering

`Manifest` fixes the vocabulary; `Registry` states the completeness predicates over an
arbitrary plugin list; this file supplies the actual list. The dependency arrow runs
plugin -> framework, never the reverse: `Registry.lean` cannot name `proofRegistry`, for the
same reason a class cannot name its subclasses.

## How to add a plugin

Two edits: import its `Plugin.lean` here, and add the `VerifiedPlugin` it exports to
`proofRegistry`. Nothing else changes, which is what makes migration a mechanical process.
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Core
import Lattice.Plugins.Domains
import Lattice.Plugins.Compose
import Lattice.Plugins.Extractors
import Lattice.Plugins.Architectures

namespace Lattice.Plugins

open Lattice.Plugins.Domains.Constraints.Penalty
open Lattice.Plugins.Domains.Constraints.Tokens

/-- **The registry of verified plugins.**

Every entry must carry a manifest whose obligations name real theorems, and a `consistent`
field proved from them. **Four plugins are migrated so far** -- `Core.Repair`,
`Domains.Constraints.Penalty`, `Domains.Constraints.Tokens` and `Extractors.ChainSlot`; the
remaining 32 become rows here as P3 proceeds.
-/
def proofRegistry : List VerifiedPlugin :=
  [Lattice.Plugins.Core.Constraint.verified,
   Lattice.Plugins.Core.Repair.verified,
   Lattice.Plugins.Domains.Constraints.Penalty.verified,
   Lattice.Plugins.Domains.Constraints.Tokens.verified,
   Lattice.Plugins.Compose.verified,
   Lattice.Plugins.Extractors.ChainSlot.verified,
   Lattice.Plugins.Architectures.GNN.verified,
   Lattice.Plugins.Architectures.Norm.verified]

/-- The registry contains the penalty plugin. -/
theorem proofRegistry_penalty_mem :
    Lattice.Plugins.Domains.Constraints.Penalty.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the repair plugin. -/
theorem proofRegistry_repair_mem :
    Lattice.Plugins.Core.Repair.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the tokenisation plugin. -/
theorem proofRegistry_tokens_mem :
    Lattice.Plugins.Domains.Constraints.Tokens.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the chain-slot extractor. -/
theorem proofRegistry_extractor_mem :
    Lattice.Plugins.Extractors.ChainSlot.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the constraint-logic plugin. -/
theorem proofRegistry_constraint_mem :
    Lattice.Plugins.Core.Constraint.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the normalisation carrier. -/
theorem proofRegistry_norm_mem :
    Lattice.Plugins.Architectures.Norm.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the graph-network carrier. -/
theorem proofRegistry_gnn_mem :
    Lattice.Plugins.Architectures.GNN.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the composition-algebra plugin. -/
theorem proofRegistry_compose_mem :
    Lattice.Plugins.Compose.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry currently holds exactly eight plugins. -/
theorem proofRegistry_length : proofRegistry.length = 8 := rfl

/-- **Every registered plugin is consistent.** -/
def RegistryConsistent : Prop := RegistryConsistentFor proofRegistry

/-- **The registry is consistent**: all eight entries discharge their bundles.

Each case is closed by the plugin's own `proof_holds`, so a plugin that stopped proving
something would break this theorem rather than being silently admitted. -/
theorem registryConsistent_holds : RegistryConsistent := by
  intro p hp
  rw [proofRegistry] at hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ => Lattice.Plugins.Core.Constraint.proof_holds
  · exact fun _ => Lattice.Plugins.Core.Repair.proof_holds
  · exact fun _ => Lattice.Plugins.Domains.Constraints.Penalty.proof_holds
  · exact fun _ => Lattice.Plugins.Domains.Constraints.Tokens.proof_holds
  · exact fun _ => Lattice.Plugins.Compose.proof_holds
  · exact fun _ => Lattice.Plugins.Extractors.ChainSlot.proof_holds
  · exact fun _ => Lattice.Plugins.Architectures.GNN.proof_holds
  · exact fun _ => Lattice.Plugins.Architectures.Norm.proof_holds

/-- **Every mandatory kind is now covered.**

**All eleven of `mandatoryKinds`**: **with `Compose`, `recovery`, `spatial` and `confluence` joined
the eight that were already witnessed.**

**The last three arrived together and the reason is structural**: they are properties of how
components COMBINE, so no single-carrier plugin could have them.
**`Compose.parallel_comm_run` supplies `spatial`, `Compose.compose_run_assoc` supplies
`confluence`, and the two unit laws supply `recovery`** -- **a unit is what makes "omit a step and
the composite is unchanged" true.**
**`recovery` is NOT claimed as invertibility; the project has refuted that
(`no_extractor_preserves_both`).**

**Note this is `coverage`, i.e. "at least one witness per kind".** **It says nothing about how MANY
theorems remain unmigrated, and `pluginCensusPending` below records that separately.** -/
theorem coverage_all_mandatory :
    ∀ k ∈ mandatoryKinds, ∃ p ∈ proofRegistry, p.manifest.claims k = true := by
  intro k hk
  simp only [mandatoryKinds, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- .soundness: the constraint-logic plugin
    exact ⟨_, proofRegistry_constraint_mem, rfl⟩
  · -- .completeness: the tokenisation plugin
    exact ⟨_, proofRegistry_tokens_mem, rfl⟩
  · -- .laws: the repair plugin
    exact ⟨_, proofRegistry_repair_mem, rfl⟩
  · -- .exactness: the chain-slot extractor
    exact ⟨_, proofRegistry_extractor_mem, rfl⟩
  · -- .approximation: the penalty plugin
    exact ⟨_, proofRegistry_penalty_mem, rfl⟩
  · -- .recovery: the composition algebra (identity is a two-sided unit)
    exact ⟨_, proofRegistry_compose_mem, rfl⟩
  · -- .spatial: the composition algebra (parallel composition commutes)
    exact ⟨_, proofRegistry_compose_mem, rfl⟩
  · -- .confluence: the composition algebra (composition is associative)
    exact ⟨_, proofRegistry_compose_mem, rfl⟩
  · -- .equivariance: the graph-network carrier
    exact ⟨_, proofRegistry_gnn_mem, rfl⟩
  · -- .idempotence: the normalisation carrier
    exact ⟨_, proofRegistry_norm_mem, rfl⟩
  · -- .invariants: the graph-network carrier (its invariant readout)
    exact ⟨_, proofRegistry_gnn_mem, rfl⟩

/-- **Registry completeness, as the plan defines it.** -/
def PluginRegistryComplete : Prop :=
  RegistryCompleteFor proofRegistry

/-- **The project's completion predicate.**

**The nine targets of the execution plan, conjoined with registry completeness.** The targets
`T0 … T8` have no Lean statement yet, so the predicate is currently *equal* to
`PluginRegistryComplete` -- recorded by `proofComplete_iff_registry` below rather than hidden.
Filling them in (P4/P5) will REPLACE that iff with a strict conjunction, i.e. make the
predicate harder, never easier.

It deliberately says nothing about C, weight I/O, formats, conformance, or training: those
are out of `ProofComplete` by construction.
-/
def ProofComplete : Prop :=
  PluginRegistryComplete

/-- **`ProofComplete` currently reduces to `PluginRegistryComplete`.**

This is a statement about the SHAPE of the definition, not a claim that completion holds:
`PluginRegistryComplete` itself is open, because `AllMandatoryKindsCoveredFor` fails for the
seven kinds no migrated plugin claims. -/
theorem proofComplete_iff_registry : ProofComplete ↔ PluginRegistryComplete :=
  Iff.rfl

/-- **The registry's kind-coverage is complete**, so the completion predicate now turns on the
PLUGIN CENSUS rather than on any missing kind. **See `pluginCensusPending` below.** -/
theorem coverageComplete_holds : AllMandatoryKindsCoveredFor proofRegistry := by
  intro k hk
  exact coverage_all_mandatory k (by simpa [mandatoryKinds] using hk)

/-- **`PluginRegistryComplete` holds**: the registry is consistent and every mandatory kind has a
witness. -/
theorem pluginRegistryComplete_holds : PluginRegistryComplete :=
  ⟨registryConsistent_holds, coverageComplete_holds⟩

/-- **The gap this registry still cannot see: unmigrated plugins.**

**`plugin-map.tsv` records 41 plugins in the tree; the registry lists 8.** **33 remain unmigrated,
and no predicate over `proofRegistry` alone can detect them.**
**=> the honest completion predicate needs a further conjunct relating the registry to the census.**

**The bound is written as `proofRegistry.length < 41` rather than as `8 < 41`, so the statement
means "the registry is smaller than the tree" -- the gap itself -- and stays meaningful as the
registry grows.** -/
def pluginCensusPending : Prop :=
  proofRegistry.length < 41

/-- **`pluginCensusPending` holds**: the registry is shorter than the plugin census. -/
theorem pluginCensusPending_holds : pluginCensusPending := by
  unfold pluginCensusPending proofRegistry
  norm_num

/-- **The honest statement of the current state.**

**Kind-coverage is complete AND the plugin census is not**, **together.**
**Any claim of project completion that omits the second conjunct would be false, and this theorem
is where that is recorded as a fact rather than as a remark.** -/
theorem current_state : PluginRegistryComplete ∧ pluginCensusPending :=
  ⟨pluginRegistryComplete_holds, pluginCensusPending_holds⟩

end Lattice.Plugins
