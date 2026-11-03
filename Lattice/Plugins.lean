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
import Lattice.Plugins.Targets
import Lattice.Plugins.Runtime.RTargets
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

/-- **The plugin census, as a number the Lean file records but does not compute.**

**`plugin-map.tsv` is generated by `gov/plugin_inventory.py` from the tree.** **Lean cannot read it, so
the count must appear HERE as a literal.**
**The audit found this literal was `42` while the tree had 43, and that the mismatch went unnoticed for
three commits.**

**=> the literal is now NAMED (`pluginCensusSize`), carries its source in the docstring, and the
completion predicate is stated as `proofRegistry.length < pluginCensusSize`.**
**A future drift between the tree and this number is a one-line edit, and the audit's own check
(`plugin_inventory.py --check`, wired into `verify_all`) reports the tree's side of it.** -/
def pluginCensusSize : ℕ := 43

/-- **The gap this registry still cannot see: unmigrated plugins.**

**The registry lists 8; the census records `pluginCensusSize` = 43.**
**=> 35 remain unmigrated, and no predicate over `proofRegistry` ALONE can detect them.**

**The statement is `proofRegistry.length < pluginCensusSize` -- "the registry is smaller than the
tree", which is the gap itself, rather than a hard-coded subtraction.** -/
def pluginCensusPending : Prop :=
  proofRegistry.length < pluginCensusSize

/-- **`pluginCensusPending` holds**, because the registry is shorter than the census. -/
theorem pluginCensusPending_holds : pluginCensusPending := by
  unfold pluginCensusPending pluginCensusSize proofRegistry
  norm_num

/-- **The project's completion predicate.**

**The nine targets of the execution plan, CONJOINED with registry completeness and with the absence
of the census gap.**

**This is a strict conjunction, not an equality** -- **`proofComplete_iff_registry` was true when the
predicate WAS the registry condition, and it is FALSE now, deliberately.**

**=> `ProofComplete` requires:**
- **`PluginRegistryComplete`** -- **kind coverage, consistency, and NON-VACUITY** (**the third conjunct
  was added after the audit found the empty-plugin shortcut**);
- **`¬ pluginCensusPending`** -- **the registry is not smaller than the census**;
- **each target's proved content**, **and for T3 BOTH the parameter layer and the SEMANTIC layer**,
  **because the audit found T3's real content was outside the predicate.**

**It deliberately says nothing about C, weight I/O, formats, conformance, or training: those are out
of `ProofComplete` by construction.** -/
def ProofComplete : Prop :=
  PluginRegistryComplete ∧ ¬ pluginCensusPending ∧
    Lattice.Plugins.Targets.t1_compile_sound_instance ∧
    Lattice.Plugins.Targets.t1_merge_sound_unrejected ∧
    Lattice.Plugins.Targets.t1_compile_sound_general ∧
    Lattice.Plugins.Targets.t2_penalty_exact ∧
    Lattice.Plugins.Targets.t2_penalty_modulus ∧
    Lattice.Plugins.Targets.t3_parameter_roundtrip ∧
    Lattice.Plugins.Targets.t3_compile_injective ∧
    Lattice.Plugins.Targets.t3_semantic_not_injective ∧
    Lattice.Plugins.Targets.t3_no_faithful_extractor ∧
    Lattice.Plugins.Targets.t4_repair_progress ∧
    Lattice.Plugins.Targets.t4_loop_converges ∧
    Lattice.Plugins.Runtime.t5_recovery ∧
    Lattice.Plugins.Runtime.t6_spatial ∧
    Lattice.Plugins.Runtime.t7_confluence ∧
    Lattice.Plugins.Runtime.t8_failure_isolation

/-- **`ProofComplete` no longer reduces to `PluginRegistryComplete`.**

**The old `proofComplete_iff_registry` was `Iff.rfl` because the predicate WAS the registry
condition.**
**Now the implication one way is strict: `ProofComplete` implies the registry condition, but NOT
conversely, because the census half can fail while the kind half holds.**
**This theorem states the one direction that remains true and is the one a reader needs.** -/
theorem proofComplete_imp_registry : ProofComplete → PluginRegistryComplete :=
  fun h => h.1

/-- **The registry's kind-coverage is complete.** -/
theorem coverageComplete_holds : AllMandatoryKindsCoveredFor proofRegistry := by
  intro k hk
  exact coverage_all_mandatory k (by simpa [mandatoryKinds] using hk)

/-- **No plugin in the registry is vacuous.**

**Every entry is a `Plugin` file with a non-empty obligation list, and this theorem is the registry's
own certificate that the FAKE-COMPLETION PATH IS CLOSED.**
**Its proof is eight `rfl`s after the case split: the obligation counts are fixed by the manifests.** -/
theorem proofRegistry_nonvacuous : NonVacuousFor proofRegistry := by
  intro p hp
  rw [proofRegistry] at hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Lattice.Plugins.Core.Constraint.verified_manifest]
    exact Lattice.Plugins.Core.Constraint.manifest_nonempty
  · rw [Lattice.Plugins.Core.Repair.verified_manifest]
    exact Lattice.Plugins.Core.Repair.manifest_nonempty
  · rw [Lattice.Plugins.Domains.Constraints.Penalty.verified_manifest]
    exact Lattice.Plugins.Domains.Constraints.Penalty.manifest_nonempty
  · rw [Lattice.Plugins.Domains.Constraints.Tokens.verified_manifest]
    exact Lattice.Plugins.Domains.Constraints.Tokens.manifest_nonempty
  · rw [Lattice.Plugins.Compose.verified_manifest]
    exact Lattice.Plugins.Compose.manifest_nonempty
  · rw [Lattice.Plugins.Extractors.ChainSlot.verified_manifest]
    exact Lattice.Plugins.Extractors.ChainSlot.manifest_nonempty
  · rw [Lattice.Plugins.Architectures.GNN.verified_manifest]
    exact Lattice.Plugins.Architectures.GNN.manifest_nonempty
  · rw [Lattice.Plugins.Architectures.Norm.verified_manifest]
    exact Lattice.Plugins.Architectures.Norm.manifest_nonempty

/-- **`PluginRegistryComplete` holds**: the registry is consistent, NON-VACUOUS, and every mandatory
kind has a witness. -/
theorem pluginRegistryComplete_holds : PluginRegistryComplete :=
  ⟨registryConsistent_holds, proofRegistry_nonvacuous,
   coverageComplete_holds⟩

/-- **`ProofComplete` is NOT reachable.**

**Witness: `ProofComplete`'s second conjunct is `¬ pluginCensusPending`, while
`pluginCensusPending_holds` proves `pluginCensusPending`.**
**=> completion cannot be reached by finishing the kind list, which is exactly the failure mode the
previous round had.**

**The contradiction is closed by the hypothesis applied to the proof of the negated proposition --
`h.2.1` has type `¬ pluginCensusPending` and `pluginCensusPending_holds` has type
`pluginCensusPending`, so `h.2.1 pluginCensusPending_holds` IS the false proposition.** -/
theorem proofComplete_unreachable :
    ¬ ProofComplete := by
  intro h
  exact h.2.1 pluginCensusPending_holds

/-- **The honest statement of the current state.**

**Kind-coverage is complete, the plugin census is NOT, four of nine targets have proved cores, and
`ProofComplete` is therefore unreachable.**
**Any claim of project completion that omits any of these would be false, and this theorem is where
they are recorded as facts rather than remarks.** -/
theorem current_state :
    PluginRegistryComplete ∧ pluginCensusPending ∧
      Lattice.Plugins.Targets.proved_target_count = 8 ∧
      ¬ ProofComplete :=
  ⟨pluginRegistryComplete_holds, pluginCensusPending_holds, rfl, proofComplete_unreachable⟩

/-! ## The fake-completion path, and its closure -/

/-- **An empty plugin ADMITS no obligations, and `NonVacuousFor` rejects it.**

**This is the adversarial statement the audit demanded: it says, in Lean, that
`VerifiedPlugin.empty` cannot be part of a COMPLETE registry.**
**Before `NonVacuousForFor` was added, the consistency predicate was
`obligations ≠ [] → Holds`, so the empty plugin discharged it vacuously** -- **and 42 of them would have
made `pluginCensusPending` false while T0 and T5-T8 stood untouched.**

**The proof is two steps: `empty_plugin_is_vacuous` gives `obligations = []`, and `NonVacuousFor`
demands `≠ []`.** -/
theorem empty_plugin_excluded (name : PluginName) (layer : PluginLayer) :
    ¬ NonVacuousFor [VerifiedPlugin.empty name layer] := by
  intro h
  have hne := h (VerifiedPlugin.empty name layer) (by simp)
  rw [empty_plugin_is_vacuous] at hne
  exact hne rfl

/-- **A registry containing an empty plugin cannot be complete.**

**Consequence of `empty_plugin_excluded`: the `NonVacuousFor` conjunct of `RegistryCompleteFor` fails,
so the whole conjunction fails.**
**This closes the path at the level a reader cares about: the completion predicate itself.** -/
theorem registry_with_empty_plugin_not_complete (name : PluginName) (layer : PluginLayer)
    (rest : List VerifiedPlugin) :
    ¬ RegistryCompleteFor (VerifiedPlugin.empty name layer :: rest) := by
  intro h
  have hnv : NonVacuousFor (VerifiedPlugin.empty name layer :: rest) := h.2.1
  have hne := hnv (VerifiedPlugin.empty name layer) (by simp)
  rw [empty_plugin_is_vacuous] at hne
  exact hne rfl

end Lattice.Plugins
