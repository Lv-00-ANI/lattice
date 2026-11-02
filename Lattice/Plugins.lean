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

namespace Lattice.Plugins

open Lattice.Plugins.Domains.Constraints.Penalty

/-- **The registry of verified plugins.**

Every entry must carry a manifest whose obligations name real theorems, and a `consistent`
field proved from them. **Two plugins are migrated so far** -- `Core.Repair` and
`Domains.Constraints.Penalty`; the remaining 33 become rows here as P3 proceeds.
-/
def proofRegistry : List VerifiedPlugin :=
  [Lattice.Plugins.Core.Repair.verified, verified]

/-- The registry contains the penalty plugin. -/
theorem proofRegistry_penalty_mem : verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry contains the repair plugin. -/
theorem proofRegistry_repair_mem :
    Lattice.Plugins.Core.Repair.verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry currently holds exactly two plugins. -/
theorem proofRegistry_length : proofRegistry.length = 2 := rfl

/-- **Every registered plugin is consistent.** -/
def RegistryConsistent : Prop := RegistryConsistentFor proofRegistry

/-- **The registry is consistent**: both entries discharge their bundles.

Each case is closed by the plugin's own `proof_holds`, so a plugin that stopped proving
something would break this theorem rather than being silently admitted. -/
theorem registryConsistent_holds : RegistryConsistent := by
  intro p hp
  rw [proofRegistry] at hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact fun _ => Lattice.Plugins.Core.Repair.proof_holds
  · exact fun _ => proof_holds

/-- **The mandatory kinds the tree already covers.**

`soundness`, `laws`, `exactness`, `approximation` and `completeness` are claimed across the
two migrated plugins. **`laws` joined this set when `Core.Repair` was migrated**: its
`iterate_succ` is a genuine monoid-action law, which the penalty plugin had no instance of.

The six still missing (`recovery`, `spatial`, `confluence`, `equivariance`, `idempotence`,
`invariants`) belong to plugins that have not been migrated. -/
theorem coverage_partial :
    (∀ k ∈ [ObligationKind.soundness, .laws, .exactness, .approximation, .completeness],
        ∃ p ∈ proofRegistry, p.manifest.claims k = true) := by
  intro k hk
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · -- soundness: either plugin
    exact ⟨verified, proofRegistry_penalty_mem, rfl⟩
  · -- laws: the repair plugin
    exact ⟨Lattice.Plugins.Core.Repair.verified, proofRegistry_repair_mem, rfl⟩
  · -- exactness: either plugin
    exact ⟨verified, proofRegistry_penalty_mem, rfl⟩
  · -- approximation: either plugin
    exact ⟨verified, proofRegistry_penalty_mem, rfl⟩
  · -- completeness: either plugin
    exact ⟨verified, proofRegistry_penalty_mem, rfl⟩

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

/-- **The registry is NOT yet complete.**

Witnessed concretely: no registered plugin claims `.recovery`, so the coverage half of
`RegistryCompleteFor` fails. This theorem is what keeps the completion predicate honest --
without it, `ProofComplete` could be read as "done" by someone who only sees the definition.
-/
theorem registryComplete_fails :
    ¬ AllMandatoryKindsCoveredFor proofRegistry := by
  intro h
  obtain ⟨p, hp, hclaim⟩ := h .recovery (by simp [mandatoryKinds])
  rw [proofRegistry] at hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · -- the repair plugin does not claim recovery either
    rw [Lattice.Plugins.Core.Repair.verified_manifest,
        Lattice.Plugins.Core.Repair.manifest_no_recovery] at hclaim
    exact Bool.false_ne_true hclaim
  · -- `verified.manifest` IS `manifest`, so the claim reduces to the manifest lemma.
    rw [verified_manifest, manifest_no_recovery] at hclaim
    exact Bool.false_ne_true hclaim

/-- **`PluginRegistryComplete` is open**, stated as the negation of its coverage half. -/
theorem pluginRegistryComplete_not_yet : ¬ PluginRegistryComplete := by
  intro h
  exact registryComplete_fails h.2

end Lattice.Plugins
