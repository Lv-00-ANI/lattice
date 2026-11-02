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
import Lattice.Plugins.Extractors

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
   Lattice.Plugins.Extractors.ChainSlot.verified]

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

/-- The registry currently holds exactly five plugins. -/
theorem proofRegistry_length : proofRegistry.length = 5 := rfl

/-- **Every registered plugin is consistent.** -/
def RegistryConsistent : Prop := RegistryConsistentFor proofRegistry

/-- **The registry is consistent**: all five entries discharge their bundles.

Each case is closed by the plugin's own `proof_holds`, so a plugin that stopped proving
something would break this theorem rather than being silently admitted. -/
theorem registryConsistent_holds : RegistryConsistent := by
  intro p hp
  rw [proofRegistry] at hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact fun _ => Lattice.Plugins.Core.Constraint.proof_holds
  · exact fun _ => Lattice.Plugins.Core.Repair.proof_holds
  · exact fun _ => Lattice.Plugins.Domains.Constraints.Penalty.proof_holds
  · exact fun _ => Lattice.Plugins.Domains.Constraints.Tokens.proof_holds
  · exact fun _ => Lattice.Plugins.Extractors.ChainSlot.proof_holds

/-- **The mandatory kinds the tree already covers.**

`soundness`, `laws`, `exactness`, `approximation` and `completeness` are claimed across the
five migrated plugins. **`laws` joined this set when `Core.Repair` was migrated** (its
`iterate_succ` is a monoid-action law), **`exactness` gained a second independent witness when
`Tokens` was migrated** (the flattening bijection), **and `soundness` gained its deepest witness
when `Core.Constraint` was migrated** (the two `Models` lemmas, which are what a compiler's
soundness theorem consumes).

**`Extractors.ChainSlot` is the first plugin whose EXACTNESS obligation concerns the REVERSE
direction**: `intermediate_poly_readable` says where a weight is, and the bundle's `soundness`
carries the matching impossibility (`deep_chain_final_slot_dead`).

The six still missing (`recovery`, `spatial`, `confluence`, `equivariance`, `idempotence`,
`invariants`) belong to plugins that have not been migrated. -/
theorem coverage_partial :
    (∀ k ∈ [ObligationKind.soundness, .laws, .exactness, .approximation, .completeness],
        ∃ p ∈ proofRegistry, p.manifest.claims k = true) := by
  intro k hk
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · -- soundness: the constraint-logic plugin
    exact ⟨_, proofRegistry_constraint_mem, rfl⟩
  · -- laws: the repair plugin
    exact ⟨_, proofRegistry_repair_mem, rfl⟩
  · -- exactness: the chain-slot extractor
    exact ⟨_, proofRegistry_extractor_mem, rfl⟩
  · -- approximation: the penalty plugin
    exact ⟨_, proofRegistry_penalty_mem, rfl⟩
  · -- completeness: the tokenisation plugin
    exact ⟨_, proofRegistry_tokens_mem, rfl⟩

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
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · -- the constraint-logic plugin does not claim recovery
    rw [Lattice.Plugins.Core.Constraint.verified_manifest,
        Lattice.Plugins.Core.Constraint.manifest_no_recovery] at hclaim
    exact Bool.false_ne_true hclaim
  · -- the repair plugin does not claim recovery
    rw [Lattice.Plugins.Core.Repair.verified_manifest,
        Lattice.Plugins.Core.Repair.manifest_no_recovery] at hclaim
    exact Bool.false_ne_true hclaim
  · -- the penalty plugin does not claim recovery
    rw [Lattice.Plugins.Domains.Constraints.Penalty.verified_manifest,
        Lattice.Plugins.Domains.Constraints.Penalty.manifest_no_recovery] at hclaim
    exact Bool.false_ne_true hclaim
  · -- the tokenisation plugin does not claim recovery
    rw [Lattice.Plugins.Domains.Constraints.Tokens.verified_manifest,
        Lattice.Plugins.Domains.Constraints.Tokens.manifest_no_recovery] at hclaim
    exact Bool.false_ne_true hclaim
  · -- the chain-slot extractor does not claim recovery
    rw [Lattice.Plugins.Extractors.ChainSlot.verified_manifest,
        Lattice.Plugins.Extractors.ChainSlot.manifest_no_recovery] at hclaim
    exact Bool.false_ne_true hclaim

/-- **`PluginRegistryComplete` is open**, stated as the negation of its coverage half. -/
theorem pluginRegistryComplete_not_yet : ¬ PluginRegistryComplete := by
  intro h
  exact registryComplete_fails h.2

end Lattice.Plugins
