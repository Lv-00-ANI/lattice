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
import Lattice.Plugins.Domains

namespace Lattice.Plugins

open Lattice.Plugins.Domains.Constraints.Penalty

/-- **The registry of verified plugins.**

Every entry must carry a manifest whose obligations name real theorems, and a `consistent`
field proved from them. **The Penalty plugin is the pilot and the only entry so far**; the
remaining 33 plugins become rows here as migration (P3) proceeds.
-/
def proofRegistry : List VerifiedPlugin :=
  [verified]

/-- The registry contains the penalty plugin. -/
theorem proofRegistry_penalty_mem : verified ∈ proofRegistry := by
  simp [proofRegistry]

/-- The registry currently holds exactly one plugin. -/
theorem proofRegistry_length : proofRegistry.length = 1 := rfl

/-- **Every registered plugin is consistent.** -/
def RegistryConsistent : Prop := RegistryConsistentFor proofRegistry

/-- **The registry is consistent**: the penalty plugin's bundle holds, and it is the only
entry. -/
theorem registryConsistent_holds : RegistryConsistent := by
  intro p hp
  rw [proofRegistry] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  exact fun _ => proof_holds

/-- **The mandatory kinds the tree already covers.**

`soundness`, `exactness`, `approximation` and `completeness` are claimed by the penalty
plugin. The rest (`laws`, `recovery`, `spatial`, `confluence`, `equivariance`,
`idempotence`, `invariants`) are not, because the plugins that would claim them have not
been migrated. -/
theorem coverage_partial :
    (∀ k ∈ [ObligationKind.soundness, .exactness, .approximation, .completeness],
        ∃ p ∈ proofRegistry, p.manifest.claims k = true) := by
  intro k hk
  refine ⟨verified, proofRegistry_penalty_mem, ?_⟩
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl

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
  simp only [List.mem_singleton] at hp
  subst hp
  -- `verified.manifest` IS `manifest`, so the claim can be reduced to the manifest lemma.
  rw [verified_manifest, manifest_no_recovery] at hclaim
  exact Bool.false_ne_true hclaim

/-- **`PluginRegistryComplete` is open**, stated as the negation of its coverage half. -/
theorem pluginRegistryComplete_not_yet : ¬ PluginRegistryComplete := by
  intro h
  exact registryComplete_fails h.2

end Lattice.Plugins
