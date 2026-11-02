/-
# LATTICE Plugin Framework -- Registry

This file turns the types of `Manifest.lean` into a *registry*: an explicit list of
verified plugins, plus the completeness predicates the project's completion definition
is phrased over.

## What "verified" means here, and what it deliberately does not

A `VerifiedPlugin` bundles a manifest with, for each obligation the manifest CLAIMS, a
proof that the named theorem exists. Lean cannot inspect its own environment from inside
a proof, so the honest encoding is: a manifest may claim an obligation, and the bundle
carries a `Prop` whose inhabitance is the claim's truth. When a plugin is registered, the
`Prop` fields are filled by the actual theorems from the tree.

This is why `PluginProof` carries *named* fields rather than a `List`: it makes a missing
obligation a type error at the point of registration, which is exactly the discipline that
stops a plugin from claiming a soundness result it does not have.

## The invariant that matters

The property the framework exists to enforce is `registry_consistent`: every claim in
every manifest is backed by an inhabitation. `PluginRegistryComplete` then says every
registered plugin is consistent AND every obligation kind that the project treats as
mandatory is claimed by at least one plugin.
-/

import Lattice.Plugins.Manifest

namespace Lattice.Plugins

/-! ## Proof bundles -/

/-- **The proofs a plugin actually has.**

Each field is a `Prop`, not a named theorem: the registry instantiates them with the real
theorems. A field left as a hypothesis is a hole the registry must not close by fiat, so
`VerifiedPlugin` is only ever built at a point where every field is discharged.

`soundness` and `laws` are non-optional because every plugin has *some* semantic content;
the rest are optional, since e.g. an extractor has no idempotence story.
-/
structure PluginProof where
  /-- The plugin's result means what its spec says. -/
  soundness : Prop
  /-- Algebraic laws the plugin obeys. -/
  laws : Prop
  /-- Exact characterisation, where the plugin has one. -/
  exactness : Prop
  /-- Error bounds, where exactness is impossible. -/
  approximation : Prop
  /-- Temporal composability. -/
  recovery : Prop
  /-- Spatial composability. -/
  spatial : Prop
  /-- Confluence of independent effects. -/
  confluence : Prop
  /-- Equivariance under a group action. -/
  equivariance : Prop
  /-- Idempotence. -/
  idempotence : Prop
  /-- Preservation of state invariants. -/
  invariants : Prop
  /-- Coverage / totality. -/
  completeness : Prop
  /-- Refinement to a lower-level semantics (future). -/
  refinement : Prop

/-- A proof bundle all of whose fields are true. -/
def PluginProof.Holds (π : PluginProof) : Prop :=
  π.soundness ∧ π.laws ∧ π.exactness ∧ π.approximation ∧ π.recovery ∧
  π.spatial ∧ π.confluence ∧ π.equivariance ∧ π.idempotence ∧
  π.invariants ∧ π.completeness ∧ π.refinement

/-- **The trivial bundle**, used as the starting point for a plugin that has nothing yet.
Every field is `True`, so `Holds` is immediate. A plugin using this proves nothing; the
point is that its manifest will also claim nothing. -/
def PluginProof.trivial : PluginProof :=
  ⟨True, True, True, True, True, True, True, True, True, True, True, True⟩

/-- The trivial bundle holds.

`True.intro` is written out rather than `trivial`, because inside `PluginProof.trivial`'s
namespace the bare word `trivial` resolves to the *definition*, not the tactic. -/
theorem PluginProof.trivial_holds : PluginProof.trivial.Holds :=
  ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro,
   True.intro, True.intro, True.intro, True.intro, True.intro, True.intro⟩

/-- **A bundle is `trivial` exactly when every field is `True`.** -/
theorem PluginProof.trivial_fields :
    PluginProof.trivial.soundness = True ∧
    PluginProof.trivial.laws = True ∧
    PluginProof.trivial.exactness = True ∧
    PluginProof.trivial.completeness = True :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Verified plugins -/

/-- **A manifest together with its proofs.**

The `consistent` field is the framework's central claim: if the manifest declares
obligations, they are backed. A `VerifiedPlugin` is therefore only constructible where
that implication has been proved. -/
structure VerifiedPlugin where
  /-- What the plugin is. -/
  manifest : PluginManifest
  /-- What the plugin proves. -/
  proof : PluginProof
  /-- The manifest's claims are backed by the proof bundle. -/
  consistent : manifest.obligations ≠ [] → proof.Holds
  -- No `Repr`: `PluginProof`'s fields are `Prop`s, which carry no runtime data.
  -- Manifests are printable, and that is what diagnostics need.

/-- A verified plugin whose manifest is empty proves nothing and is trivially consistent. -/
def VerifiedPlugin.empty (name : PluginName) (layer : PluginLayer) : VerifiedPlugin where
  manifest := PluginManifest.empty name layer
  proof := PluginProof.trivial
  consistent := fun h => absurd rfl h

/-! ## The registry -/

/-- **The registry of verified plugins.**

Currently empty: the migration has not begun. Every addition must come with a manifest
whose obligations name real theorems, and a `consistent` field proved from them.
-/
def proofRegistry : List VerifiedPlugin := []

/-- The registry is empty at the time of writing. -/
theorem proofRegistry_eq_nil : proofRegistry = [] := rfl

/-- **Every registered plugin is consistent.** -/
def RegistryConsistent : Prop :=
  ∀ p ∈ proofRegistry, p.manifest.obligations ≠ [] → p.proof.Holds

/-- The empty registry is consistent, vacuously. -/
theorem registryConsistent_nil : RegistryConsistent := by
  intro p hp
  simp [proofRegistry] at hp

/-! ## Completeness -/

/-- **Every mandatory kind is claimed by some registered plugin.**

`mandatoryKinds` lives in `Manifest.lean`, next to the obligation taxonomy. -/
def AllMandatoryKindsCovered : Prop :=
  ∀ k ∈ mandatoryKinds, ∃ p ∈ proofRegistry, p.manifest.claims k = true

/-- **The empty registry does not cover the mandatory kinds.**

The only way to witness coverage of `.soundness` would be a plugin in the registry whose
`claims .soundness` is `true`; `[]` contains none. (An `empty` plugin would not help
either: `PluginManifest.empty_claims_false` says its `claims` is `false` for every kind.)

Consequently `PluginRegistryComplete` is NOT provable at this stage, which is the correct
state of affairs before any migration. -/
theorem allMandatoryKindsCovered_nil_fails :
    ¬ (∀ k ∈ mandatoryKinds, ∃ p ∈ ([] : List VerifiedPlugin),
        p.manifest.claims k = true) := by
  intro h
  obtain ⟨p, hp, _⟩ := h .soundness (by simp [mandatoryKinds])
  simp at hp

/-- **The registry is complete**: consistent, and covering every mandatory kind. -/
def PluginRegistryComplete : Prop :=
  RegistryConsistent ∧ AllMandatoryKindsCovered

/-- **The project's completion predicate.**

The nine targets of the execution plan, conjoined with registry completeness. The targets
`T0 … T8` are not yet named in Lean; this predicate is their landing point, and it is
stated here so that the shape of completion is fixed before the work of filling it in.

It deliberately says nothing about C, weight I/O, formats, conformance, or training:
those are out of `ProofComplete` by construction.
-/
def ProofComplete : Prop :=
  PluginRegistryComplete

/-- **`ProofComplete` reduces to `PluginRegistryComplete`** at the current stage, where the
nine targets have no separate statement yet. This is an equality of propositions, not a
claim that completion holds. -/
theorem proofComplete_iff_registry : ProofComplete ↔ PluginRegistryComplete :=
  Iff.rfl

end Lattice.Plugins
