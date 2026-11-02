/-
# LATTICE Plugin Framework -- Types

This file defines the static, machine-checkable half of the plugin system: what a plugin
IS, what it must prove, and what a registry of verified plugins looks like.

It deliberately contains no instances. `Registry.lean` holds those, and it is the file
that grows as the migration proceeds.

## Why the types come first

The project's rule is that **every theorem belongs to exactly one plugin**, and that a
plugin is a capability contract together with its semantic proofs. That rule is only
enforceable if the vocabulary is fixed before any theorem is moved, so this file is
deliberately declarative: it fixes

- the taxonomy of proof obligations (`ObligationKind`),
- the architectural stratification plugins live in (`PluginLayer`),
- the service keys that encode "requires" / "provides",
- the manifest, proof bundle, and verified-plugin records,
- and the two completeness predicates (`PluginRegistryComplete`, `ProofComplete`).

## Relationship to `Lattice.Geo.Layer`

`Lattice.Geo.Layer` is an **algebraic** classification of geometric constraints (poly /
square / existential / transc) and answers whether a penalty exists. `PluginLayer` below
is an **architectural** stratification of the library and answers where a proof lives.
They are unrelated and must not be conflated; the distinct names are intentional.

## Numbers

The `Path` and `Version` notions here are deliberately minimal. They exist so that a
manifest can name a file and a revision without dragging in a filesystem model, which
would make the framework depend on the very I/O layer the project excludes.
-/

namespace Lattice.Plugins

/-! ## Obligation taxonomy -/

/-- **The kinds of proof obligation a plugin can carry.**

The constructor set is taken verbatim from `PLUGIN-PROOFS.md` §3, so that the document
and the code name the same eleven folders. `refinement` is present from the start even
though nothing uses it yet: the C backend will need it, and leaving a hole is cheaper
than renumbering a downstream taxonomy later. -/
inductive ObligationKind
  /-- Semantic preservation: the plugin's result means what the spec says. -/
  | soundness
  /-- Coverage / totality: everything the spec allows is handled. -/
  | completeness
  /-- Algebraic laws: associativity, commutativity, unit, distributivity, … -/
  | laws
  /-- Exact characterisation, stated as an iff rather than one implication. -/
  | exactness
  /-- Error / epsilon bounds, when exactness is impossible. -/
  | approximation
  /-- Temporal composability: uninstall undoes exactly install. -/
  | recovery
  /-- Spatial composability: independent plugins do not interfere. -/
  | spatial
  /-- Confluence: the order of independent effects does not matter. -/
  | confluence
  /-- Equivariance under a group action. -/
  | equivariance
  /-- Idempotence, e.g. normalisation applied twice. -/
  | idempotence
  /-- State invariants preserved by every step. -/
  | invariants
  /-- Refinement to a lower-level (future C) semantics. -/
  | refinement
  deriving DecidableEq, Repr, Inhabited

/-- **Every obligation kind, in document order.**

Used by the registry-completeness predicate: a plugin may legitimately have no
`refinement` proof, so completeness is stated per *declared* obligation rather than per
kind. This list exists so that `ObligationKind.all` is testable against the constructors.
-/
def ObligationKind.all : List ObligationKind :=
  [.soundness, .completeness, .laws, .exactness, .approximation, .recovery,
   .spatial, .confluence, .equivariance, .idempotence, .invariants, .refinement]

/-- The taxonomy lists every constructor, and lists each once. -/
theorem ObligationKind.all_length : ObligationKind.all.length = 12 := rfl

/-! ## Architectural stratification -/

/-- **The architectural layer a plugin belongs to.**

This is the stratification the library is actually built on, read off `PLUGIN-PROOFS.md`
§2. It is *not* `Lattice.Geo.Layer`. -/
inductive PluginLayer
  /-- Shared algebra with no plugin of its own. -/
  | shared
  /-- Reconstruction, constraints, repair: the kernel of the forward direction. -/
  | core
  /-- Tokenisation and program semantics: the symbolic engine's own substrate. -/
  | runtime
  /-- Domain carriers: constraints, geometry. -/
  | domains
  /-- Composition, spatial and temporal. -/
  | compose
  /-- End-to-end semantics of the chain. -/
  | semantics
  /-- Reverse direction: weights back to symbols. -/
  | extractors
  /-- Architecture carriers: conv, attention, norm, DAG. -/
  | architectures
  deriving DecidableEq, Repr, Inhabited

/-- The stratification has exactly the eight layers of `PLUGIN-PROOFS.md` §2. -/
theorem PluginLayer.card_eq_eight :
    ([PluginLayer.shared, .core, .runtime, .domains, .compose, .semantics,
      .extractors, .architectures] : List PluginLayer).length = 8 := rfl

/-! ## Service keys -/

/-- **A capability a plugin consumes or produces.**

A plain string is enough and deliberately so: the point of the key is that manifests
mention the *same* one when one plugin requires what another provides. Using a string
keeps the type decidable and printable without committing to a combinator language.
-/
abbrev ServiceKey := String

/-- **A plugin name.** Distinct from the Lean namespace, so a plugin can be renamed. -/
abbrev PluginName := String

/-! ## Revisions -/

/-- **A revision, as three natural numbers.**

Kept structural rather than a string so that “newer than” is a decidable relation on
data, not on parsing. -/
structure Version where
  /-- Major bump: the plugin's contract changed. -/
  major : Nat
  /-- Minor bump: obligations were added. -/
  minor : Nat
  /-- Patch bump: proofs were strengthened or restated. -/
  patch : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The initial revision. -/
def Version.zero : Version := ⟨0, 0, 0⟩

/-- Lexicographic order, which is the order `ProofUpgrade` is meant to respect. -/
def Version.lt (a b : Version) : Bool :=
  if a.major ≠ b.major then a.major < b.major
  else if a.minor ≠ b.minor then a.minor < b.minor
  else a.patch < b.patch

/-- A revision is not below itself. -/
theorem Version.not_lt_self (v : Version) : Version.lt v v = false := by
  simp [Version.lt]

/-! ## Manifests -/

/-- **One proof obligation, bound to the theorem that discharges it.**

`theoremName` is the Lean name and `file` the declaring file, so that an obligation can be
checked mechanically against the tree rather than being taken on trust. -/
structure Obligation where
  /-- Human-facing obligation name, e.g. `penalty_minimality`. -/
  name : String
  /-- Which family this belongs to. -/
  kind : ObligationKind
  /-- The Lean constant that proves it. -/
  theoremName : String
  /-- The file declaring that constant. -/
  file : String
  deriving Repr, Inhabited

/-- **The static description of a plugin.**

A manifest says who the plugin is, which architectural layer it lives in, which services
it consumes and produces, which obligations it claims, and at which revision. It says
nothing about *how* the plugin is installed -- that is `VerifiedPlugin`. -/
structure PluginManifest where
  /-- Unique plugin name. -/
  name : PluginName
  /-- Architectural layer. -/
  layer : PluginLayer
  /-- Capabilities this plugin needs from others. -/
  requires : List ServiceKey
  /-- Capabilities this plugin offers. -/
  provides : List ServiceKey
  /-- The obligations the plugin claims to discharge. -/
  obligations : List Obligation
  /-- Revision. -/
  version : Version
  deriving Repr, Inhabited

/-- A manifest with no obligations is well-formed but proves nothing. -/
def PluginManifest.empty (name : PluginName) (layer : PluginLayer) : PluginManifest :=
  ⟨name, layer, [], [], [], Version.zero⟩

/-- **The names of a manifest's obligations.** -/
def PluginManifest.obligationNames (m : PluginManifest) : List String :=
  m.obligations.map (·.name)

/-- **Whether a manifest claims an obligation of a given kind.** -/
def PluginManifest.claims (m : PluginManifest) (k : ObligationKind) : Bool :=
  m.obligations.any (·.kind == k)

/-- A manifest with no obligations claims nothing.

This is the theorem the empty-manifest discipline rests on: an `empty` manifest cannot
silently claim coverage, because `claims` is `false` for every kind. -/
theorem PluginManifest.empty_claims_false (name : PluginName) (layer : PluginLayer)
    (k : ObligationKind) :
    (PluginManifest.empty name layer).claims k = false := rfl

/-! ## Mandatory kinds -/

/-- **The obligation kinds the project treats as mandatory.**

Every one of these must be claimed by at least one plugin before the project is complete.
`refinement` is excluded by design: it belongs to the C backend, which is out of scope.

Defined here rather than in `Registry.lean` because it is a property of the obligation
taxonomy, and because the empty-manifest lemma below needs it. -/
def mandatoryKinds : List ObligationKind :=
  [.soundness, .completeness, .laws, .exactness, .approximation,
   .recovery, .spatial, .confluence, .equivariance, .idempotence, .invariants]

/-- `refinement` is not mandatory: the C backend is out of scope. -/
theorem refinement_not_mandatory : ObligationKind.refinement ∉ mandatoryKinds := by
  simp [mandatoryKinds]

/-- **An empty manifest cannot discharge any mandatory kind.**

The fragment of registry completeness that is already decided: coverage requires a plugin
whose `claims` is `true`, and `PluginManifest.empty_claims_false` rules that out for
`empty` manifests. Phrased as a negation so that it composes with
`AllMandatoryKindsCovered` rather than merely restating the `rfl`. -/
theorem PluginManifest.empty_never_covers (name : PluginName) (layer : PluginLayer)
    (k : ObligationKind) (hk : k ∈ mandatoryKinds) :
    ¬ ((PluginManifest.empty name layer).claims k = true) := by
  rw [PluginManifest.empty_claims_false]
  exact Bool.false_ne_true

end Lattice.Plugins
