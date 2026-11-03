/-
# Compose Plugin -- Manifest

The COMPOSITION algebra (P3-7). It is the plugin that closes the last three mandatory kinds:
`recovery`, `spatial`, `confluence`.

## Why those three cannot live in any single-carrier plugin

**`recovery`, `spatial` and `confluence` are all properties of how plugins COMBINE:**
- **`spatial`**: independent sub-computations do not interfere;
- **`confluence`**: the order of independent effects does not matter;
- **`recovery`**: an identity/unit exists, so a step can be undone by not composing it.

**A carrier plugin (`Norm`, `GNN`, `Penalty`) is a single map; it has nothing to be confluent WITH.**
**=> the kinds are structurally unavailable until the composition layer is migrated, which is why
they were the last three.**

## The three witnesses

**`spatial`**: `parallel_comm_run` -- running `f ∥ g` on `(a,b)` equals running `g ∥ f` on `(b,a)`
and swapping. **The two orders agree, which is exactly non-interference.**

**`confluence`**: `compose_run_assoc` -- associativity of composition at the level of `run`.
**Re-associating a three-way composition does not change the result, so the order in which a chain
is built is immaterial.**

**`recovery`**: `identity_compose_run` and `compose_identity_right` -- `identity` is a two-sided unit
for composition. **A unit is what makes "undo" meaningful: a step can be cancelled by not composing
it, and the composite is unchanged.** **That is the operational content of temporal recovery, and it
is the honest witness for the kind -- NOT a claim that every plugin has an inverse, which the
project has already REFUTED (`no_extractor_preserves_both`).**

## What this manifest deliberately does NOT claim

**No `exactness`**: composition is not approximating anything.
**No `approximation`**: `compose_strength` and `compose_coverage` are exact equalities, not bounds.
-/

import Lattice.Plugins.Manifest

namespace Lattice.Plugins.Compose

open Lattice.Plugins

/-- **The composition-algebra plugin's manifest.**

Layer `compose`. It requires `core.primitive` (the `Primitive` structure it composes) and offers
`compose.binary` and `compose.parallel`.
-/
def manifest : PluginManifest where
  name := "Compose"
  layer := .compose
  requires := ["core.primitive"]
  provides := ["compose.binary", "compose.parallel"]
  obligations := [
    -- SPATIAL: parallel composition commutes (the orders do not interfere).
    { name := "parallel_comm"
      kind := .spatial
      theoremName := "parallel_comm_run"
      file := "Lattice/Compose/Laws.lean" },
    -- CONFLUENCE: composition is associative at the level of `run`.
    { name := "compose_assoc"
      kind := .confluence
      theoremName := "compose_run_assoc"
      file := "Lattice/Compose/Combinators.lean" },
    -- RECOVERY: `identity` is a left unit, so a step can be cancelled by not composing it.
    { name := "identity_left_unit"
      kind := .recovery
      theoremName := "identity_compose_run"
      file := "Lattice/Compose/Combinators.lean" },
    -- RECOVERY: and a right unit.
    { name := "identity_right_unit"
      kind := .recovery
      theoremName := "compose_identity_right"
      file := "Lattice/Compose/Laws.lean" },
    -- LAWS: sequential composition is sound -- the composite preserves the postcondition.
    { name := "compose_sound"
      kind := .soundness
      theoremName := "compose_sound"
      file := "Lattice/Compose/Combinators.lean" },
    -- LAWS: the composite's strength is the minimum of the parts.
    { name := "compose_strength"
      kind := .laws
      theoremName := "compose_strength"
      file := "Lattice/Compose/Combinators.lean" },
    -- LAWS: the composite's coverage is the intersection of the parts.
    { name := "compose_coverage"
      kind := .laws
      theoremName := "compose_coverage"
      file := "Lattice/Compose/Combinators.lean" },
    -- LAW: parallel composition is well defined on pairs.
    { name := "parallel_run"
      kind := .laws
      theoremName := "parallel_run"
      file := "Lattice/Compose/Laws.lean" },
    -- LAW: parallel composition has a unit.
    { name := "parallel_identity"
      kind := .laws
      theoremName := "parallel_identity_run"
      file := "Lattice/Compose/Laws.lean" },
    -- SOUNDNESS: the composition hypothesis collapses when the second component's precondition is
    -- trivially true. (The library's counterexample for the general case is `private`, so it is
    -- not citable from a plugin; the positive statement is what can be cited.)
    { name := "compose_h_of_pre_true"
      kind := .soundness
      theoremName := "compose_h_of_pre_true"
      file := "Lattice/Compose/ComposeObligation.lean" }
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims ten obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 10 := rfl

/-- The plugin lives in the `compose` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.compose := rfl

/-- It requires the primitive structure. -/
theorem manifest_requires : manifest.requires = ["core.primitive"] := rfl

/-- It offers binary and parallel composition. -/
theorem manifest_provides : manifest.provides = ["compose.binary", "compose.parallel"] := rfl

/-- **It claims SPATIAL** -- parallel non-interference. -/
theorem manifest_claims_spatial : manifest.claims .spatial = true := rfl

/-- **It claims CONFLUENCE** -- associativity of composition. -/
theorem manifest_claims_confluence : manifest.claims .confluence = true := rfl

/-- **It claims RECOVERY** -- the identity is a two-sided unit. -/
theorem manifest_claims_recovery : manifest.claims .recovery = true := rfl

/-- It claims laws -- strength, coverage and parallel's unit. -/
theorem manifest_claims_laws : manifest.claims .laws = true := rfl

/-- It claims soundness -- composition preserves the postcondition. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- **It does NOT claim exactness**: composition approximates nothing. -/
theorem manifest_no_exactness : manifest.claims .exactness = false := rfl

/-- **It does NOT claim approximation**: `compose_strength` and `compose_coverage` are exact
equalities, not bounds. -/
theorem manifest_no_approximation : manifest.claims .approximation = false := rfl

/-- **It does NOT claim equivariance**: no group acts on composition. -/
theorem manifest_no_equivariance : manifest.claims .equivariance = false := rfl

/-- **It does NOT claim idempotence**: a composite is not re-applied to fix a point. -/
theorem manifest_no_idempotence : manifest.claims .idempotence = false := rfl

end Lattice.Plugins.Compose
