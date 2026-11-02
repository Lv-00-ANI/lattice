/-
# Domains.Constraints.Tokens Plugin -- Manifest

The third migrated plugin (P3-1). It is the **T1 Compile / T3 Extract** carrier for the
`Domains/Constraints` directory: constraints become token sequences, point clouds become flat
vectors, and both round trips are proved.

## Name: why `Tokens` and not `Constraints`

`Domains/Constraints/` already owns a plugin named `Domains.Constraints.Penalty`. A plugin
named `Domains.Constraints` would be the SIBLING of `Penalty` and also its superset, which
makes the ownership relation ambiguous. This plugin is the tokenisation + flattening part, so
it is named after that part.

## What this manifest records, and the one thing it must NOT claim

**Proved and claimed below**: the token encoding round-trips on both sides (`seqDecode_encode`,
`seqEncode_decode`), the flattening is a bijection (`flatten_injective`, `flatten_surjective`)
with an equality-form round trip, and the loss's non-injectivity is recorded with its sharpened
form (`no_loss_to_constraint_section`).

**NOT claimed, because it does not exist**: **`penalty_min_to_violation`** -- the plan's T2
obligation `IsLocalMin (loss p) x → violation p x ≤ g ε`.
**That `IsLocalMin` machinery lives in `Domains/Geometry`, not here**, and nothing in this
directory bridges a local minimum of the loss to a bound on the violation.
**A manifest that stayed silent on this would let a reader assume T2 was done.**

## Why `flatten_injective` and `penaltyLoss_not_injective` sit in the same plugin

They look contradictory and are not. **`flatten` is a bijection between a point CLOUD and a flat
vector, so it IS invertible. `penaltyLoss` collapses many point clouds onto one real number, so it
is NOT.** **Two different maps; together they are the reversibility boundary the reverse direction
has to live inside** -- the parameter layer round-trips, the semantic layer does not.
-/

import Lattice.Plugins.Manifest

namespace Lattice.Plugins.Domains.Constraints.Tokens

open Lattice.Plugins

/-- **The constraint-tokenisation plugin's manifest.**

Layer `domains`. It requires the penalty carrier (`penalty.loss`, provided by
`Domains.Constraints.Penalty`) because the loss lemmas it claims are the penalty's, and offers
constraint tokenisation plus the flattening bijection.
-/
def manifest : PluginManifest where
  name := "Domains.Constraints.Tokens"
  layer := .domains
  requires := ["penalty.loss"]
  provides := ["constraint.tokens", "constraint.flatten"]
  obligations := [
    -- T3 / flatten_injective: the point-cloud / flat-vector correspondence is injective.
    { name := "flatten_injective"
      kind := .exactness
      theoremName := "flatten_injective"
      file := "Lattice/Domains/Constraints/Flatten.lean" },
    -- T3 / the other half: every flat vector is realised by some point cloud.
    { name := "flatten_surjective"
      kind := .completeness
      theoremName := "flatten_surjective"
      file := "Lattice/Domains/Constraints/Flatten.lean" },
    -- The round trip stated as an equality rather than through the bijection lemmas.
    { name := "flatten_roundtrip"
      kind := .laws
      theoremName := "flattenRepresentation_roundtrip"
      file := "Lattice/Domains/Constraints/Flatten.lean" },
    -- T1 / the sequence representation round-trips on both sides.
    { name := "seq_decode_encode"
      kind := .laws
      theoremName := "seqDecode_encode"
      file := "Lattice/Domains/Constraints/SeqRepresentation.lean" },
    { name := "seq_encode_decode"
      kind := .laws
      theoremName := "seqEncode_decode"
      file := "Lattice/Domains/Constraints/SeqRepresentation.lean" },
    -- T3 / the NEGATIVE half of the reversibility boundary.
    { name := "penalty_loss_not_injective"
      kind := .soundness
      theoremName := "penaltyLoss_not_injective"
      file := "Lattice/Domains/Constraints/LossExtraction.lean" },
    -- The sharper statement: no section of the loss map exists.
    { name := "no_loss_to_constraint_section"
      kind := .soundness
      theoremName := "no_loss_to_constraint_section"
      file := "Lattice/Domains/Constraints/LossExtraction.lean" }
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims seven obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 7 := rfl

/-- The plugin lives in the `domains` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.domains := rfl

/-- It requires the penalty carrier's loss. -/
theorem manifest_requires : manifest.requires = ["penalty.loss"] := rfl

/-- It offers constraint tokenisation and the flattening bijection. -/
theorem manifest_provides :
    manifest.provides = ["constraint.tokens", "constraint.flatten"] := rfl

/-- It claims exactness -- the flattening injectivity. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- It claims laws -- the round trips. -/
theorem manifest_claims_laws : manifest.claims .laws = true := rfl

/-- It claims soundness -- the negative reversibility statements. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- It does NOT claim spatial composability. -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- It does NOT claim confluence. -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- It does NOT claim recovery. -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- It does NOT claim refinement. -/
theorem manifest_no_refinement : manifest.claims .refinement = false := rfl

end Lattice.Plugins.Domains.Constraints.Tokens
