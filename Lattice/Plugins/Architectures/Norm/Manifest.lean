/-
# Architectures.Norm Plugin -- Manifest

The NORMALISATION carrier (P6-3). It is the first of the four architecture plugins, and the one
that can close the `idempotence` gap in the registry's mandatory-kind coverage.

## Why normalisation is an architecture carrier and not a domain concern

**A domain plugin turns a CONSTRAINT into a loss or a token sequence.**
**An architecture carrier turns a POINT CLOUD into another point cloud of the same shape** --
it is a *transformation of the representation*, not a statement about what the representation
means.

**=> the two are different layers, and `PluginLayer.architectures` is where the second lives.**

## What this plugin actually proves

**`varOf_varNormalize_eq_one`**: normalising a non-degenerate vector gives variance exactly `1`.
**`varOf_varNormalize_le_one`**: for ANY vector (including the degenerate one) the normalised
variance is at most `1`.
**`varOf_iterate_varNormalize_le_one`**: iterating the normaliser ANY number of times keeps the
variance at most `1` -- **this is the idempotence obligation**, and it is stated as an iterated
bound rather than as `f ∘ f = f`, because normalisation is NOT literally idempotent once a scale
factor `gamma` is reintroduced; what IS idempotent is its effect on the variance.

**`bn_train_eq_infer`**: train-mode and inference-mode batch normalisation agree on the batch they
were computed from -- **the consistency statement that makes train/test behaviour comparable.**

**`varNormalize_unit_lipschitz_sharp`**: the unit-scale normaliser is Lipschitz with the SHARP
constant -- **the approximation obligation, with the constant not merely bounded but attained.**

## What it does NOT claim

**No `equivariance`**: `Lib/Architectures/RealGNNEquivariance.lean` holds the equivariance results,
and they belong to a different carrier (`GNN`, not `Norm`).
**No `confluence`**: normalisation is a single map, not a rewriting system.
-/

import Lattice.Plugins.Manifest

namespace Lattice.Plugins.Architectures.Norm

open Lattice.Plugins

/-- **The normalisation carrier's manifest.**

Layer `architectures`. It requires the point-cloud representation (`domain.points`) and offers the
capability `arch.normalize`.
-/
def manifest : PluginManifest where
  name := "Architectures.Norm"
  layer := .architectures
  requires := ["domain.points"]
  provides := ["arch.normalize"]
  obligations := [
    -- IDEMPOTENCE: iterating the normaliser keeps the variance bounded by 1.
    { name := "norm_iterate_variance_le_one"
      kind := .idempotence
      theoremName := "varOf_iterate_varNormalize_le_one"
      file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean" },
    -- EXACTNESS: on a non-degenerate input the normalised variance is exactly 1.
    { name := "norm_variance_eq_one"
      kind := .exactness
      theoremName := "varOf_varNormalize_eq_one"
      file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean" },
    -- SOUNDNESS: train-mode and inference-mode agree on the batch they were computed from.
    { name := "norm_train_infer_agree"
      kind := .soundness
      theoremName := "bn_train_eq_infer"
      file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean" },
    -- APPROXIMATION: the unit-scale normaliser is Lipschitz with the SHARP constant.
    { name := "norm_lipschitz_sharp"
      kind := .approximation
      theoremName := "varNormalize_unit_lipschitz_sharp"
      file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean" },
    -- APPROXIMATION: the same bound in its non-sharp (unconditional) form.
    { name := "norm_lipschitz"
      kind := .approximation
      theoremName := "varNormalize_unit_lipschitz"
      file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean" },
    -- SOUNDNESS: the variance is non-negative -- the normaliser is well defined.
    { name := "norm_variance_nonneg"
      kind := .soundness
      theoremName := "varOf_nonneg"
      file := "Lattice/Lib/Architectures/RealBatchNormConsistency.lean" }
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims six obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 6 := rfl

/-- The plugin lives in the `architectures` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.architectures := rfl

/-- It requires the point-cloud representation. -/
theorem manifest_requires : manifest.requires = ["domain.points"] := rfl

/-- It offers normalisation. -/
theorem manifest_provides : manifest.provides = ["arch.normalize"] := rfl

/-- **It claims IDEMPOTENCE** -- the obligation that no plugin before it could claim. -/
theorem manifest_claims_idempotence : manifest.claims .idempotence = true := rfl

/-- It claims exactness -- the variance-is-one statement. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- It claims approximation -- the Lipschitz bounds. -/
theorem manifest_claims_approximation : manifest.claims .approximation = true := rfl

/-- It claims soundness -- well-definedness and train/infer agreement. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- **It does NOT claim equivariance**: that belongs to the GNN carrier
(`Lib/Architectures/RealGNNEquivariance.lean`), not to normalisation. -/
theorem manifest_no_equivariance : manifest.claims .equivariance = false := rfl

/-- **It does NOT claim confluence**: normalisation is a single map, not a rewriting system. -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- **It does NOT claim recovery.** -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- **It does NOT claim spatial composability.** -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- **It does NOT claim laws**: the algebraic laws of composition are `Compose`'s business. -/
theorem manifest_no_laws : manifest.claims .laws = false := rfl

end Lattice.Plugins.Architectures.Norm
