/-
# Architectures.Conv Plugin -- Manifest

The CONVOLUTION carrier (plan P1). It is the second of the architecture plugins, and it closes the
`equivariance` gap that `ARCHITECTURE-CARRIERS.md` had listed for it while no such plugin existed.

## Why convolution is an architecture carrier

**A domain plugin turns a CONSTRAINT into a loss or a token sequence.**
**An architecture carrier turns a SIGNAL into another signal of the same shape** -- it is a *transformation of
the representation*, not a statement about what the representation means.

**=> the two are different layers, and `PluginLayer.architectures` is where the second lives.**

## What this plugin actually proves

**`conv_translation_equivariant`**: applying the filter to a shifted input gives the shifted output --
**the `equivariance` obligation, stated as an identity.**

**`conv_eq_shared_filter`**: every output offset uses the SAME filter --
**weight sharing, stated as what the definition IS rather than as an extra hypothesis.**

**`conv_window_determines_output`**: two signals agreeing on a window agree on that window's output --
**the symbolic content compilation must preserve.**

**`conv_equivariant`**: the equivariance as a function equality.

## What it does NOT claim

**No `idempotence`**: convolution is not idempotent -- applying a filter twice is a different filter.
**No `confluence`**: a single map is not a rewriting system.
**No strided or multi-channel form**: a strided convolution is NOT equivariant under arbitrary shifts, so
claiming it here would be FALSE. **The unit-stride single-channel case is what is proved, and the boundary is
stated rather than discovered later.**
-/

import Lattice.Plugins.Manifest
-- Round 767: obligations carry their propositions, so the manifest imports the proofs.
import Lattice.Plugins.Architectures.Conv.Proofs

namespace Lattice.Plugins.Architectures.Conv

open Lattice.Plugins

/-- **Translation equivariance**: shifting the input shifts the output. -/
def conv_translation_equivariantProp : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (t i : ℕ),
    convApply k f (shift t x) i = convApply k f x (i + t)

/-- **Weight sharing**: every offset uses the same filter. -/
def conv_weight_sharingProp : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (i i' : ℕ),
    convApply k f x i = Finset.univ.sum (fun j : Fin k => f j * x (i + (j : ℕ)))
      ∧ convApply k f x i' = Finset.univ.sum (fun j : Fin k => f j * x (i' + (j : ℕ)))

/-- **Window determination**: the output is determined by its input window. -/
def conv_window_determines_outputProp : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℝ) (x y : ℕ → ℝ), ℕ → ∀ (j₀ : ℕ),
    (∀ (j : Fin k), x (j₀ + (j : ℕ)) = y (j₀ + (j : ℕ))) →
      convApply k f x j₀ = convApply k f y j₀

/-- **The three propositions are the three theorems' types.** -/
theorem conv_props_hold :
    conv_translation_equivariantProp ∧ conv_weight_sharingProp
      ∧ conv_window_determines_outputProp :=
  ⟨conv_translation_equivariant, conv_eq_shared_filter, conv_window_determines_output⟩

/-- **The convolution carrier's manifest.**

Layer `architectures`. It requires the point-cloud representation (`domain.points`) and offers the capability
`arch.convolve`.
-/
def manifest : PluginManifest where
  name := "Architectures.Conv"
  version := ⟨1, 0, 0⟩
  layer := .architectures
  requires := ["domain.points"]
  provides := ["arch.convolve"]
  obligations := [
    verifiedObligation "conv_translation_equivariant" .equivariance
      "Lattice/Plugins/Architectures/Conv/Proofs.lean"
      "conv_translation_equivariant" conv_translation_equivariantProp,
    verifiedObligation "conv_weight_sharing" .soundness
      "Lattice/Plugins/Architectures/Conv/Proofs.lean"
      "conv_eq_shared_filter" conv_weight_sharingProp,
    verifiedObligation "conv_window_determines_output" .exactness
      "Lattice/Plugins/Architectures/Conv/Proofs.lean"
      "conv_window_determines_output" conv_window_determines_outputProp
  ]

/-- **The carrier claims three obligations, so its obligation list is not empty.**

**`manifest_nonempty` is what the registry's `NonVacuousFor` check consumes: a plugin that claimed NOTHING would
otherwise count as satisfying every obligation vacuously.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  simp [manifest]

end Lattice.Plugins.Architectures.Conv
