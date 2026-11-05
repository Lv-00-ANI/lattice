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

namespace Lattice.Plugins.Architectures.Conv

open Lattice.Plugins

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
    -- EQUIVARIANCE: shifting the input shifts the output.
    { name := "conv_translation_equivariant"
      kind := .equivariance
      theoremName := "conv_translation_equivariant"
      file := "Lattice/Plugins/Architectures/Conv/Proofs.lean" },
    -- SOUNDNESS: every offset uses the same filter (weight sharing).
    { name := "conv_weight_sharing"
      kind := .soundness
      theoremName := "conv_eq_shared_filter"
      file := "Lattice/Plugins/Architectures/Conv/Proofs.lean" },
    -- EXACTNESS: the output is determined by the window.
    { name := "conv_window_determines_output"
      kind := .exactness
      theoremName := "conv_window_determines_output"
      file := "Lattice/Plugins/Architectures/Conv/Proofs.lean" }
  ]

/-- **The carrier claims three obligations, so its obligation list is not empty.**

**`manifest_nonempty` is what the registry's `NonVacuousFor` check consumes: a plugin that claimed NOTHING would
otherwise count as satisfying every obligation vacuously.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  simp [manifest]

end Lattice.Plugins.Architectures.Conv
