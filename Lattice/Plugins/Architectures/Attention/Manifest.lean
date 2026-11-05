/-
# Architectures.Attention Plugin -- Manifest

The ATTENTION carrier (plan P1). It is the third of the architecture plugins, and it closes the
`equivariance` obligation `ARCHITECTURE-CARRIERS.md` listed for it while no such plugin existed.

## Why attention is an architecture carrier

**A domain plugin turns a CONSTRAINT into a loss or a token sequence.**
**An architecture carrier turns a SET OF KEYS into a pooled value** -- it is a *transformation of the
representation*, not a statement about what the representation means.

**=> the two are different layers, and `PluginLayer.architectures` is where the second lives.**

## What this plugin actually proves

**`softmax_row_stochastic`**: the softmax weights sum to `1` --
**the "行随机" obligation, and what makes the output a WEIGHTED AVERAGE.**

**`attention_masked_excludes`**: a masked-out index contributes nothing --
**the mask semantics, stated as an exact zero rather than an approximate one.**

**`attention_perm_equivariant`**: reordering the keys changes nothing --
**`attn_equivariant`, and the reason positional encodings are necessary.**

## What it does NOT claim

**No `idempotence`**: attention is not idempotent.
**No `confluence`**: pooling is not a rewriting system.

**No CAUSAL masking**: a causal mask is POSITION-DEPENDENT and breaks permutation equivariance BY DESIGN.
**=> proving `attention_perm_equivariant` and claiming causal support together would be a contradiction, so the
file proves the freely-masked case and states the boundary.**
-/

import Lattice.Plugins.Manifest

namespace Lattice.Plugins.Architectures.Attention

open Lattice.Plugins

/-- **The attention carrier's manifest.**

Layer `architectures`. It requires the point-cloud representation (`domain.points`) and offers the capability
`arch.attend`.
-/
def manifest : PluginManifest where
  name := "Architectures.Attention"
  version := ⟨1, 0, 0⟩
  layer := .architectures
  requires := ["domain.points"]
  provides := ["arch.attend"]
  obligations := [
    -- EQUIVARIANCE: permuting the keys changes nothing.
    { name := "attention_perm_equivariant"
      kind := .equivariance
      theoremName := "attention_perm_equivariant"
      file := "Lattice/Plugins/Architectures/Attention/Proofs.lean" },
    -- SOUNDNESS: the weights are row-stochastic.
    { name := "attention_row_stochastic"
      kind := .soundness
      theoremName := "softmax_row_stochastic"
      file := "Lattice/Plugins/Architectures/Attention/Proofs.lean" },
    -- EXACTNESS: a masked-out index contributes exactly zero.
    { name := "attention_mask_excludes"
      kind := .exactness
      theoremName := "attention_masked_excludes"
      file := "Lattice/Plugins/Architectures/Attention/Proofs.lean" }
  ]

/-- **The carrier claims three obligations, so its obligation list is not empty.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  simp [manifest]

end Lattice.Plugins.Architectures.Attention
