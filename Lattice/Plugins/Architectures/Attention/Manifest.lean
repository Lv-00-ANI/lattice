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
-- Round 767: the obligations now CARRY their propositions, and those propositions are the
-- theorems' own types -- so the manifest must import the file that proves them.
import Lattice.Plugins.Architectures.Attention.Proofs

namespace Lattice.Plugins.Architectures.Attention

open Lattice.Plugins

/-- **The equivariance obligation's proposition**: permuting keys and values changes nothing. -/
def attention_perm_equivariantProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] (s v : ι → ℝ) (σ : ι ≃ ι),
    attention (fun i => s (σ i)) (fun i => v (σ i)) = attention s v

/-- **The soundness obligation's proposition**: the softmax weights sum to one. -/
def attention_row_stochasticProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → ℝ),
    (Finset.univ.sum (fun i : ι => softmaxWeight s i)) = 1

/-- **The exactness obligation's proposition**: a masked-out index contributes zero. -/
def attention_mask_excludesProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (M : ι → Bool) (s v : ι → ℝ) (i : ι),
    M i = true → maskedWeight M s i * v i = 0

/-- **The three propositions are exactly the three theorems' types.**

**=> 这三条把 `Prop` 定义与已证定理接上：命题不是新写的，是定理自己的类型。
⇒ 若定理改名或改陈述，这几条会立刻失败 —— 这正是 `proof` 字段要保证的事。** -/
theorem attention_props_hold :
    attention_perm_equivariantProp ∧ attention_row_stochasticProp
      ∧ attention_mask_excludesProp :=
  ⟨attention_perm_equivariant, softmax_row_stochastic, attention_masked_excludes⟩

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
    -- **Round 767: the three obligations now go through `verifiedObligation`, so each CARRIES its
    -- proposition.** Before this round the manifest named a theorem as a `String`, and a manifest
    -- could name a theorem that did not exist without anything in the tree noticing.
    verifiedObligation "attention_perm_equivariant" .equivariance
      "Lattice/Plugins/Architectures/Attention/Proofs.lean"
      "attention_perm_equivariant" attention_perm_equivariantProp,
    -- SOUNDNESS: the weights are row-stochastic.
    verifiedObligation "attention_row_stochastic" .soundness
      "Lattice/Plugins/Architectures/Attention/Proofs.lean"
      "softmax_row_stochastic" attention_row_stochasticProp,
    -- EXACTNESS: a masked-out index contributes exactly zero.
    verifiedObligation "attention_mask_excludes" .exactness
      "Lattice/Plugins/Architectures/Attention/Proofs.lean"
      "attention_masked_excludes" attention_mask_excludesProp
  ]

/-- **The carrier claims three obligations, so its obligation list is not empty.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  simp [manifest]

end Lattice.Plugins.Architectures.Attention
