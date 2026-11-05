/-
# Architectures.Attention Plugin -- the verified carrier

The three obligations of `Manifest.lean`, discharged by
`Lattice/Plugins/Architectures/Attention/Proofs.lean`.

## The three propositions

| proposition | content |
|:--|:--|
| **`AttentionPermEquivarianceProp`** | **permuting the keys changes nothing** |
| **`AttentionRowStochasticProp`** | **the softmax weights sum to `1`** |
| **`AttentionMaskExcludesProp`** | **a masked-out index contributes exactly zero** |

**The first is the `equivariance` slot, filled with content for the second time in the tree (after `Conv`).**
**The other two are `soundness` and `exactness`.**

## What this plugin does NOT claim

**`idempotence` and `confluence` are `True`, because attention is neither idempotent nor a rewriting system.**
**=> the slots that would be vacuous are marked `True` rather than given a weakened statement that would look
like a claim.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Architectures.Attention.Manifest
import Lattice.Plugins.Architectures.Attention.Proofs

namespace Lattice.Plugins.Architectures.Attention

open Lattice.Plugins

/-- **Equivariance: permuting the keys changes nothing.** -/
def AttentionPermEquivarianceProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] (s v : ι → ℝ) (σ : ι ≃ ι),
    attention (fun i => s (σ i)) (fun i => v (σ i)) = attention s v

/-- **`AttentionPermEquivarianceProp` holds** -- by `attention_perm_equivariant`. -/
theorem attentionPermEquivarianceProp_holds : AttentionPermEquivarianceProp := by
  intro ι _ _ s v σ
  exact attention_perm_equivariant s v σ

/-- **Soundness: the softmax weights sum to `1`.** -/
def AttentionRowStochasticProp : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → ℝ), ∑ i, softmaxWeight s i = 1

/-- **`AttentionRowStochasticProp` holds** -- by `softmax_row_stochastic`. -/
theorem attentionRowStochasticProp_holds : AttentionRowStochasticProp := by
  intro ι _ _ s
  exact softmax_row_stochastic s

/-- **Exactness: a masked-out index contributes exactly zero.** -/
def AttentionMaskExcludesProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (M : ι → Bool) (s v : ι → ℝ) (i : ι),
    M i = true → maskedWeight M s i * v i = 0

/-- **`AttentionMaskExcludesProp` holds** -- by `attention_masked_excludes`. -/
theorem attentionMaskExcludesProp_holds : AttentionMaskExcludesProp := by
  intro ι _ M s v i h
  exact attention_masked_excludes M s v i h

/-- **The attention carrier's proof bundle.**

**`equivariance` filled here -- the second non-`True` equivariance in the tree.** -/
def proof : PluginProof where
  soundness := AttentionRowStochasticProp
  laws := True
  exactness := AttentionMaskExcludesProp
  approximation := True
  recovery := True
  spatial := True
  confluence := True
  equivariance := AttentionPermEquivarianceProp
  idempotence := True
  invariants := True
  completeness := True
  refinement := True

/-- **Every claimed obligation of the attention carrier is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨attentionRowStochasticProp_holds,
         True.intro,
         attentionMaskExcludesProp_holds,
         True.intro, True.intro, True.intro, True.intro,
         attentionPermEquivarianceProp_holds,
         True.intro, True.intro, True.intro, True.intro⟩

/-- **The verified attention carrier.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The carrier claims three obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 3 := rfl

end Lattice.Plugins.Architectures.Attention
