/-
# Architectures.Conv Plugin -- the verified carrier

The three obligations of `Manifest.lean`, discharged by
`Lattice/Plugins/Architectures/Conv/Proofs.lean`.

## The three propositions

| proposition | content |
|:--|:--|
| **`ConvEquivarianceProp`** | **shifting the input shifts the output** |
| **`ConvWeightSharingProp`** | **every offset uses the same filter** |
| **`ConvWindowDeterminesOutputProp`** | **agreement on a window forces agreement on its output** |

**The first is the `equivariance` slot -- the one no plugin in this tree had filled with content before.**
**The other two are `soundness` and `exactness`, and they say what compilation must preserve.**

## What this plugin does NOT claim

**`idempotence` is `True`, because convolution is NOT idempotent.**
**`confluence` is `True`, because a single map is not a rewriting system.**

**=> the two slots that would be vacuous are marked `True` rather than given a proof of a weakened statement
that would look like a claim.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Architectures.Conv.Manifest
import Lattice.Plugins.Architectures.Conv.Proofs

namespace Lattice.Plugins.Architectures.Conv

open Lattice.Plugins

/-- **Equivariance: shifting the input shifts the output.** -/
def ConvEquivarianceProp : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (t : ℕ),
    (fun i => convApply k f (shift t x) i) = shift t (fun i => convApply k f x i)

/-- **`ConvEquivarianceProp` holds** -- by `conv_equivariant`. -/
theorem convEquivarianceProp_holds : ConvEquivarianceProp := by
  intro k f x t
  exact conv_equivariant k f x t

/-- **Weight sharing: every output offset uses the SAME filter.** -/
def ConvWeightSharingProp : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (i i' : ℕ),
    convApply k f x i = ∑ j : Fin k, f j * x (i + j)
      ∧ convApply k f x i' = ∑ j : Fin k, f j * x (i' + j)

/-- **`ConvWeightSharingProp` holds** -- by `conv_eq_shared_filter`. -/
theorem convWeightSharingProp_holds : ConvWeightSharingProp := by
  intro k f x i i'
  exact conv_eq_shared_filter k f x i i'

/-- **The output is determined by the window.** -/
def ConvWindowDeterminesOutputProp : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℝ) (x y : ℕ → ℝ) (j₀ : ℕ),
    (∀ j : Fin k, x (j₀ + j) = y (j₀ + j)) → convApply k f x j₀ = convApply k f y j₀

/-- **`ConvWindowDeterminesOutputProp` holds** -- by `conv_window_determines_output`. -/
theorem convWindowDeterminesOutputProp_holds : ConvWindowDeterminesOutputProp := by
  intro k f x y j₀ h
  exact conv_window_determines_output k f x y 0 j₀ h

/-- **The convolution carrier's proof bundle.**

**`equivariance` is the slot filled here -- the first non-`True` equivariance in an architecture plugin.**
-/
def proof : PluginProof where
  soundness := ConvWeightSharingProp
  laws := True
  exactness := ConvWindowDeterminesOutputProp
  approximation := True
  recovery := True
  spatial := True
  confluence := True
  equivariance := ConvEquivarianceProp
  idempotence := True
  invariants := True
  completeness := True
  refinement := True

/-- **Every claimed obligation of the convolution carrier is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨convWeightSharingProp_holds,
         True.intro,
         convWindowDeterminesOutputProp_holds,
         True.intro, True.intro, True.intro, True.intro,
         convEquivarianceProp_holds,
         True.intro, True.intro, True.intro, True.intro⟩

/-- **The verified convolution carrier.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The carrier claims three obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 3 := rfl

end Lattice.Plugins.Architectures.Conv
