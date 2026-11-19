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

/-- **`laws` 槽位：卷积对输入是**线性**的（叠加 + 齐次）。** -/
def ConvLinearityProp : Prop :=
  (∀ (k : ℕ) (f : Fin k → ℝ) (x y : ℕ → ℝ) (i : ℕ),
      convApply k f (fun j => x j + y j) i = convApply k f x i + convApply k f y i) ∧
  (∀ (k : ℕ) (f : Fin k → ℝ) (c : ℝ) (x : ℕ → ℝ) (i : ℕ),
      convApply k f (fun j => c * x j) i = c * convApply k f x i)

/-- **`ConvLinearityProp` holds** -- by `convApply_add` and `convApply_smul`. -/
theorem convLinearityProp_holds : ConvLinearityProp := by
  constructor
  · intro k f x y i; exact convApply_add k f x y i
  · intro k f c x i; exact convApply_smul k f c x i

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

/-- **`ConvShiftComposeProp`（`recovery`）：两次平移等于一次求和的平移。**

**⇒ 卷积对平移是**等变**的（那是 `equivariance` 槽），而本条说的是另一件事：
平移本身作为一种时间操作是**可组合**的——先移 `s` 再移 `t`，等于一次移 `t + s`。
这是时间可组合性的最小非平凡实例。** -/
def ConvShiftComposeProp : Prop :=
  ∀ (t s : ℕ) (x : ℕ → ℝ), shift t (shift s x) = shift (t + s) x

/-- **`ConvShiftComposeProp` holds** — 展开 `shift` 后用 `Nat.add_assoc`。 -/
theorem convShiftComposeProp_holds : ConvShiftComposeProp := by
  intro t s x
  funext i
  show x (i + t + s) = x (i + (t + s))
  rw [Nat.add_assoc]

/-- **`ConvOneTapProp`（`refinement`）：单抽头卷积退化为逐点乘。**

**⇒ 抽头长度 1 时，`convApply` 的求和只剩一项，于是 `f 0 * x i`——
抽象的卷积在这个特例上与最素朴的逐点缩放一致。** -/
def ConvOneTapProp : Prop :=
  ∀ (f : Fin 1 → ℝ) (x : ℕ → ℝ) (i : ℕ), convApply 1 f x i = f 0 * x i

/-- **`ConvOneTapProp` holds** — 展开 `convApply`，用 `Fin.sum_univ_one`。 -/
theorem convOneTapProp_holds : ConvOneTapProp := by
  intro f x i
  show (∑ j : Fin 1, f j * x (i + j)) = f 0 * x i
  rw [Fin.sum_univ_one]
  simp

/-- **The convolution carrier's proof bundle.**

**`equivariance` is the slot filled here -- the first non-`True` equivariance in an architecture plugin.**
-/
def proof : PluginProof where
  soundness := ConvWeightSharingProp
  laws := ConvLinearityProp
  exactness := ConvWindowDeterminesOutputProp
  approximation := True
  recovery := ConvShiftComposeProp
  spatial := True
  confluence := True
  equivariance := ConvEquivarianceProp
  idempotence := True
  invariants := True
  completeness := True
  refinement := ConvOneTapProp

/-- **Every claimed obligation of the convolution carrier is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨convWeightSharingProp_holds,
         convLinearityProp_holds,
         convWindowDeterminesOutputProp_holds,
         True.intro, convShiftComposeProp_holds, True.intro, True.intro,
         convEquivarianceProp_holds,
         True.intro, True.intro, True.intro, convOneTapProp_holds⟩

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
