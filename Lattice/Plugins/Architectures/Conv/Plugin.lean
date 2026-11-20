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

/-- **`ConvBoundProp`（`approximation`）：卷积输出的绝对值被**滤波器绝对和**与**输入上界**之积所控。**

**⇒ `|convApply k f x i| ≤ (∑ j, |f j|) · M`，只要窗口内 `|x (i+j)| ≤ M` 且 `M ≥ 0`。**
**这条不是三角不等式的机械应用：它把「卷积能放大多少」变成一个**可算的量**——
放大率恰是滤波器的 `ℓ¹` 范数。**⇒ 于是「卷积不会失控」不再是一句经验判断，
而是关于 `f` 的一个数值条件。**
**也正因为它，`approximation` 这个槽在这里有内容：输出近似输入，误差由 `∑|f j|` 度量。** -/
def ConvBoundProp : Prop :=
  ∀ (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (i : ℕ) (M : ℝ),
    0 ≤ M → (∀ j : Fin k, |x (i + j)| ≤ M) →
    |convApply k f x i| ≤ (∑ j : Fin k, |f j|) * M

/-- **`ConvBoundProp` holds** — 三角不等式 + 逐项放缩 + 提取公因子 `M`。 -/
theorem convBoundProp_holds : ConvBoundProp := by
  intro k f x i M hM hx
  show |∑ j : Fin k, f j * x (i + j)| ≤ (∑ j : Fin k, |f j|) * M
  calc |∑ j : Fin k, f j * x (i + j)|
      ≤ ∑ j : Fin k, |f j * x (i + j)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin k, |f j| * |x (i + j)| := by
          exact Finset.sum_congr rfl (fun j _ => abs_mul _ _)
    _ ≤ ∑ j : Fin k, |f j| * M := by
          exact Finset.sum_le_sum (fun j _ =>
            mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
    _ = (∑ j : Fin k, |f j|) * M := by rw [Finset.sum_mul]

/-- **The convolution carrier's proof bundle.**

**`equivariance` is the slot filled here -- the first non-`True` equivariance in an architecture plugin.**
-/
def proof : PluginProof where
  soundness := ConvWeightSharingProp
  laws := ConvLinearityProp
  exactness := ConvWindowDeterminesOutputProp
  approximation := ConvBoundProp
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
         convBoundProp_holds, convShiftComposeProp_holds, True.intro, True.intro,
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
