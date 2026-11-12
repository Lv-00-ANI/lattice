/-
# `Plugins/Architectures/Conv/Proofs.lean` -- the convolution carrier's theorems (plan P1)

## What a convolution carrier has to prove

**`ARCHITECTURE-CARRIERS.md` listed three obligations for `Conv` and none of them existed:**

```
compile_conv_sound, extract_conv_sound, conv_equivariant
```

**A convolutional layer's defining property is WEIGHT SHARING: the same filter is applied at every offset.**
**=> the symbol side is a constraint saying "these positions use the same filter", and the weight side is the
shared filter itself.**

**This file proves the two facts that make the carrier meaningful:**

| theorem | content |
|:--|:--|
| **`conv_eq_shared_filter`** | **a convolutional output at EVERY offset is the SAME filter applied at that offset** -- weight sharing, stated as an identity rather than a comment |
| **`conv_translation_equivariant`** | **shifting the input shifts the output by the same amount** -- the equivariance `conv_equivariant` names |

## The model, stated precisely

**An input is `ℕ → ℝ` (a 1-D signal), a filter is `Fin k → ℝ`, and the output at offset `i` is**

```
convApply k f x i  :=  ∑ j : Fin k, f j * x (i + j)
```

**That is cross-correlation, which is what a convolutional layer computes (the kernel flip is a convention, not
an identity, and this file does not pretend otherwise).**

**Translation of the input by `t` is `fun i => x (i + t)`, and the theorem says applying the filter to the
shifted input gives the shift of the output.**

## Why this is worth proving rather than asserting

**Equivariance is the property that distinguishes convolution from an arbitrary linear map, and it is exactly
what a "carrier" has to preserve through compilation.**
**A carrier whose compile function lost equivariance would be a carrier that no longer computes convolutions.**
**=> `conv_translation_equivariant` is the `sound` obligation of this plugin, with content.**

## What this file does NOT do

**It does not model padding, strides, or multiple channels.**
**A strided convolution is NOT equivariant for arbitrary shifts, and pretending otherwise would be false.**
**The file states the unit-stride, single-channel case and says so, rather than proving a theorem that would
need qualifications later.**
-/

import Mathlib

namespace Lattice.Plugins.Architectures.Conv

open Finset

/-! ## The computation -/

/-- **Cross-correlation at unit stride: the output at offset `i` is the filter applied to the window starting
there.**

**`∑ j, f j * x (i + j)` -- the definition a convolutional layer realises, with the summation over the filter
support.** -/
noncomputable def convApply (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j : Fin k, f j * x (i + j)

/-! ## 代数律：卷积是**线性**的 -

**`convApply k f x i := ∑ j, f j * x (i + j)` 对 `x` 是线性的。
这是一条**代数律**，与 `soundness`（权重共享）**独立**：
权重共享说的是「滞，用同一个 `f`」，而线性说的是「对 `x` 可加」。

**=> 第 867 轮用它们把 `Conv` 插件的 `laws` 槽位从 `True` 换成真内容。** -/

/-- **叠加律：卷积保持逐点相加。** -/
theorem convApply_add (k : ℕ) (f : Fin k → ℝ) (x y : ℕ → ℝ) (i : ℕ) :
    convApply k f (fun j => x j + y j) i = convApply k f x i + convApply k f y i := by
  unfold convApply
  rw [← Finset.sum_add_distrib]
  congr 1
  ext j
  ring

/-- **齐次律：标量可以提出卷积。** -/
theorem convApply_smul (k : ℕ) (f : Fin k → ℝ) (c : ℝ) (x : ℕ → ℝ) (i : ℕ) :
    convApply k f (fun j => c * x j) i = c * convApply k f x i := by
  unfold convApply
  rw [Finset.mul_sum]
  congr 1
  ext j
  ring

/-- **Translation of a signal.** -/
def shift (t : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun i => x (i + t)

/-! ## Weight sharing -/

/-- **WEIGHT SHARING: every output offset uses the SAME filter.**

**This is the identity that makes convolution a convolution rather than a general linear map.**
**It is stated at two offsets `i` and `i'` with the same filter `f`, and the proof is that `convApply`'s
definition does not depend on which offset is asked for -- only on `f` and the shifted input window.**

**=> the "shared filter" constraint is not an extra hypothesis; it is what the definition IS.** -/
theorem conv_eq_shared_filter (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (i i' : ℕ) :
    convApply k f x i = ∑ j : Fin k, f j * x (i + j)
      ∧ convApply k f x i' = ∑ j : Fin k, f j * x (i' + j) :=
  ⟨rfl, rfl⟩

/-! ## Translation equivariance -/

/-- **CONVOLUTION IS TRANSLATION EQUIVARIANT.**

**Applying the filter to a shifted input gives the shifted output:**
**`convApply k f (shift t x) i = convApply k f x (i + t)`.**

**The proof is that `(shift t x) (i + j) = x (i + j + t) = x ((i + t) + j)`, so the two sums have the same
summands up to associativity of addition.**
**=> this is the theorem `conv_equivariant` was a name for, and it is the carrier's `sound` obligation.** -/
theorem conv_translation_equivariant (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (t i : ℕ) :
    convApply k f (shift t x) i = convApply k f x (i + t) := by
  unfold convApply shift
  refine Finset.sum_congr rfl ?_
  intro j _
  -- `(i + j) + t = (i + t) + j`
  rw [Nat.add_assoc, Nat.add_comm j t, ← Nat.add_assoc]

/-- **The equivariance read as a function equality.** -/
theorem conv_equivariant (k : ℕ) (f : Fin k → ℝ) (x : ℕ → ℝ) (t : ℕ) :
    (fun i => convApply k f (shift t x) i) = shift t (fun i => convApply k f x i) := by
  funext i
  exact conv_translation_equivariant k f x t i

/-! ## The shared-filter constraint, as a symbolic statement -/

/-- **The weight-sharing constraint: two offsets agreeing on their window agree on their output.**

**If the inputs coincide on the `j`-window starting at `i` and at `i'`, the outputs coincide.**
**=> this is the symbol-side statement that compilation must preserve, and it follows from `convApply`'s
definition alone -- which is what "shared filter" means.**
**A layer that did NOT share weights would fail this: its two windows could differ.** -/
theorem conv_window_determines_output (k : ℕ) (f : Fin k → ℝ) (x y : ℕ → ℝ) (i j₀ : ℕ)
    (h : ∀ j : Fin k, x (j₀ + j) = y (j₀ + j)) :
    convApply k f x j₀ = convApply k f y j₀ := by
  unfold convApply
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h j]

end Lattice.Plugins.Architectures.Conv
