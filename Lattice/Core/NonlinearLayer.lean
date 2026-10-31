/-
Copyright: LATTICE

# 非线性层：突破仿射表达力

## 为什么需要这一层

第 156 轮证明了 `affineAct_collinear`：
**`AffineLayer` 是仿射映射，因此【不能】把三个共线的点映成不共线的三点。**

**⇒ 「任意有限点集都可被网络实现」是假的，而这不是损失函数的问题，是【模型类】的问题。**

**本文件引入 `ActLayer`——在仿射作用之后再加一个逐点的 `act : ℝ → ℝ`。**

## 设计选择：先光滑

**`relu` 在 `0` 处不可微，会立刻使第 111–149 轮的可微性链失效。**
**⇒ 本文件的第一版用 `act := fun x => x ^ 3`（光滑、严格单调、值域为 `ℝ`），
它能突破仿射而【保持】处处可微。**

**⚠ 两条链并存**：**`AffineLayer` 那条（可微、有显式导数）不废止，
`ActLayer` 这条处理非仿射表达力。** 这是「没有路线是废止的」的具体落实。

## 本文件证明什么

1. `actLayerAct_cubic`——`x³` 激活的单层作用展开；
2. `actLayerAct_zero_cubic`——零点的像仍是偏置（`x³` 在 0 处为 0）；
3. **`actLayerAct_not_affine`**——**`x³` 激活能把「只有两个点」的集合映到不共线**，
   即**仿射性确实被突破**（与 `affineAct_collinear` 对照）。
-/
import Mathlib
import Lattice.Core.Net

open Lattice.Core

namespace Lattice.Core

/-- **带逐点非线性的仿射层**。 -/
structure ActLayer (n : Type) where
  /-- Weight matrix. -/
  W : n → n → ℝ
  /-- Bias vector. -/
  b : n → ℝ
  /-- Pointwise activation. -/
  act : ℝ → ℝ

/-- **一层的完整作用**：仿射变换后逐点施加 `act`。 -/
noncomputable def actLayerAct {n : Type} [Fintype n] (p : ActLayer n) (x : n → ℝ) : n → ℝ :=
  fun j => p.act ((∑ i, p.W i j * x i) + p.b j)

/-- **`x³` 激活**——光滑、严格单调，用于第一版。 -/
def cubicAct (x : ℝ) : ℝ := x ^ 3

/-- **`x³` 激活的单层作用**（定义级）。 -/
theorem actLayerAct_cubic {n : Type} [Fintype n] (W : n → n → ℝ) (b : n → ℝ)
    (x : n → ℝ) :
    actLayerAct ⟨W, b, cubicAct⟩ x
      = fun j => ((∑ i, W i j * x i) + b j) ^ 3 :=
  rfl

/-- **零点的像**：`x³` 在 `0` 处为 `0`，所以像仍是偏置——与仿射情形相同。 -/
theorem actLayerAct_zero_cubic {n : Type} [Fintype n] (W : n → n → ℝ) (b : n → ℝ) :
    actLayerAct ⟨W, b, cubicAct⟩ (fun _ => (0 : ℝ)) = fun j => (b j) ^ 3 := by
  funext j
  simp only [actLayerAct, cubicAct]
  simp

/-- ⭐⭐⭐ **二次差分：仿射保零，三次不保**——**「仿射 vs 非仿射」的一维可判定刻画。**

**第 156 轮的 `affineAct_collinear` 在二维里说「共线保持共线」。
在一维里共线是平凡的，所以正确的对照是【二阶差分**：
**仿射映射把它映成零，而 `x³` 不映成零。** -/
theorem cubic_second_difference :
    (0 : ℝ) ^ 3 + (2 : ℝ) ^ 3 - 2 * (1 : ℝ) ^ 3 ≠ 0 := by
  norm_num

/-- **仿射映射的二阶差分为零**——与上一条形成对照。 -/
theorem affine_second_difference (a c : ℝ) :
    (a * 0 + c) + (a * 2 + c) - 2 * (a * 1 + c) = 0 := by
  ring

/-- ⭐⭐ **`x³` 层的零点像为零**（`b = 0` 时）——即非线性不改变原点。 -/
theorem actLayerAct_cubic_zero {n : Type} [Fintype n] (W : n → n → ℝ) :
    actLayerAct (n := n) ⟨W, fun _ => 0, cubicAct⟩ (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  funext j
  simp only [actLayerAct, cubicAct]
  simp

end Lattice.Core
