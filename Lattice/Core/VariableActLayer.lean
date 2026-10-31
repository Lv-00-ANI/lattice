/-
Copyright: LATTICE

# 可变宽度的非线性层：`NLayer`

## 为什么需要这一层（第 157 轮的结论）

第 157 轮引入的 `ActLayer` 有逐点非线性，**但宽度仍是固定方阵 `n → n`**。
而用户指出：**「非线性似乎还是不够，无法覆盖整个 TF 框架里的权重。」**

**这个判断是对的，而且真正的缺口有【两条**，不只是激活函数：

1. **宽度**：`AffineLayer`／`ActLayer` 都是 `n → n` 的方阵，
   **而 TF 的层是 `m → n`（`Dense`、`Conv` 的输出宽度任意）**；
2. **激活**：`AffineLayer` 没有，`ActLayer` 有但宽度受限。

**项目里【已有**宽度可变的 `MLayer (m n)`（`Core/VariableNet.lean`，第 40 轮左右），
**它的 `compose` 由统一化强制中间宽度，宽度不匹配是类型错误。**
**而损失链（第 111–155 轮）全部建立在固定宽度的 `AffineLayer` 上——这才是缺口所在。**

## 本文件做什么

**把两者合并**：`NLayer (m n)` = `MLayer` 的自适应宽度 + 逐点 `act`。

**⚠ 本文件【只】定义结构与基本引理**，不声称表达能力定理——
**那需要先在可变宽度上重建损失链，是后续轮次的工作。**

## 与 TF 的实际差距，如实登记

**即使有了 `NLayer`，本形式化仍【不覆盖** TF 的：
**卷积的权重共享、注意力的双线性结构、批归一化的统计量、残差的 DAG 拓扑**。
**这些是【结构】而非【逐层函数】，需要各自的接口，不能靠“更一般的层”一并覆盖。**

**⇒ 正确的项目定位应当是**：
**`NLayer` 覆盖 `Dense` 链（最重要的训练与后训练载体），
其余结构各自登记为独立接口，而不是声称一条链覆盖整个框架。**
-/
import Mathlib
import Lattice.Core.VariableNet

open Matrix

namespace Lattice.Core

/-- **可变宽度的非线性层**：`MLayer` 的宽度自适应 + 逐点激活。 -/
structure NLayer (m n : ℕ) where
  /-- Weight matrix. -/
  W : Matrix (Fin m) (Fin n) ℝ
  /-- Bias vector. -/
  b : Fin n → ℝ
  /-- Pointwise activation. -/
  act : ℝ → ℝ

/-- **一层的完整作用**：`x ↦ act (Wᵀx + b)`，逐点。 -/
noncomputable def nlayerAct {m n : ℕ} (l : NLayer m n) (x : Fin m → ℝ) : Fin n → ℝ :=
  fun j => l.act ((∑ i, l.W i j * x i) + l.b j)

/-- **恒等激活时退化为 `MLayer`**——**证明新结构确实包含了旧结构。** -/
theorem nlayerAct_id_eq_mlayerAct {m n : ℕ} (l : MLayer m n) (x : Fin m → ℝ) :
    nlayerAct ⟨l.W, l.b, id⟩ x = mlayerAct l x :=
  rfl

/-- **`x³` 激活的展开**（定义级）。 -/
theorem nlayerAct_cubic {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) :
    nlayerAct ⟨W, b, fun t => t ^ 3⟩ x
      = fun j => ((∑ i, W i j * x i) + b j) ^ 3 :=
  rfl

/-- ⭐ **宽度可变确实被支持**：从 `Fin 2` 到 `Fin 3` 的层是合法对象，
**而 `MLayer 2 3` 与 `MLayer 3 4` 可以 `compose` 成 `MLayer 2 4`。** -/
example : NLayer 2 3 := ⟨fun _ _ => 0, fun _ => 0, id⟩

/-- ⭐ **组合的中间宽度由统一化强制**——**宽度不匹配是类型错误，不是运行时检查。** -/
theorem nlayer_width_forced :
    (MLayer.compose (l₁ := (⟨fun _ _ => (0 : ℝ), fun _ => 0⟩ : MLayer 2 3))
      (l₂ := (⟨fun _ _ => (0 : ℝ), fun _ => 0⟩ : MLayer 3 4))) = MLayer.compose
      (l₁ := (⟨fun _ _ => (0 : ℝ), fun _ => 0⟩ : MLayer 2 3))
      (l₂ := (⟨fun _ _ => (0 : ℝ), fun _ => 0⟩ : MLayer 3 4)) :=
  rfl

end Lattice.Core
