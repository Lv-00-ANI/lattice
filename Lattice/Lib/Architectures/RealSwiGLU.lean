import Mathlib
import Lattice.Lib.Architectures.RealActClass
/-!
# LATTICE: SwiGLU 门控 —— 软掩码类的真实激活实例

激活类抽象（RealActClass 的 SoftMasked）覆盖真实模型：
SwiGLU（LLaMA 系 FFN 门控）f(x) = x·σ(x)，σ = sigmoid ∈ (0,1)——

  · sigmoid 有界：0 < σ(x) < 1（exp_pos）；
  · SwiGLU 是 SoftMasked 实例：swiglu x = σ(x)·x，s = σ ∈ [0,1]；
  · 于是软掩码 FFN 有效线性（softMask_FFN_effective）对 SwiGLU 成立。

模型无关：任何 sigmoid 门控 FFN 都是 SoftMasked 成员。
-/


open Lattice.Lib.Architectures.RealActClass

namespace Lattice

/-! ## sigmoid -/

/-- Sigmoid：`1/(1+e^{−x})`。

⚠ **平行定义提示 —— ⭐ C-16 复核：本条已失效（见下）。**

原文（v14，S9 发现）声称 `Lattice.sigmoid` **在本文件与 `RealExtractInvertibility.lean:122`**
各定义一次、同时 import 会冲突。**该指控已不成立**：

* `RealExtractInvertibility.lean` 里**没有** `def sigmoid` —— 它定义的是
  `extractSigmoid`（**`:138`**，非原文的 `:122`）与 `extractGeluTanh`（**`:164`**，非原文的 `:148`）；
* 全库 `def sigmoid` 现在**只有本文件 `:31` 一处** ⟹ 不存在同名冲突。

⇒ ⭐ **保留本条是为了防止有人照旧文档重复「sigmoid 冲突」立项**；
历史经过见 `CORRECTIONS.md`。⚠ **同族的 `geluTanh` 平行定义仍需各自核对**
（本条不再对 `RealActClass:74` / `RealExtractInvertibility` 的 `geluTanh` 作任何断言）。 -/
-- 1/(1+e) 的域除法无执行代码，故标 noncomputable。
noncomputable def sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-! ## 定理一：sigmoid 有界（0,1）
0 < σ(x) < 1（exp_pos → 1+e > 1）。-/

theorem sigmoid_bounds : ∀ x : ℝ, 0 < sigmoid x ∧ sigmoid x < 1 := by
  intro x
  unfold sigmoid
  have hpos : 0 < Real.exp (-x) := Real.exp_pos _
  constructor
  · -- 0 < 1/(1+e)
    exact div_pos zero_lt_one (by linarith)
  · -- 1/(1+e) < 1 ⟺ 1 < 1+e（分母正）
    have h1 : 1 < 1 + Real.exp (-x) := by linarith
    have hden : 0 < 1 + Real.exp (-x) := by linarith
    -- 1/(1+e) < 1：分子 1 < 分母
    exact (div_lt_one hden).mpr h1

/-! ## SwiGLU 门控 -/

noncomputable def swiglu (x : ℝ) : ℝ := x * sigmoid x

/-! ## 定理二：SwiGLU 是软掩码激活
swiglu x = σ(x)·x，σ ∈ [0,1]（SoftMasked 实例）。-/

theorem swiglu_is_soft_masked : SoftMasked swiglu sigmoid := by
  constructor
  · -- 分解：swiglu x = σ(x)·x（定义）
    intro x
    unfold swiglu
    ring
  · constructor
    · -- σ ≥ 0
      intro x
      exact le_of_lt (sigmoid_bounds x).1
    · -- σ ≤ 1
      intro x
      exact le_of_lt (sigmoid_bounds x).2

/-! ## 推论：SwiGLU-FFN 有效线性映射（类实例化）
Σ Wᵢ·swiglu(hᵢ) = Σ (Wᵢ·σ(hᵢ))·hᵢ（软掩码 FFN 对 SwiGLU 成立）。-/

theorem swiglu_FFN_effective {ι : Type*} [Fintype ι] (W h : ι → ℝ) :
    ∑ i, W i * swiglu (h i) = ∑ i, (W i * sigmoid (h i)) * h i := by
  apply Finset.sum_congr rfl
  intro i hi
  unfold swiglu
  ring

end Lattice
