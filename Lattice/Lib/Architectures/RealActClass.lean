import Mathlib
import Lattice.Lift.RealNonlinear
/-!
# LATTICE: 软掩码激活类 —— 激活族抽象的模型无关范式

transformer 调研的 FFN 激活类抽象：
ReLU 是硬掩码（s ∈ {0,1}），GELU/SwiGLU 是软掩码（s ∈ [0,1]）——统一为：

  软掩码激活类 SoftMasked：f(x) = s(x)·x，s 有界 [0,1]

  · ReLU：s(x) = 1{x>0}（硬掩码，s ∈ {0,1}）
  · GELU-tanh：s(x) = 0.5(1+tanh(√(2/π)(x+0.044715x³)))（tanh 界 → s ∈ [0,1]）

FFN 的有效线性映射对整类成立：
  Σᵢ Wᵢ·f(hᵢ) = Σᵢ (Wᵢ·sᵢ)·hᵢ   （有效线性系数 Wᵢ·sᵢ，软掩码版）

模型无关：证明对类（SoftMasked）成立，relu/gelu 只是实例。
-/


namespace Lattice.Lib.Architectures.RealActClass

-- relu 等声明来自 RealNonlinear（同在 Lattice 命名空间），无需 open。

/-! ## 软掩码激活类 -/

def SoftMasked (f s : ℝ → ℝ) : Prop :=
  (∀ x, f x = s x * x) ∧ (∀ x, 0 ≤ s x) ∧ (∀ x, s x ≤ 1)

/-! ## ReLU 的软掩码实例（硬掩码） -/

-- `0 < x` 的判定依赖 `Real.decidableLT`（无执行代码），故标记 noncomputable。
noncomputable def reluSoftMask (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-! ## 引理：ReLU 的软掩码分解 relu x = s(x)·x -/

lemma relu_mask_decomposition (x : ℝ) : relu x = reluSoftMask x * x := by
  by_cases h : 0 < x
  · rw [reluSoftMask, if_pos h]
    unfold relu
    rw [max_eq_left (le_of_lt h)]
    ring
  · rw [reluSoftMask, if_neg h]
    unfold relu
    rw [max_eq_right (le_of_not_gt h)]
    ring

/-! ## 定理一：ReLU 是软掩码激活
relu x = s_relu(x)·x 且 s_relu ∈ {0,1} ⊂ [0,1]。-/

theorem relu_is_soft_masked : SoftMasked relu reluSoftMask := by
  constructor
  · -- 分解：relu x = s·x（复用 relu_mask_decomposition）
    intro x
    exact relu_mask_decomposition x
  · constructor
    · -- 非负
      intro x
      by_cases h : 0 < x
      · simp [reluSoftMask, h]
      · simp [reluSoftMask, h]
    · -- ≤ 1
      intro x
      by_cases h : 0 < x
      · simp [reluSoftMask, h]
      · simp [reluSoftMask, h]

/-! ## GELU-tanh 的软掩码实例 -/

noncomputable def geluSoftMask (x : ℝ) : ℝ :=
  0.5 * (1 + Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3)))

/-- GELU（tanh 近似）：`x · geluSoftMask x`。

【历史沿革，已否证，不得作为当前事实引用】

本节原称 `Lattice.geluTanh` 在本文件与 `RealExtractInvertibility.lean` 各定义一次，
同时 import 会报 `environment already contains 'Lattice.geluTanh'`；并称
`Lattice.sigmoid` 在 `RealSwiGLU` 与 `RealExtractInvertibility` 各定义一次。

该两条冲突经 C-16 复核**均不成立**，证据见 `RealNonlinearFidelity.lean:12-26`：

* 全库 `def sigmoid` 仅 `RealSwiGLU.lean` 一处；`RealExtractInvertibility.lean` 定义的是
  `extractSigmoid`（`:138`），名字不同，不构成冲突。
* `RealExtractInvertibility.lean` 没有 `def geluTanh`，它定义的是 `extractGeluTanh`（`:164`）；
  而本文件的 `geluTanh` 在**本行下方第 82 行**（原注释所写 `:74`、`RealSwiGLU:23`、
  `RealExtractInvertibility:122`、`:148` 均为漂移或错误行号）。三者名字互不相同。

⇒ 不存在导入拓扑硬冲突。本文件不 import `RealExtractInvertibility` 仍是有效的工程决定，
但理由不再是硬冲突，而是沿 `RealActComplete` 侧选型（见 `RealNonlinearFidelity.lean:24-30`）。

保留本节的目的，与 `RealNonlinearFidelity.lean:24` 相同：防止后续会话照旧文档重复立项
「符号层同名冲突」。 -/
noncomputable def geluTanh (x : ℝ) : ℝ :=
  x * geluSoftMask x

/-! ## 引理：tanh 绝对值 ≤ 1
mathlib 4.14 无现成 `Real.abs_tanh_le_one`，用 tanh = sinh/cosh、cosh > 0 与
cosh² − sinh² = 1 证明：|sinh| ≤ cosh ⟹ |tanh| ≤ 1。-/

lemma tanh_abs_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  rw [abs_div, abs_of_nonneg (le_of_lt (Real.cosh_pos x))]
  have hle : |Real.sinh x| ≤ Real.cosh x := by
    have hsq : Real.sinh x ^ 2 ≤ Real.cosh x ^ 2 := by
      rw [Real.cosh_sq]
      nlinarith
    simpa [abs_of_nonneg (le_of_lt (Real.cosh_pos x))] using (sq_le_sq.mp hsq)
  exact (div_le_one (Real.cosh_pos x)).2 hle

/-! ## 定理二：GELU 软掩码有界 [0,1]
s_gelu ∈ [0,1]（tanh ∈ [-1,1] → 0.5(1+tanh) ∈ [0,1]）。-/

theorem gelu_soft_mask_bounds : ∀ x, 0 ≤ geluSoftMask x ∧ geluSoftMask x ≤ 1 := by
  intro x
  unfold geluSoftMask
  have ht : |Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3))| ≤ 1 :=
    tanh_abs_le_one _
  -- |t| ≤ 1 → -1 ≤ t ≤ 1（abs_le 分解）
  have hlo : -1 ≤ Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3)) :=
    (abs_le.mp ht).1
  have hhi : Real.tanh (Real.sqrt (2 / Real.pi) * (x + 0.044715 * x ^ 3)) ≤ 1 :=
    (abs_le.mp ht).2
  constructor
  · -- 0 ≤ 0.5(1+t)：t ≥ -1
    nlinarith
  · -- 0.5(1+t) ≤ 1：t ≤ 1
    nlinarith

/-! ## 定理三：GELU-tanh 是软掩码激活 -/

theorem gelu_is_soft_masked : SoftMasked geluTanh geluSoftMask := by
  constructor
  · -- 分解：gelu(x) = s(x)·x（定义，需交换乘序）
    intro x
    unfold geluTanh
    ring
  · -- 有界（定理二）
    constructor
    · intro x; exact (gelu_soft_mask_bounds x).1
    · intro x; exact (gelu_soft_mask_bounds x).2

/-! ## 定理四：软掩码 FFN 有效线性映射（对类成立）
对任意软掩码激活 f（f(hᵢ) = sᵢ·hᵢ）：
Σ Wᵢ·f(hᵢ) = Σ (Wᵢ·sᵢ)·hᵢ（有效线性系数，模型无关）。-/

theorem softMask_FFN_effective {ι : Type*} [Fintype ι] (f : ℝ → ℝ)
    (W h s : ι → ℝ) (hsm : ∀ i, f (h i) = s i * h i) :
    ∑ i, W i * f (h i) = ∑ i, (W i * s i) * h i := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsm i]
  ring

/-! ## 定理五：ReLU 实例化（衔接 RealFFN）
用软掩码类统一 ReLU：FFN_relu 的有效线性系数 = Wᵢ·1{hᵢ>0}。 -/

theorem relu_FFN_effective_via_class {ι : Type*} [Fintype ι] (W h : ι → ℝ) :
    ∑ i, W i * relu (h i) = ∑ i, (W i * reluSoftMask (h i)) * h i := by
  apply Finset.sum_congr rfl
  intro i hi
  -- relu(hᵢ) = s(hᵢ)·hᵢ（relu 是软掩码实例的分解）
  have hdec : relu (h i) = reluSoftMask (h i) * h i := relu_is_soft_masked.1 (h i)
  rw [hdec]
  ring

end Lattice.Lib.Architectures.RealActClass
