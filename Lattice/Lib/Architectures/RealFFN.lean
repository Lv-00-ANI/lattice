import Mathlib
import Lattice.Runtime.RealNonlinear
/-!
# LATTICE: FFN 激活模式 → 有效线性映射（模型无关）

transformer 调研（research/real-world/transformer-semantics.md 目标 B）：
ReLU-FFN 的分片线性语义——

  relu(hᵢ) = 1{hᵢ > 0} · hᵢ   （对角掩码 × 输入）

给定激活模式（掩码向量 M 固定），FFN 输出是输入的**线性函数**：

  FFN_out(W, h) = Σᵢ Wᵢ·relu(hᵢ) = Σᵢ (Wᵢ·Mᵢ)·hᵢ   （有效线性映射）

这是提取方向落真实 FFN 的必经台阶：激活模式确定有效线性系数，
分片线性 = 精确语义（无近似）。模型无关：只依赖 relu 的掩码分解，
不依赖任何具体模型维度。

ReLU 是"零化函数类"（f(0)=0、分段线性零化）的实例；对类的推广见注释。
-/


namespace Lattice

/-! ## 引理：ReLU 的掩码分解
relu x = (if 0 < x then 1 else 0) · x。-/

lemma relu_mask_decomposition (x : ℝ) :
    relu x = (if 0 < x then 1 else 0) * x := by
  unfold relu
  by_cases h : 0 < x
  · -- x > 0：max x 0 = x
    have hmax : max x 0 = x := max_eq_left (le_of_lt h)
    rw [if_pos h, hmax]
    ring
  · -- x ≤ 0：max x 0 = 0
    have hle : x ≤ 0 := le_of_not_gt h
    have hmax : max x 0 = 0 := max_eq_right hle
    rw [if_neg h, hmax]
    ring

/-! ## 掩码向量与 relu 向量 -/

noncomputable def MaskVec (h : ι → ℝ) : ι → ℝ := fun i => if 0 < h i then 1 else 0

noncomputable def ReLUVec (h : ι → ℝ) : ι → ℝ := fun i => relu (h i)

/-! ## 定理一：逐元素掩码分解
relu(hᵢ) = Mᵢ·hᵢ（ReLUVec = MaskVec ⊙ h）。-/

theorem relu_vec_mask (h : ι → ℝ) :
    ∀ i, ReLUVec h i = MaskVec h i * h i := by
  intro i
  unfold ReLUVec MaskVec
  exact relu_mask_decomposition (h i)

/-! ## FFN 输出（单层，relu 激活） -/

noncomputable def FFNOut {ι : Type} [Fintype ι] (W : ι → ℝ) (h : ι → ℝ) : ℝ :=
  ∑ i, W i * ReLUVec h i

/-! ## 定理二：FFN 有效线性映射（核心）
给定输入 h（掩码模式确定），FFN 输出 = 有效线性系数 Wᵢ·Mᵢ 作用在 h 上
（分片线性的精确代数）。-/

theorem FFN_effective_linear {ι : Type} [Fintype ι] (W h : ι → ℝ) :
    FFNOut W h = ∑ i, (W i * MaskVec h i) * h i := by
  unfold FFNOut
  apply Finset.sum_congr rfl
  intro i hi
  rw [relu_vec_mask h i]
  ring

/-! ## 定理三：掩码固定时 FFN 是线性映射
若两个输入 h、h' 有相同激活模式（掩码相同），则 FFN 输出差是
有效系数作用在输入差上的线性函数（分段线性=每段线性）。-/

theorem FFN_linear_on_fixed_mask {ι : Type} [Fintype ι] (W h h' : ι → ℝ)
    (hmask : ∀ i, MaskVec h i = MaskVec h' i) :
    FFNOut W h - FFNOut W h' = ∑ i, (W i * MaskVec h i) * (h i - h' i) := by
  rw [FFN_effective_linear W h, FFN_effective_linear W h']
  -- 逐项差
  calc
    (∑ i, (W i * MaskVec h i) * h i) - (∑ i, (W i * MaskVec h' i) * h' i)
        = (∑ i, (W i * MaskVec h i) * h i) - (∑ i, (W i * MaskVec h i) * h' i) := by
          -- hmask 替换 h' 的掩码为 h 的
          apply congrArg (fun x => _ - x)
          apply Finset.sum_congr rfl
          intro i hi
          rw [hmask i]
    _ = ∑ i, (W i * MaskVec h i) * (h i - h' i) := by
      -- 减法进和
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-! ## 定理四：激活零化 ⟺ 掩码零（ReLU 零化语义，relu_preserves 的掩码形态）
relu(hᵢ) = 0 ⟺ Mᵢ = 0（掩码指示激活）。-/

theorem relu_zero_iff_mask_zero (x : ℝ) : relu x = 0 ↔ (if 0 < x then 1 else 0) = 0 := by
  rw [relu_eq_zero_iff]
  -- x ≤ 0 ⟺ (if 0 < x then 1 else 0) = 0
  by_cases h : 0 < x
  · -- x > 0：掩码 = 1 ≠ 0；x ≤ 0 不成立
    rw [if_pos h]
    constructor
    · intro hxle; linarith
    · intro h1; norm_num at h1
  · -- x ≤ 0：掩码 = 0；x ≤ 0 成立
    rw [if_neg h]
    constructor
    · intro _; rfl
    · intro _; exact le_of_not_gt h

end Lattice
