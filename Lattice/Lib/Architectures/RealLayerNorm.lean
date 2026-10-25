import Mathlib

/-!
# LATTICE: LayerNorm 尺度不变性（归一化族核心，模型无关）

transformer 调研（research/real-world/transformer-semantics.md）的 LayerNorm 性质：
中心化-归一化的**尺度不变性**——对任意输入 x 与任意缩放 α > 0：

  LN(α·x) = LN(x)

（中心化是线性的：center(αx) = α·center x；方差缩放 α²；
归一化比值中 α 消去——normalization 对输入缩放不敏感。）

模型无关：任意维度（ι 任意有限指标）、任意向量值。γ/β 仿射项与
ε 实现变体的推广见注释。这是「缩放-平移规范化族」的一个实例。
-/

noncomputable section

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 中心化（减去均值） -/

def mean (x : ι → ℝ) : ℝ :=
  (∑ i, x i) / (Fintype.card ι : ℝ)

def center (x : ι → ℝ) : ι → ℝ :=
  fun i => x i - mean x

/-! ## 引理：均值线性（缩放）
mean(α·x) = α·mean(x)。-/

lemma mean_scale (x : ι → ℝ) (α : ℝ) :
    mean (fun i => α * x i) = α * mean x := by
  unfold mean
  calc
    (∑ i, α * x i) / (Fintype.card ι : ℝ) = (α * ∑ i, x i) / (Fintype.card ι : ℝ) := by
      rw [Finset.mul_sum]
    _ = α * ((∑ i, x i) / (Fintype.card ι : ℝ)) := by
      ring

/-! ## 引理：中心化线性（缩放）
center(α·x) = α·center(x)。-/

lemma center_scale (x : ι → ℝ) (α : ℝ) :
    center (fun i => α * x i) = fun i => α * center x i := by
  funext i
  unfold center
  calc
    α * x i - mean (fun j => α * x j) = α * x i - α * mean x := by rw [mean_scale x α]
    _ = α * (x i - mean x) := by ring

/-! ## 中心平方和 -/

def centerSq (x : ι → ℝ) : ℝ :=
  ∑ i, (center x i) ^ 2

/-! ## 引理：中心平方和的缩放
centerSq(α·x) = α²·centerSq(x)。-/

lemma centerSq_scale (x : ι → ℝ) (α : ℝ) :
    centerSq (fun i => α * x i) = α ^ 2 * centerSq x := by
  unfold centerSq
  have hc : center (fun j => α * x j) = fun i => α * center x i := center_scale x α
  calc
    (∑ i, (center (fun j => α * x j) i) ^ 2) = ∑ i, (α * center x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc]
    _ = α ^ 2 * ∑ i, (center x i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-! ## 归一化（中心化 + 单位化） -/

def normalize (x : ι → ℝ) : ι → ℝ :=
  fun i => center x i / Real.sqrt (centerSq x)

/-! ## 定理：LayerNorm 尺度不变性（核心）
α > 0 ⟹ normalize(α·x) = normalize(x)（归一化对输入缩放不敏感）。-/

theorem normalize_scale_invariant (x : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    normalize (fun i => α * x i) = normalize x := by
  funext i
  unfold normalize
  -- 分子：α·cᵢ
  have hnum : center (fun j => α * x j) i = α * center x i := by
    exact congrFun (center_scale x α) i
  -- 分母：sqrt(α²·s) = α·sqrt(s)
  have hden : Real.sqrt (centerSq (fun j => α * x j)) = α * Real.sqrt (centerSq x) := by
    rw [centerSq_scale x α]
    have hαsq : 0 ≤ α ^ 2 := sq_nonneg α
    rw [Real.sqrt_mul hαsq (centerSq x)]
    have hsqrt : Real.sqrt (α ^ 2) = α := by
      rw [Real.sqrt_sq_eq_abs α]
      exact abs_of_nonneg (le_of_lt hα)
    rw [hsqrt]
  -- 比值：α·c / (α·√s) = c / √s（分 √s = 0 情形，field_simp 需要 √s ≠ 0）
  rw [hnum, hden]
  by_cases hs : Real.sqrt (centerSq x) = 0
  · simp [hs]
  · field_simp [ne_of_gt hα, hs]
    ring

/-! ## 推论：中心平方和恒正（归一化良定，x 非常数时）
centerSq(x) > 0 当 x 非常数（存在非零中心分量）。-/

theorem centerSq_pos_of_nonconstant (x : ι → ℝ) (i : ι) (h : center x i ≠ 0) :
    0 < centerSq x := by
  unfold centerSq
  have hsq : 0 < (center x i) ^ 2 := sq_pos_of_ne_zero h
  -- 单项 ≤ 总和（其余非负）
  have hle : (center x i) ^ 2 ≤ ∑ j, (center x j) ^ 2 := by
    -- single_le_sum（其余项非负）
    exact Finset.single_le_sum (fun j hj => sq_nonneg (center x j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le hsq hle

/-! ## 注：γ/β 仿射与 ε 变体的推广
本文件证明无 γ/β 的核心归一化。带仿射的完整 LayerNorm
  LN(x) = γ·normalize(x) + β
对固定 γ/β 是 normalize 的仿射变换（尺度不变性保持，仿射项不变）；
ε 实现版（分母加 ε）的精确缩放不变不成立（小 ε 时近似），
对标 transformer 调研的标注。 -/

end Lattice
