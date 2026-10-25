import Mathlib

/-!
# LATTICE: 量词约束统一 —— ∀ = 大 AND、∃ = 大 OR（非负损失类）

把组合子（andC/orC）推广到任意基数（量词维度）：

  ∀i, lᵢ = 0  ⟺  Σᵢ lᵢ = 0     （非负损失：全称 = 和为零）
  ∃i, lᵢ ≠ 0  ⟺  Σᵢ lᵢ > 0     （非负损失：存在违背 = 和为正）

抽象到**任意非负损失函数**（l : ι → ℝ，∀i 0 ≤ lᵢ）——比 sq/relu 特定版
更通用：平方损失、relu 输出、任意非负度量都是实例。

这是批量验证（∀ 约束）与违背检测（∃）的通用核心，模型无关。
-/

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 定理一：非负和为零 ⟺ 每项为零（∀ = 大 AND） -/

theorem sum_nonneg_zero_iff_all (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
    (∑ i, l i) = 0 ↔ ∀ i, l i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h i
      exact h i (Finset.mem_univ i)
    · intro h i hi
      exact h i
  · intro i hi
    exact hl i

/-! ## 定理二：非负和为正 ⟺ 存在非零项（∃ 违背检测 = 和为正） -/

theorem sum_pos_iff_exists (l : ι → ℝ) (hl : ∀ i, 0 ≤ l i) :
    0 < ∑ i, l i ↔ ∃ i, l i ≠ 0 := by
  constructor
  · intro h
    by_contra hnot
    -- 不存在非零 → 全零 → 和 = 0，矛盾
    have hall : ∀ i, l i = 0 := by
      intro i
      by_contra hz
      exact hnot ⟨i, hz⟩
    have hsum : ∑ i, l i = 0 := by
      rw [Finset.sum_eq_zero_iff_of_nonneg]
      · intro i hi
        exact hall i
      · intro i hi
        exact hl i
    linarith
  · intro h
    -- 存在非零（正）项 → 和 > 0
    rcases h with ⟨i, hi⟩
    have hpos : 0 < l i := lt_of_le_of_ne (hl i) (by
      intro hz
      exact hi hz.symm)
    have hle : l i ≤ ∑ j, l j := by
      exact Finset.single_le_sum (fun j hj => hl j) (Finset.mem_univ i)
    exact lt_of_lt_of_le hpos hle

/-! ## 实例：平方损失（∀ 约束验证）
∀i, outᵢ = 0 ⟺ Σ outᵢ² = 0（批量验证，平方损失非负）。 -/

theorem forall_constraint_verify (out : ι → ℝ) :
    (∀ i, out i = 0) ↔ (∑ i, (out i) ^ 2) = 0 := by
  rw [sum_nonneg_zero_iff_all (fun i => (out i) ^ 2) (fun i => sq_nonneg _)]
  constructor
  · intro h i
    exact sq_eq_zero_iff.mpr (h i)
  · intro h i
    exact sq_eq_zero_iff.mp (h i)

/-! ## 实例：平方损失（∃ 违背检测）
∃i, outᵢ ≠ 0 ⟺ Σ outᵢ² > 0（违背 ⟹ 损失严格正）。 -/

theorem exists_violation_positive (out : ι → ℝ) :
    (∃ i, out i ≠ 0) ↔ 0 < ∑ i, (out i) ^ 2 := by
  rw [sum_pos_iff_exists (fun i => (out i) ^ 2) (fun i => sq_nonneg _)]
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    exact ⟨i, by
      intro hz
      exact hi (sq_eq_zero_iff.mp hz)⟩
  · intro h
    rcases h with ⟨i, hi⟩
    exact ⟨i, by
      intro hz
      exact hi (by rw [hz]; norm_num)⟩

/-! ## 注：relu 批量验证的完整形式（衔接 sumRelu 的思路）
∀i, xᵢ ≤ 0 ⟺ Σ (relu xᵢ)² = 0——relu 输出非负，由 sum_nonneg_zero_iff_all
+ relu_eq_zero_iff 直接给出（sumRelu_all_constraints 已是具体版）。
量词抽象统一了它：非负损失类的通用结果。 -/

end Lattice
