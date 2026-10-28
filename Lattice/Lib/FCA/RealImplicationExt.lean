import Lattice.Runtime.RealNonlinear
import Lattice.Lib.FCA.RealImplication
import Mathlib

/-!
# LATTICE: 蕴含族可微损失（margin 版）—— soft 蕴含惩罚的完整语义

RealImplication（对齐蕴含）的 **margin 可微损失族**扩展：
蕴含 c₁ → c₂ 的可微惩罚

    penalty(x) = relu(out₂(x) − out₁(x))

（margin 型：前提输出为阈值，结论越界才惩罚）：

  1. 惩罚语义：前提满足（out₁ = 0）∧ 结论违背（out₂ > 0）
     ⟹ penalty > 0（该惩罚时必罚）；
  2. 零化语义：out₂ ≤ out₁ ⟹ penalty = 0（蕴含成立时零惩罚）；
  3. 传递性：relu 惩罚的蕴含关系传递（c₁→c₂ ∧ c₂→c₃ ⟹ c₁→c₃）；
  4. relu 是 1-Lipschitz（惩罚的光滑性，损失扰动界）；
  5. 批量零化：Σ 蕴含惩罚 = 0 ⟺ 每个蕴含成立（relu 非负 + 和零）。

对比 RealImplication.implication_penalty（out₁=0 时才惩罚 relu(out₂²)，
非可微指示）：margin 版对全部输入可微（relu），前提违背时自动不罚。

模型无关：纯 ℝ 代数，任意输出对 (out₁, out₂)。
-/

namespace Lattice

/-! ## 定理一：margin 蕴含惩罚为正
前提满足（out₁=0）∧ 结论违背（out₂>0）⟹ relu(out₂−out₁) > 0。-/

theorem margin_implication_penalty (out₁ out₂ : ℝ) (h₁ : out₁ = 0) (h₂ : 0 < out₂) :
    0 < relu (out₂ - out₁) := by
  have hpos : 0 < out₂ - out₁ := by
    rw [h₁]
    linarith
  have hrelu : relu (out₂ - out₁) = out₂ - out₁ := by
    unfold relu
    exact max_eq_left (le_of_lt hpos)
  rw [hrelu]
  exact hpos

/-! ## 定理二：margin 蕴含零化
out₂ ≤ out₁ ⟹ relu(out₂−out₁) = 0（结论不超过前提 ⟹ 零惩罚）。-/

theorem margin_implication_satisfied (out₁ out₂ : ℝ) (h : out₂ ≤ out₁) :
    relu (out₂ - out₁) = 0 := by
  exact (relu_eq_zero_iff (out₂ - out₁)).mpr (by linarith)

/-! ## 定理三：蕴含传递性（惩罚层面）
relu(b−a) = 0 ∧ relu(c−b) = 0 ⟹ relu(c−a) = 0（c₁→c₂ ∧ c₂→c₃ ⟹ c₁→c₃）。-/

theorem implication_transitive (a b c : ℝ)
    (h₁ : relu (b - a) = 0) (h₂ : relu (c - b) = 0) :
    relu (c - a) = 0 := by
  have hba : b ≤ a := sub_nonpos.mp ((relu_eq_zero_iff (b - a)).mp h₁)
  have hcb : c ≤ b := sub_nonpos.mp ((relu_eq_zero_iff (c - b)).mp h₂)
  exact (relu_eq_zero_iff (c - a)).mpr (by linarith)

/-! ## 定理四：relu 是 1-Lipschitz
|relu x − relu y| ≤ |x − y|（惩罚的光滑性，损失扰动有界）。-/

theorem relu_lipschitz (x y : ℝ) : |relu x - relu y| ≤ |x - y| := by
  -- |max x 0 − max y 0| ≤ |x−y|：两方向三角
  -- mathlib 4.14 的 abs_sub_le_iff 是差形式：|a-b| ≤ c ↔ a-b ≤ c ∧ b-a ≤ c
  rw [abs_sub_le_iff]
  constructor
  · -- max x 0 - max y 0 ≤ |x−y|
    unfold relu
    have hx : x ≤ y + |x - y| := by linarith [le_abs_self (x - y)]
    have h0 : 0 ≤ |x - y| := abs_nonneg (x - y)
    have hle : max x 0 ≤ max y 0 + |x - y| := by
      exact max_le (le_trans hx (add_le_add_right (le_max_left y 0) _))
        (le_trans (le_max_right y 0) (le_add_of_nonneg_right h0))
    linarith
  · -- max y 0 - max x 0 ≤ |x−y|
    unfold relu
    have hy : y ≤ x + |x - y| := by linarith [le_abs_self (y - x), abs_sub_comm x y]
    have h0 : 0 ≤ |x - y| := abs_nonneg (x - y)
    have hle : max y 0 ≤ max x 0 + |x - y| := by
      exact max_le (le_trans hy (add_le_add_right (le_max_left x 0) _))
        (le_trans (le_max_right x 0) (le_add_of_nonneg_right h0))
    linarith

/-! ## 定理五：批量蕴含总惩罚零化
Σ relu(outᵢ₂ − outᵢ₁) = 0 ⟺ 每个蕴含成立（relu 非负 → 和零 ⟺ 各项零）。-/

theorem implication_sum_zero_iff (ps : List (ℝ × ℝ)) :
    (ps.map (fun p => relu (p.2 - p.1))).foldr (fun a b => a + b) 0 = 0 ↔
      ∀ p ∈ ps, relu (p.2 - p.1) = 0 := by
  -- 转换到 SumRelu（p.1 − p.2 顺序）通过映射 (p.2, p.1)
  have hmap : ps.map (fun p => relu (p.2 - p.1)) =
      (ps.map (fun p => (p.2, p.1))).map (fun q => relu (q.1 - q.2)) := by
    simpa [List.map_map]
  have hswap : (ps.map (fun p => relu (p.2 - p.1))).foldr (fun a b => a + b) 0
      = SumRelu (ps.map (fun p => (p.2, p.1))) := by
    unfold SumRelu
    rw [hmap]
  rw [hswap]
  -- SumRelu 零化 ⟺ 每项 ReluOut = 0（sumRelu_eq_zero_iff_each）
  rw [sumRelu_eq_zero_iff_each]
  constructor
  · intro h p hp
    -- p ∈ ps ⟹ (p.2, p.1) ∈ map ⟹ relu (p.2 − p.1) = 0
    simpa using h (p.2, p.1) (List.mem_map.2 ⟨p, hp, rfl⟩)
  · intro h q hq
    -- q ∈ map ⟹ ∃ p ∈ ps, q = (p.2, p.1) ⟹ relu (q.1 − q.2) = 0
    rcases (List.mem_map.mp hq) with ⟨p, hp, rfl⟩
    simpa using h p hp

/-! ## 注：蕴含损失族闭环
  margin 惩罚（relu(out₂−out₁)）是蕴含 c₁→c₂ 的可微损失：
  惩罚为正（定理一）/零化（定理二）/传递（定理三）/光滑（定理四）/
  批量判定（定理五）——「蕴含族可微损失」完整；与对齐蕴含
  （RealImplication，权重对齐时零惩罚）衔接：对齐时 out₂ = k·out₁，
  若 k ≤ 1 则 out₂ ≤ out₁ 恒成立 ⟹ 零惩罚（margin 自动满足）。-/

end Lattice
