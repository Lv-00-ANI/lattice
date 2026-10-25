import Mathlib

/-!
# LATTICE: 编辑容差判定（矩阵扰动 → Verdict 公共骨架）

权重编辑调研（research/real-world/model-edit-math.md 目标 2）：
ROME/MEMIT/LoRA 的编辑保语义统一归约到同一链条——

  权重扰动 ‖W'−W‖ ≤ ε₁、偏置扰动 |b'−b| ≤ ε₂、输入有界 ‖x‖ ≤ X、
  原约束满足（W·x + b = 0）
  ⟹ 编辑后输出有界 |W'·x + b'| ≤ ε₁X + ε₂
  ⟹ 编辑后平方损失 (W'·x + b')² ≤ (ε₁X + ε₂)²
  ⟹ 验证器容差 τ ≥ ε₁X + ε₂ 时 Verdict = pass（编辑保语义）。

这是三种编辑方法共享的矩阵版 ε 链（各方法的 Δ 公式只在 ε₁ 的具体值上不同）。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 引理一：仿射（带偏置）编辑的输出变化界
|(W'x + b') - (Wx + b)| ≤ ‖W'−W‖·‖x‖ + |b'−b|。-/

lemma affine_edit_output_bound (W W' : E →L[ℝ] ℝ) (b b' : ℝ) (x : E) :
    |(W' x + b') - (W x + b)| ≤ ‖W' - W‖ * ‖x‖ + |b' - b| := by
  -- 拆解：差值 = (W'x - Wx) + (b' - b)
  have hdiff : (W' x + b') - (W x + b) = (W' x - W x) + (b' - b) := by ring
  calc
    |(W' x + b') - (W x + b)| = |(W' x - W x) + (b' - b)| := by rw [hdiff]
    _ ≤ |W' x - W x| + |b' - b| := abs_add _ _
    _ ≤ ‖W' - W‖ * ‖x‖ + |b' - b| := by
      -- ‖W'x - Wx‖ = ‖(W'-W)x‖ ≤ ‖W'-W‖·‖x‖（算子范数）
      have hle : ‖W' x - W x‖ ≤ ‖W' - W‖ * ‖x‖ := by
        have hdiff : W' x - W x = (W' - W) x := by
          simp [ContinuousLinearMap.sub_apply]
        rw [hdiff]
        exact (W' - W).le_opNorm x
      -- |W'x - Wx| = ‖W'x - Wx‖（ℝ 范数 = 绝对值）
      have hnorm : |W' x - W x| = ‖W' x - W x‖ := by
        rw [Real.norm_eq_abs]
      rw [hnorm]
      exact add_le_add_right hle |b' - b|

/-! ## 引理二：原约束满足 ⟹ 编辑后输出被界住
W·x + b = 0 ⟹ |W'·x + b'| ≤ ‖W'−W‖·‖x‖ + |b'−b|。-/

lemma edit_preserves_affine_constraint (W W' : E →L[ℝ] ℝ) (b b' : ℝ) (x : E)
    (h : W x + b = 0) :
    |W' x + b'| ≤ ‖W' - W‖ * ‖x‖ + |b' - b| := by
  calc
    |W' x + b'| = |(W' x + b') - (W x + b)| := by
      simpa [h]
    _ ≤ ‖W' - W‖ * ‖x‖ + |b' - b| := affine_edit_output_bound W W' b b' x

/-! ## 定理：编辑容差判定（Verdict 公共骨架）
扰动有界（ε₁/ε₂）、输入有界（X）、原约束满足
⟹ 编辑后平方损失 ≤ (ε₁X + ε₂)²（验证器 τ ≥ ε₁X+ε₂ 时 pass）。-/

theorem edit_tolerance_verdict (W W' : E →L[ℝ] ℝ) (b b' : ℝ) (x : E) (ε₁ ε₂ X : ℝ)
    (h : W x + b = 0) (hε₁ : ‖W' - W‖ ≤ ε₁) (hε₂ : |b' - b| ≤ ε₂) (hx : ‖x‖ ≤ X) :
    (W' x + b') ^ 2 ≤ (ε₁ * X + ε₂) ^ 2 := by
  -- |W'x+b'| ≤ ‖Δ‖‖x‖ + |Δb| ≤ ε₁X + ε₂
  have hb : |W' x + b'| ≤ ε₁ * X + ε₂ := by
    calc
      |W' x + b'| ≤ ‖W' - W‖ * ‖x‖ + |b' - b| := edit_preserves_affine_constraint W W' b b' x h
      _ ≤ ε₁ * ‖x‖ + ε₂ := by
        exact add_le_add (mul_le_mul_of_nonneg_right hε₁ (norm_nonneg x)) hε₂
      _ ≤ ε₁ * X + ε₂ := by
        have hε₁₀ : 0 ≤ ε₁ := le_trans (norm_nonneg (W' - W)) hε₁
        exact add_le_add_right (mul_le_mul_of_nonneg_left hx hε₁₀) ε₂
  -- 平方单调（非负）：|a| ≤ |b| ⟹ a² ≤ b²（b = ε₁X+ε₂ ≥ 0）
  have hb0 : 0 ≤ ε₁ * X + ε₂ := le_trans (abs_nonneg (W' x + b')) hb
  exact sq_le_sq.mpr (by simpa [abs_of_nonneg hb0] using hb)

/-! ## 推论：容差阈值的 Verdict 判定
若验证器容差 τ ≥ ε₁X + ε₂，则编辑后约束被接受（损失 ≤ τ² 即 pass 条件）。-/

theorem edit_verdict_pass (W W' : E →L[ℝ] ℝ) (b b' : ℝ) (x : E) (ε₁ ε₂ X τ : ℝ)
    (h : W x + b = 0) (hε₁ : ‖W' - W‖ ≤ ε₁) (hε₂ : |b' - b| ≤ ε₂) (hx : ‖x‖ ≤ X)
    (hτ : (ε₁ * X + ε₂) ^ 2 ≤ τ) :
    (W' x + b') ^ 2 ≤ τ := by
  exact le_trans (edit_tolerance_verdict W W' b b' x ε₁ ε₂ X h hε₁ hε₂ hx) hτ

/-! ## 推论：编辑零变化 ⟹ 约束精确保持（容差退化）
无编辑（W' = W、b' = b）时约束精确保持（τ = 0 亦可 pass）。-/

theorem edit_identity_affine_preserves (W W' : E →L[ℝ] ℝ) (b b' : ℝ) (x : E)
    (h : W x + b = 0) (hW : W' = W) (hb' : b' = b) :
    W' x + b' = 0 := by
  rw [hW, hb']
  exact h

end Lattice
