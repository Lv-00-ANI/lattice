import Mathlib
import Lattice.Lib.Chain.RealScalarField
/-!
# LATTICE: Verdict 核心标量域参数化（审计建议 ① 收尾）

编辑核心（RealScalarField）与残差核心（RealScalarResidual）已参数化；
Verdict 判定（仿射编辑 → 容差）同构——只用三角不等式与算子范数：

  1. 仿射编辑输出变化界：‖(W'x+b') − (Wx+b)‖ ≤ ‖W'−W‖·‖x‖ + ‖b'−b‖（𝕜）；
  2. 原约束满足 ⟹ 编辑后 ‖W'x+b'‖ ≤ ε₁X + ε₂（扰动/输入有界时）。

ℝ 版（RealEditVerdict）是其实例；ℂ/p-adic 域同成立。
至此审计建议 ①（标量域参数化）的编辑/残差/Verdict 核心组全部落地。
-/


noncomputable section

namespace Lattice

variable {𝕜 E : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ## 定理一：仿射（带偏置）编辑的输出变化界（任意域）
‖(W'x+b') − (Wx+b)‖ ≤ ‖W'−W‖·‖x‖ + ‖b'−b‖。-/

theorem affine_edit_output_bound_scalar (W W' : E →L[𝕜] 𝕜) (b b' : 𝕜) (x : E) :
    ‖(W' x + b') - (W x + b)‖ ≤ ‖W' - W‖ * ‖x‖ + ‖b' - b‖ := by
  -- 差值 = (W'x−Wx) + (b'−b)
  have hdiff : (W' x + b') - (W x + b) = (W' x - W x) + (b' - b) := by abel
  calc
    ‖(W' x + b') - (W x + b)‖ = ‖(W' x - W x) + (b' - b)‖ := by rw [hdiff]
    _ ≤ ‖W' x - W x‖ + ‖b' - b‖ := norm_add_le _ _
    _ ≤ ‖W' - W‖ * ‖x‖ + ‖b' - b‖ := by
      exact add_le_add_right (edit_output_bound_scalar W W' x) ‖b' - b‖

/-! ## 定理二：编辑容差判定（𝕜 版）
扰动有界（ε₁/ε₂）、输入有界（X）、原约束满足 ⟹ ‖W'x+b'‖ ≤ ε₁X+ε₂。 -/

theorem edit_verify_tolerance_scalar_affine (W W' : E →L[𝕜] 𝕜) (b b' : 𝕜) (x : E)
    (ε₁ ε₂ X : ℝ) (h : W x + b = 0) (hε₁ : ‖W' - W‖ ≤ ε₁) (hε₂ : ‖b' - b‖ ≤ ε₂)
    (hx : ‖x‖ ≤ X) :
    ‖W' x + b'‖ ≤ ε₁ * X + ε₂ := by
  calc
    ‖W' x + b'‖ = ‖W' x + b' - (W x + b)‖ := by
      rw [h]
      simp
    _ ≤ ‖W' - W‖ * ‖x‖ + ‖b' - b‖ := affine_edit_output_bound_scalar W W' b b' x
    _ ≤ ε₁ * ‖x‖ + ε₂ := by
      exact add_le_add (mul_le_mul_of_nonneg_right hε₁ (norm_nonneg x)) hε₂
    _ ≤ ε₁ * X + ε₂ := by
      have hε₁nonneg : 0 ≤ ε₁ := le_trans (norm_nonneg (W' - W)) hε₁
      exact add_le_add_right (mul_le_mul_of_nonneg_left hx hε₁nonneg) ε₂

/-! ## 注：审计建议 ① 完成度
编辑核心（edit_output_bound/preserves/tolerance）✅ RealScalarField
残差核心（error_isolation/edit_local/constraint）✅ RealScalarResidual
Verdict 核心（affine_bound/verify_tolerance）✅ 本文件
法方程/内积相关（内积涉及 𝕜-共轭）留待内积空间参数化专项。 -/

end Lattice
