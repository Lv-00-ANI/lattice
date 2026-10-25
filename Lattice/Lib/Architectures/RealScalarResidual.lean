import Mathlib
import Lattice.Lib.Chain.RealScalarField
/-!
# LATTICE: 残差核心标量域参数化（审计建议 ① 推广）

编辑核心已在任意 NontriviallyNormedField 𝕜 上证明（RealScalarField）；
残差核心同构——只用 abel（加群）与算子范数，域无关：

  1. 误差隔离：‖(x+Fx) − (x+Gx)‖ = ‖Fx − Gx‖（𝕜）；
  2. 编辑局部性：‖Residual F' x − Residual F x‖ ≤ ‖F'−F‖·‖x‖（𝕜）；
  3. 约束保持：残差层约束编辑后近似保持（𝕜 值标量约束）。

ℝ 版（RealResidual）是其实例；ℂ/p-adic 域同成立。
-/


noncomputable section

namespace Lattice

variable {𝕜 E : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ## 残差（𝕜 版） -/

def ResidualS (F : E →L[𝕜] E) (x : E) : E := x + F x

/-! ## 定理一：残差误差隔离（任意域）
恒等路径抵消：‖(x+Fx) − (x+Gx)‖ = ‖Fx − Gx‖。-/

theorem residual_error_isolation_scalar (x Fx Gx : E) :
    ‖(x + Fx) - (x + Gx)‖ = ‖Fx - Gx‖ := by
  have h : (x + Fx) - (x + Gx) = Fx - Gx := by
    abel
  rw [h]

/-! ## 定理二：残差编辑局部性（任意域）
支路编辑 F→F' 后，整层输出变化 ≤ ‖F'−F‖·‖x‖。-/

theorem residual_edit_local_scalar (x : E) (F F' : E →L[𝕜] E) :
    ‖ResidualS F' x - ResidualS F x‖ ≤ ‖F' - F‖ * ‖x‖ := by
  unfold ResidualS
  have h : (x + F' x) - (x + F x) = F' x - F x := by
    abel
  rw [h]
  exact edit_output_bound_scalar F F' x

/-! ## 定理三：残差编辑后的约束近似保持（𝕜 值约束）
W·(Residual F x) + b = 0 ⟹ ‖W·(Residual F' x) + b‖ ≤ ‖W‖·‖F'−F‖·‖x‖。-/

theorem residual_edit_constraint_scalar (W : E →L[𝕜] 𝕜) (b : 𝕜) (x : E) (F F' : E →L[𝕜] E)
    (h : W (ResidualS F x) + b = 0) :
    ‖W (ResidualS F' x) + b‖ ≤ ‖W‖ * (‖F' - F‖ * ‖x‖) := by
  -- ‖W(R')+b‖ = ‖W(R')+b − (W(R)+b)‖（原约束 = 0）= ‖W(R'−R)‖
  have hzero : ‖W (ResidualS F' x) + b‖ = ‖W (ResidualS F' x) + b - (W (ResidualS F x) + b)‖ := by
    rw [h]
    -- W(R')+b - 0 = W(R')+b
    simp
  have hlin : W (ResidualS F' x) + b - (W (ResidualS F x) + b) = W (ResidualS F' x - ResidualS F x) := by
    calc
      W (ResidualS F' x) + b - (W (ResidualS F x) + b) = W (ResidualS F' x) - W (ResidualS F x) := by
        abel
      _ = W (ResidualS F' x - ResidualS F x) := (W.map_sub (ResidualS F' x) (ResidualS F x)).symm
  calc
    ‖W (ResidualS F' x) + b‖ = ‖W (ResidualS F' x) + b - (W (ResidualS F x) + b)‖ := hzero
    _ = ‖W (ResidualS F' x - ResidualS F x)‖ := by rw [hlin]
    _ ≤ ‖W‖ * ‖ResidualS F' x - ResidualS F x‖ := W.le_opNorm _
    _ ≤ ‖W‖ * (‖F' - F‖ * ‖x‖) := by
      have hb : ‖ResidualS F' x - ResidualS F x‖ ≤ ‖F' - F‖ * ‖x‖ := residual_edit_local_scalar x F F'
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg W)

end Lattice
