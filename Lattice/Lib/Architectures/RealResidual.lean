import Mathlib
import Lattice.Lib.Editing.RealEditBound
/-!
# LATTICE: 残差误差隔离与编辑局部性

transformer 调研（research/real-world/transformer-semantics.md 目标 A）：
真实 transformer 的残差连接（Residual F x = x + F x）的关键性质——

  1. 误差隔离：‖(x + Fx) − (x + Gx)‖ = ‖Fx − Gx‖
     （恒等路径 x 抵消，误差只由残差支路贡献）；
  2. 编辑局部性：残差支路编辑 F → F' 后，整层输出变化 ≤ ‖F'−F‖·‖x‖
     （由算子范数界控制，非等号；模型编辑可验证性的代数根源：局部修改影响恰为 ΔF，
     等号形式仅对第 1 条的元素级隔离成立）；
  3. 编辑后约束保持：约束在残差层输出上满足 ⟹ 编辑后 |W(R')+b| ≤ ‖W‖·‖ΔF‖·‖x‖。

难度：易（恒等路径抵消 = 纯代数）。
-/


noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 残差层 -/

def Residual (F : E →L[ℝ] E) (x : E) : E := x + F x

/-! ## 定理一：残差误差隔离
恒等路径抵消：‖(x+Fx) − (x+Gx)‖ = ‖Fx − Gx‖（误差只来自支路）。-/

omit [NormedSpace ℝ E] in
theorem residual_error_isolation (x Fx Gx : E) :
    ‖(x + Fx) - (x + Gx)‖ = ‖Fx - Gx‖ := by
  have h : (x + Fx) - (x + Gx) = Fx - Gx := by
    abel
  rw [h]

/-! ## 定理二：残差编辑局部性
支路编辑 F→F' 后，整层输出变化 ≤ ‖F'−F‖·‖x‖（恰好 ΔF，无跨路径泄漏）。-/

theorem residual_edit_local (x : E) (F F' : E →L[ℝ] E) :
    ‖Residual F' x - Residual F x‖ ≤ ‖F' - F‖ * ‖x‖ := by
  unfold Residual
  -- (x + F'x) - (x + Fx) = F'x - Fx
  have h : (x + F' x) - (x + F x) = F' x - F x := by
    abel
  rw [h]
  exact edit_output_bound F F' x

/-! ## 定理三：残差编辑后的约束近似保持
约束在残差层输出上满足（W·(Residual F x) + b = 0）⟹
编辑支路后 |W·(Residual F' x) + b| ≤ ‖W‖·‖F'−F‖·‖x‖。-/

theorem residual_edit_constraint (W : E →L[ℝ] ℝ) (b : ℝ) (x : E) (F F' : E →L[ℝ] E)
    (h : W (Residual F x) + b = 0) :
    |W (Residual F' x) + b| ≤ ‖W‖ * (‖F' - F‖ * ‖x‖) := by
  -- |W(R')+b| = |W(R')+b - (W(R)+b)|（原约束 = 0）= |W(R'-R)|
  have hzero : |W (Residual F' x) + b| = |W (Residual F' x) + b - (W (Residual F x) + b)| := by
    rw [h]
    ring
  have hlin : W (Residual F' x) + b - (W (Residual F x) + b) = W (Residual F' x - Residual F x) := by
    -- W(R') - W(R) = W(R' - R)，b 抵消
    calc
      W (Residual F' x) + b - (W (Residual F x) + b) = W (Residual F' x) - W (Residual F x) := by ring
      _ = W (Residual F' x - Residual F x) := (W.map_sub (Residual F' x) (Residual F x)).symm
  calc
    |W (Residual F' x) + b| = |W (Residual F' x) + b - (W (Residual F x) + b)| := hzero
    _ = |W (Residual F' x - Residual F x)| := by rw [hlin]
    _ ≤ ‖W‖ * ‖Residual F' x - Residual F x‖ := W.le_opNorm _
    _ ≤ ‖W‖ * (‖F' - F‖ * ‖x‖) := by
      have hb : ‖Residual F' x - Residual F x‖ ≤ ‖F' - F‖ * ‖x‖ := residual_edit_local x F F'
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg W)

/-! ## 定理四：多层残差误差隔离（精确版）
两层残差（各含独立支路）的差：第一层差经 F₂ 放大（‖F₂‖+1）+ 第二层支路编辑。
恒等路径不泄漏（分解精确）。-/

theorem residual_two_layer_isolation_exact (x : E) (F₁ F₂ G₁ G₂ : E →L[ℝ] E) :
    ‖Residual F₂ (Residual F₁ x) - Residual G₂ (Residual G₁ x)‖ ≤
      (‖F₂‖ + 1) * ‖Residual F₁ x - Residual G₁ x‖ + ‖F₂ - G₂‖ * ‖Residual G₁ x‖ := by
  -- 中间分解：R_F₂(R_F₁ x) - R_F₂(R_G₁ x) + R_F₂(R_G₁ x) - R_G₂(R_G₁ x)
  calc
    ‖Residual F₂ (Residual F₁ x) - Residual G₂ (Residual G₁ x)‖
        ≤ ‖Residual F₂ (Residual F₁ x) - Residual F₂ (Residual G₁ x)‖
          + ‖Residual F₂ (Residual G₁ x) - Residual G₂ (Residual G₁ x)‖ := by
            have h : Residual F₂ (Residual F₁ x) - Residual G₂ (Residual G₁ x) =
                (Residual F₂ (Residual F₁ x) - Residual F₂ (Residual G₁ x))
                + (Residual F₂ (Residual G₁ x) - Residual G₂ (Residual G₁ x)) := by abel
            rw [h]
            exact norm_add_le _ _
    _ ≤ (‖F₂‖ + 1) * ‖Residual F₁ x - Residual G₁ x‖ + ‖F₂ - G₂‖ * ‖Residual G₁ x‖ := by
      -- 第一项：同支路 F₂，输入差 Δ₁ = R_F₁x - R_G₁x；残差输出差 = ‖F₂(Δ₁) + Δ₁‖ ≤ (‖F₂‖+1)‖Δ₁‖
      have h1 : ‖Residual F₂ (Residual F₁ x) - Residual F₂ (Residual G₁ x)‖ ≤
          (‖F₂‖ + 1) * ‖Residual F₁ x - Residual G₁ x‖ := by
        -- 残差 F₂ 的 Lipschitz：‖R_F₂(a) - R_F₂(b)‖ = ‖(a-F₂a... 展开
        calc
          ‖Residual F₂ (Residual F₁ x) - Residual F₂ (Residual G₁ x)‖
              = ‖(Residual F₁ x + F₂ (Residual F₁ x)) - (Residual G₁ x + F₂ (Residual G₁ x))‖ := rfl
          _ = ‖(Residual F₁ x - Residual G₁ x) + (F₂ (Residual F₁ x) - F₂ (Residual G₁ x))‖ := by
                have h : (Residual F₁ x + F₂ (Residual F₁ x)) - (Residual G₁ x + F₂ (Residual G₁ x)) =
                    (Residual F₁ x - Residual G₁ x) + (F₂ (Residual F₁ x) - F₂ (Residual G₁ x)) := by abel
                rw [h]
          _ ≤ ‖Residual F₁ x - Residual G₁ x‖ + ‖F₂ (Residual F₁ x) - F₂ (Residual G₁ x)‖ := norm_add_le _ _
          _ ≤ ‖Residual F₁ x - Residual G₁ x‖ + ‖F₂‖ * ‖Residual F₁ x - Residual G₁ x‖ := by
                have hF : ‖F₂ (Residual F₁ x) - F₂ (Residual G₁ x)‖ ≤ ‖F₂‖ * ‖Residual F₁ x - Residual G₁ x‖ := by
                  -- F₂ 线性：F₂(a) - F₂(b) = F₂(a-b)；opNorm
                  have : F₂ (Residual F₁ x) - F₂ (Residual G₁ x) = F₂ (Residual F₁ x - Residual G₁ x) := (F₂.map_sub _ _).symm
                  rw [this]
                  exact F₂.le_opNorm _
                nlinarith [hF]
          _ = (‖F₂‖ + 1) * ‖Residual F₁ x - Residual G₁ x‖ := by ring
      -- 第二项：支路编辑（residual_edit_local）
      have h2 : ‖Residual F₂ (Residual G₁ x) - Residual G₂ (Residual G₁ x)‖ ≤
          ‖F₂ - G₂‖ * ‖Residual G₁ x‖ := residual_edit_local (Residual G₁ x) G₂ F₂
      nlinarith [h1, h2]

end Lattice
