import Mathlib

/-!
# LATTICE: 权重编辑的 Lipschitz 误差界 —— 编辑保语义的基础

证明线重定向（面向真实权重）的第一个定理：
真实模型权重 W 经编辑变为 W'（编辑 = 权重变化 Δ = W' - W，如 ROME/MEMIT/LoRA），
输出变化被算子范数界住：

  ‖W'·x - W·x‖ ≤ ‖W' - W‖ · ‖x‖   （Lipschitz，连续线性算子）

推论（约束保持判定）：
  原约束满足（W·x = 0）⟹ 编辑后输出被界住 ‖W'·x‖ ≤ ‖W' - W‖·‖x‖
  ⟹ 验证器容差判定：若 ‖W' - W‖·‖x‖ ≤ ε 则接受（约束近似保持）。

这是 ROME/MEMIT/低秩编辑保语义证明的公共基础（编辑方法的具体 Δ 形式待调研后补充）。
-/

noncomputable section

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 定理一：编辑输出变化界（Lipschitz）
‖W' x - W x‖ ≤ ‖W' - W‖ · ‖x‖（算子范数性质）。-/

theorem edit_output_bound (W W' : E →L[ℝ] F) (x : E) :
    ‖W' x - W x‖ ≤ ‖W' - W‖ * ‖x‖ := by
  -- W'x - Wx = (W'-W)x
  have hdiff : W' x - W x = (W' - W) x := by
    simp [ContinuousLinearMap.sub_apply]
  rw [hdiff]
  exact (W' - W).le_opNorm x

/-! ## 定理二：编辑后约束近似保持
原约束满足（W·x = 0）⟹ 编辑后输出有界 ‖W'·x‖ ≤ ‖W' - W‖·‖x‖。-/

theorem edit_preserves_constraint_approx (W W' : E →L[ℝ] ℝ) (x : E)
    (h : W x = 0) :
    ‖W' x‖ ≤ ‖W' - W‖ * ‖x‖ := by
  calc
    ‖W' x‖ = ‖W' x - W x‖ := by
      rw [h]
      simp
    _ ≤ ‖W' - W‖ * ‖x‖ := edit_output_bound W W' x

/-! ## 定理三：验证器容差判定
编辑后若 ‖W' - W‖·‖x‖ ≤ ε，则验证器接受（约束 ε-近似保持）。-/

theorem edit_verify_tolerance (W W' : E →L[ℝ] ℝ) (x : E) (ε : ℝ)
    (h : W x = 0) (hε : ‖W' - W‖ * ‖x‖ ≤ ε) :
    ‖W' x‖ ≤ ε := by
  exact le_trans (edit_preserves_constraint_approx W W' x h) hε

/-! ## 定理四：编辑零变化 ⟹ 约束精确保持
W' = W（无编辑）⟹ 原约束仍满足。-/

theorem edit_identity_preserves (W W' : E →L[ℝ] ℝ) (x : E)
    (h : W x = 0) (hW : W' = W) :
    W' x = 0 := by
  rw [hW]
  exact h

/-! ## 定理五：验证容差随编辑量收紧
编辑量小的编辑，其约束保持的**容差界**更紧。
（注：单调的是"界"而非实际输出——‖W₂x‖ 无下界保证；
编辑保语义的量化对象是验证容差（界），不是输出本身。）-/

theorem edit_tolerance_tighter (W W₁ W₂ : E →L[ℝ] ℝ) (x : E) (ε₂ : ℝ)
    (h : W x = 0) (h12 : ‖W₁ - W‖ * ‖x‖ ≤ ‖W₂ - W‖ * ‖x‖)
    (hε : ‖W₂ - W‖ * ‖x‖ ≤ ε₂) :
    ‖W₁ x‖ ≤ ε₂ := by
  calc
    ‖W₁ x‖ ≤ ‖W₁ - W‖ * ‖x‖ := edit_preserves_constraint_approx W W₁ x h
    _ ≤ ‖W₂ - W‖ * ‖x‖ := h12
    _ ≤ ε₂ := hε

end Lattice
