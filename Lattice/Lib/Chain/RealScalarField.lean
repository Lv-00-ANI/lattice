import Mathlib

/-!
# LATTICE: 标量域参数化 —— 编辑核心在任意域成立（审计建议 ①）

审计建议（research/audit/GENERALITY-AUDIT.md 建议 1）：
编辑/验证核心组的 `NormedSpace ℝ` 泛化为任意 `NontriviallyNormedField 𝕜`——
关键观察：这些证明只用 `le_opNorm`、三角不等式、减法，
**不依赖 ℝ 特有性质**（无 |·| 绝对值、无 ℝ 序的特殊用法），
故在任意标量域 𝕜 上逐字成立。

本文件给出编辑核心三定理的 𝕜 版（ℝ 版是其实例）：
  1. edit_output_bound：‖W'x − Wx‖ ≤ ‖W'−W‖·‖x‖（任意域）；
  2. edit_preserves_constraint：标量约束编辑后近似保持；
  3. edit_verify_tolerance：容差判定。

同构可迁移：编辑序列（累积）、残差、法方程、Verdict 的核心组
（同只用 le_opNorm/三角）均可参数化；ℝ 版保留为实例。
-/

noncomputable section

namespace Lattice

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-! ## 定理一：编辑输出变化界（任意标量域 𝕜）
‖W'·x − W·x‖ ≤ ‖W'−W‖·‖x‖（算子范数 Lipschitz，域无关）。-/

theorem edit_output_bound_scalar (W W' : E →L[𝕜] F) (x : E) :
    ‖W' x - W x‖ ≤ ‖W' - W‖ * ‖x‖ := by
  have hdiff : W' x - W x = (W' - W) x := by
    simp [ContinuousLinearMap.sub_apply]
  rw [hdiff]
  exact (W' - W).le_opNorm x

/-! ## 定理二：编辑后标量约束近似保持（𝕜 值输出）
W·x = 0（原约束满足）⟹ ‖W'·x‖ ≤ ‖W'−W‖·‖x‖。-/

theorem edit_preserves_constraint_scalar (W W' : E →L[𝕜] 𝕜) (x : E)
    (h : W x = 0) :
    ‖W' x‖ ≤ ‖W' - W‖ * ‖x‖ := by
  calc
    ‖W' x‖ = ‖W' x - W x‖ := by
      rw [h]
      simp
    _ ≤ ‖W' - W‖ * ‖x‖ := edit_output_bound_scalar W W' x

/-! ## 定理三：容差判定（𝕜 版）
‖W'−W‖·‖x‖ ≤ ε ⟹ 编辑后约束 ε-近似保持（验证器接受）。-/

theorem edit_verify_tolerance_scalar (W W' : E →L[𝕜] 𝕜) (x : E) (ε : ℝ)
    (h : W x = 0) (hε : ‖W' - W‖ * ‖x‖ ≤ ε) :
    ‖W' x‖ ≤ ε := by
  exact le_trans (edit_preserves_constraint_scalar W W' x h) hε

/-! ## 注：实例化
取 𝕜 = ℝ 即回到既有 RealEditBound（ℝ 版是 𝕜 版的实例）；
取 𝕜 = ℂ、p-adic 域等同样成立——编辑保语义的核心是域无关的。 -/

end Lattice
