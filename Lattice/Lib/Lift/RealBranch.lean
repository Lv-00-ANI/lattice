import Mathlib
import Lattice.Lib.Architectures.RealActClass
/-!
# LATTICE: 控制流分支 —— 约束程序的 if-then-else 门控路由

早期批评「SymbolToWeightCorrectness 是约束集合而非程序（无控制流）」：
本文件补控制流的最小维度——**分支路由**：

  1. 门控选择：BranchSel(cond, t, e) = if 0 < cond then t else e
     （条件决定走哪支，确定性路由）；
  2. 路由确定性：cond > 0 ⟹ 取 t；cond ≤ 0 ⟹ 取 e；
  3. 分支的约束语义：分支输出满足约束 ⟺ 在对应条件下；
  4. 与 ReLU 门控衔接：if 0 < cond 与 reluSoftMask（掩码）同一门控条件。

模型无关：任意条件、任意分支值（范数空间）。
-/


noncomputable section

open Lattice.Lib.Architectures.RealActClass

namespace Lattice

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 门控选择（if-then-else 路由） -/

def BranchSel (cond : ℝ) (then_ else_ : F) : F :=
  if 0 < cond then then_ else else_

/-! ## 定理一：正向路由
cond > 0 ⟹ 取 then 分支（确定性）。-/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem branch_then_when_positive (cond : ℝ) (t e : F) (h : 0 < cond) :
    BranchSel cond t e = t := by
  unfold BranchSel
  exact if_pos h

/-! ## 定理二：反向路由
cond ≤ 0 ⟹ 取 else 分支。-/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem branch_else_when_nonpos (cond : ℝ) (t e : F) (h : cond ≤ 0) :
    BranchSel cond t e = e := by
  unfold BranchSel
  exact if_neg (not_lt.mpr h)

/-! ## 定理三：分支输出的约束满足（条件路由语义）
分支输出 = then 分支且 then 满足约束 ⟹ 在 cond > 0 下输出满足约束。-/

theorem branch_constraint_when_then (cond : ℝ) (t e : F) (W : F →L[ℝ] ℝ) (b : ℝ)
    (hcond : 0 < cond) (ht : W t + b = 0) :
    W (BranchSel cond t e) + b = 0 := by
  -- cond > 0 → 输出 = t → 约束满足
  rw [branch_then_when_positive cond t e hcond]
  exact ht

/-! ## 定理四：与 ReLU 门控衔接
分支条件（0 < cond）与 relu 掩码（reluSoftMask = if 0 < x then 1 else 0）
同一门控：cond > 0 ⟺ reluSoftMask cond = 1（硬路由激活）。-/

theorem branch_condition_equals_relu_mask (cond : ℝ) :
    (0 < cond ↔ reluSoftMask cond = 1) ∧ (cond ≤ 0 ↔ reluSoftMask cond = 0) := by
  constructor
  · constructor
    · intro h
      unfold reluSoftMask
      exact if_pos h
    · intro h
      unfold reluSoftMask at h
      by_cases hc : 0 < cond
      · exact hc
      · rw [if_neg hc] at h
        norm_num at h
  · constructor
    · intro h
      unfold reluSoftMask
      exact if_neg (not_lt.mpr h)
    · intro h
      unfold reluSoftMask at h
      by_cases hc : 0 < cond
      · rw [if_pos hc] at h
        norm_num at h
      · exact le_of_not_gt hc

/-! ## 定理五：分支输出范数界（任一分支有界）
then/else 分支都 ≤ M ⟹ 分支输出 ≤ M（路由不引入新范数）。-/

omit [NormedSpace ℝ F] in
theorem branch_output_bound (cond : ℝ) (t e : F) (M : ℝ)
    (ht : ‖t‖ ≤ M) (he : ‖e‖ ≤ M) :
    ‖BranchSel cond t e‖ ≤ M := by
  unfold BranchSel
  by_cases h : 0 < cond
  · rw [if_pos h]
    exact ht
  · rw [if_neg h]
    exact he

end Lattice
