import Mathlib

/-!
# LATTICE: LoRA 低秩编辑界（编辑方法第三实例）

权重编辑调研（research/real-world/model-edit-math.md）的 LoRA：
W' = W + (α/r)·B·A（A 下投影到低秩空间 H，B 上投影回 F，α/r 缩放）——

  ‖Δ·x‖ = ‖(α/r)·B·A·x‖ ≤ |α/r|·‖B‖·‖A‖·‖x‖

（smul 范数 + 两次 opNorm：B∘A 的 Lipschitz）。

推论：LoRA 编辑后约束近似保持（标量约束情形的界见本文件
`lora_edit_constraint`：‖W‖·(|c|·‖B‖·‖A‖·‖x‖) + |c|·‖B‖·‖A‖·‖x‖，
即含 ‖W‖ 与 ‖x‖ 两个因子，而非 |c|·‖B‖·‖A‖）。
此处与 `edit_tolerance_verdict` 仅为文档级指涉（本文件只 import Mathlib，
未 import 也未引用该名）。编辑方法三实例（ROME 精确/MEMIT 加法/LoRA 低秩）
统一在 Lipschitz 框架下。

模型无关：任意范数空间、任意低秩中间空间 H。
-/

noncomputable section

namespace Lattice

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-! ## LoRA 编辑：W' = W + c·(B∘A) -/

def LoRAEdit (A : E →L[ℝ] H) (B : H →L[ℝ] F) (c : ℝ) : E →L[ℝ] F :=
  c • (B.comp A)

/-! ## 定理：LoRA 编辑输出变化界
‖c·(B∘A)·x‖ ≤ |c|·‖B‖·‖A‖·‖x‖。-/

theorem lora_edit_bound (A : E →L[ℝ] H) (B : H →L[ℝ] F) (c : ℝ) (x : E) :
    ‖LoRAEdit A B c x‖ ≤ |c| * ‖B‖ * ‖A‖ * ‖x‖ := by
  unfold LoRAEdit
  calc
    ‖(c • (B.comp A)) x‖ = |c| * ‖(B.comp A) x‖ := by
      rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
    _ = |c| * ‖B (A x)‖ := by
      rw [ContinuousLinearMap.comp_apply]
    _ ≤ |c| * (‖B‖ * ‖A x‖) := by
      exact mul_le_mul_of_nonneg_left (B.le_opNorm (A x)) (abs_nonneg c)
    _ ≤ |c| * (‖B‖ * (‖A‖ * ‖x‖)) := by
      have hA : ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA (norm_nonneg B)) (abs_nonneg c)
    _ = |c| * ‖B‖ * ‖A‖ * ‖x‖ := by ring

/-! ## 推论一：LoRA 编辑容差判定
|c|·‖B‖·‖A‖·‖x‖ ≤ ε ⟹ 编辑后输出 ≤ ε（验证器容差）。-/

theorem lora_edit_verdict (A : E →L[ℝ] H) (B : H →L[ℝ] F) (c : ℝ) (x : E) (ε : ℝ)
    (hε : |c| * ‖B‖ * ‖A‖ * ‖x‖ ≤ ε) :
    ‖LoRAEdit A B c x‖ ≤ ε := by
  exact le_trans (lora_edit_bound A B c x) hε

/-! ## 推论二：LoRA 编辑后约束近似保持（标量约束）
原约束满足（W·x + b = 0）⟹ 编辑后 |W'·x + b| ≤ ‖W‖·(|c|‖B‖‖A‖‖x‖)（经 edit 界 + W 放大）。-/

theorem lora_edit_constraint (W : E →L[ℝ] ℝ) (b : ℝ) (x : E)
    (A : E →L[ℝ] H) (B : H →L[ℝ] ℝ) (c : ℝ)
    (h0 : W x + b = 0) :
    |(W + LoRAEdit A B c) x + b| ≤ ‖W‖ * (|c| * ‖B‖ * ‖A‖ * ‖x‖) + |c| * ‖B‖ * ‖A‖ * ‖x‖ := by
  -- 编辑后输出 = Wx + b + (LoRAEdit x)；原约束 = 0
  calc
    |(W + LoRAEdit A B c) x + b| = |(W x + b) + LoRAEdit A B c x| := by
      -- (W + Δ)x + b = Wx + Δx + b
      have : (W + LoRAEdit A B c) x + b = (W x + b) + LoRAEdit A B c x := by
        simp [ContinuousLinearMap.add_apply]
        abel
      rw [this]
    _ ≤ |W x + b| + |LoRAEdit A B c x| := abs_add _ _
    _ = |LoRAEdit A B c x| := by
      rw [h0]
      norm_num
    _ ≤ |c| * ‖B‖ * ‖A‖ * ‖x‖ := lora_edit_bound A B c x
    _ ≤ ‖W‖ * (|c| * ‖B‖ * ‖A‖ * ‖x‖) + |c| * ‖B‖ * ‖A‖ * ‖x‖ := by
      -- 0 ≤ ‖W‖·(...)（非负）
      have hw : 0 ≤ ‖W‖ * (|c| * ‖B‖ * ‖A‖ * ‖x‖) := by
        positivity
      linarith

end Lattice
