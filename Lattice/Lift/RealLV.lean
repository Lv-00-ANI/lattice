import Lattice.Runtime.RealLinear
import Lattice.Lift.RealNonlinear
import Lattice.Lift.RealTotalLoss
import Mathlib

/-!
# LATTICE: Lv-00 接口执行版 —— 证明即程序（实现线以 Lean 本体落地）

doc/03 契约（C11 接口草案）的 **Lean 执行版**：用户观察成立——Lean 是证明即程序的语言（Curry-Howard）：

   · **def = 可执行实现**（接口函数即程序）；
   · **theorem = 契约不变量**（接口实现的正确性由定理保证，违反不变量即违反定理 = bug）；
   · **证明与程序无鸿沟**：同一语言里 def 是程序、theorem 是其性质——实现线的"执行版"
     以 Lean 本体落地，无需另写 C（外部独立实现可由 Lean def 直接翻译，语义已由定理钉死）。

契约接口（doc/03 §3）落地为 Lean def + 不变量定理：
   · `lv_neuron_out` / `lv_compile`：编译保语义（convertReal_preserves）；
   · `lv_loss`：平方损失零化 ⟺ 满足（realLoss_soundness）；
   · `lv_verify`：Bool 判定 = 损失零化（decide）；
   · `lv_relu`：relu=0 ⟹ x≤0（单向；本文件未以双向形式暴露该结论，双重蕴含见 relu_eq_zero_iff）。

注（mathlib 4.14 适配）：ℝ 的 `≤`/`=` 判定（Real.decidableLE / Real.decidableEq）为
noncomputable instance，故 `max`/`decide` 无法在 `#eval` 中执行——原文件的 `#eval`
演示行已移除（`lv_verify` 标注 noncomputable，定理证明不受影响）。
-/

namespace Lattice

/-! ## 接口：编译（约束 → 神经元，系数拷贝） -/

def lv_compile (c : RealConstraint) : RealNeuron :=
  convertReal c

/-! ## 接口：神经元输出 -/

def lv_neuron_out (n : RealNeuron) (x : ℝ) : ℝ :=
  RealNeuronOut n x

/-! ## 不变量：编译保语义（零化 ⟺ 满足）
lv_compile 后的神经元输出为零 ⟺ 原约束满足（convertReal_preserves）。-/

theorem lv_compile_invariant (c : RealConstraint) (x : ℝ) :
    lv_neuron_out (lv_compile c) x = 0 → RealConstraintSat c x := by
  unfold lv_neuron_out lv_compile
  exact (convertReal_preserves c x).mpr

/-! ## 接口：平方损失（约束嵌入） -/

def lv_loss (c : RealConstraint) (x : ℝ) : ℝ :=
  realLoss c x

/-! ## 不变量：损失零化 ⟹ 满足（realLoss_soundness）
损失 = 0 ⟹ 约束满足；不满足 ⟹ 损失 > 0（严格正）。-/

theorem lv_loss_invariant (c : RealConstraint) (x : ℝ) :
    lv_loss c x = 0 → RealConstraintSat c x := by
  unfold lv_loss
  exact (realLoss_soundness c x).mp

theorem lv_loss_pos_of_unsatisfied (c : RealConstraint) (x : ℝ) (h : ¬ RealConstraintSat c x) :
    0 < lv_loss c x := by
  unfold lv_loss
  -- 不满足 ⟹ 损失 ≠ 0；损失 = out² ≥ 0；非负非零 ⟹ 严格正
  have hne : realLoss c x ≠ 0 := by
    intro hz
    exact h ((realLoss_soundness c x).mp hz)
  have hnonneg : 0 ≤ realLoss c x := by
    unfold realLoss
    exact sq_nonneg _
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-! ## 接口：验证判定（Bool） -/

-- 注：ℝ 的相等判定（Real.decidableEq）在 mathlib 4.14 中为 noncomputable instance，
-- 故 lv_verify 必须标注 noncomputable（decide 无法在 #eval 中执行，但类型与定理均成立）。
noncomputable def lv_verify (c : RealConstraint) (x : ℝ) : Bool :=
  decide (lv_loss c x = 0)

/-! ## 不变量：验证通过 ⟹ 约束满足
lv_verify = true ⟹ 约束满足（decide + realLoss_soundness）。-/

theorem lv_verify_invariant (c : RealConstraint) (x : ℝ) :
    lv_verify c x = true → RealConstraintSat c x := by
  intro h
  have hz : lv_loss c x = 0 := by
    unfold lv_verify at h
    exact (decide_eq_true_iff.mp h)
  exact lv_loss_invariant c x hz

/-! ## 接口：ReLU 编码 -/

def lv_relu (x : ℝ) : ℝ :=
  relu x

/-! ## 不变量：relu 零化 ⟹ x ≤ 0（单向：`lv_relu_invariant` 仅证 relu=0 → x≤0；
双向形式见 relu_eq_zero_iff，本文件未以双向形式暴露） -/

theorem lv_relu_invariant (x : ℝ) :
    lv_relu x = 0 → x ≤ 0 := by
  unfold lv_relu
  exact (relu_eq_zero_iff x).mp

theorem lv_relu_nonneg (x : ℝ) : 0 ≤ lv_relu x := by
  unfold lv_relu
  exact relu_nonneg x

end Lattice
